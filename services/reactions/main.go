package main

import (
	"context"
	"crypto/sha1" // stable hash required to match Remark42's custom-provider user ID
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"log"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/signal"
	"regexp"
	"strings"
	"sync"
	"syscall"
	"time"
)

var (
	orcidPattern    = regexp.MustCompile(`^[0-9]{4}-[0-9]{4}-[0-9]{4}-[0-9]{3}[0-9X]$`)
	remarkIDPattern = regexp.MustCompile(`^orcid_[0-9a-f]{40}$`)
	segmentPattern  = regexp.MustCompile(`^[A-Za-z0-9][A-Za-z0-9._-]*$`)
)

type config struct {
	address       string
	databasePath  string
	backupDir     string
	remarkUserURL string
	orcidInfoURL  string
	provider      string
	allowed       map[string]struct{}
}

type remarkUser struct {
	ID   string `json:"id"`
	Name string `json:"name"`
}

type response struct {
	pageResult
	ViewerVote    int       `json:"viewer_vote"`
	Authenticated bool      `json:"authenticated"`
	Eligible      bool      `json:"eligible"`
	Viewer        *identity `json:"viewer,omitempty"`
}

type publicIdentity struct {
	RemarkID  string  `json:"remark42_id"`
	ORCID     string  `json:"orcid_id"`
	Name      string  `json:"name"`
	Profile   string  `json:"profile_url"`
	AvatarURL *string `json:"avatar_url"`
}

type app struct {
	config config
	store  *store
	client *http.Client
	limits *rateLimits
}

func env(key, fallback string) string {
	if value := strings.TrimSpace(os.Getenv(key)); value != "" {
		return value
	}
	return fallback
}

func loadConfig() config {
	allowed := map[string]struct{}{}
	for _, origin := range strings.Split(env("ALLOWED_ORIGINS", "https://laxarchive.org,https://www.laxarchive.org,http://localhost:3000,http://127.0.0.1:3000"), ",") {
		if origin = strings.TrimSpace(origin); origin != "" {
			allowed[origin] = struct{}{}
		}
	}
	return config{
		address:       env("LISTEN_ADDR", ":8081"),
		databasePath:  env("DATABASE_PATH", "/var/lib/reactions/reactions.db"),
		backupDir:     env("BACKUP_DIR", "/var/lib/reactions/backups"),
		remarkUserURL: env("REMARK_USER_URL", "http://remark42:8080/api/v1/user?site=remark"),
		orcidInfoURL:  env("ORCID_USERINFO_URL", "https://orcid.org/oauth/userinfo"),
		provider:      env("AUTH_PROVIDER", "orcid"),
		allowed:       allowed,
	}
}

func main() {
	cfg := loadConfig()
	database, err := openStore(cfg.databasePath)
	if err != nil {
		log.Fatal(err)
	}
	defer database.close()
	application := &app{
		config: cfg,
		store:  database,
		client: &http.Client{Timeout: 8 * time.Second, CheckRedirect: func(_ *http.Request, _ []*http.Request) error { return http.ErrUseLastResponse }},
		limits: newRateLimits(),
	}

	mux := http.NewServeMux()
	mux.HandleFunc("GET /healthz", application.health)
	mux.HandleFunc("GET /internal/orcid/userinfo", application.orcidUserInfo)
	mux.HandleFunc("OPTIONS /reactions/v1/{rest...}", application.preflight)
	mux.HandleFunc("GET /reactions/v1/page", application.getPage)
	mux.HandleFunc("GET /reactions/v1/identity", application.getIdentity)
	mux.HandleFunc("GET /reactions/v1/identities", application.getIdentities)
	mux.HandleFunc("PUT /reactions/v1/vote", application.putVote)
	server := &http.Server{Addr: cfg.address, Handler: application.security(mux), ReadHeaderTimeout: 5 * time.Second, ReadTimeout: 10 * time.Second, WriteTimeout: 15 * time.Second, IdleTimeout: 60 * time.Second, MaxHeaderBytes: 16 << 10}

	ctx, stop := signal.NotifyContext(context.Background(), syscall.SIGINT, syscall.SIGTERM)
	defer stop()
	go application.backupLoop(ctx)
	go func() {
		<-ctx.Done()
		shutdown, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()
		_ = server.Shutdown(shutdown)
	}()
	log.Printf("reactions service listening on %s", cfg.address)
	if err = server.ListenAndServe(); err != nil && !errors.Is(err, http.ErrServerClosed) {
		log.Fatal(err)
	}
}

func writeJSON(w http.ResponseWriter, status int, value any) {
	w.Header().Set("Content-Type", "application/json; charset=utf-8")
	w.Header().Set("Cache-Control", "no-store")
	w.WriteHeader(status)
	_ = json.NewEncoder(w).Encode(value)
}

func writeError(w http.ResponseWriter, status int, message string) {
	writeJSON(w, status, map[string]string{"error": message})
}

func toPublicIdentity(value identity) publicIdentity {
	return publicIdentity{
		RemarkID:  value.RemarkID,
		ORCID:     value.ORCID,
		Name:      value.Name,
		Profile:   "https://orcid.org/" + value.ORCID,
		AvatarURL: nil,
	}
}

func (a *app) security(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("X-Content-Type-Options", "nosniff")
		w.Header().Set("Referrer-Policy", "strict-origin-when-cross-origin")
		w.Header().Set("Content-Security-Policy", "default-src 'none'; frame-ancestors 'none'")
		if strings.HasPrefix(r.URL.Path, "/reactions/") {
			origin := r.Header.Get("Origin")
			if origin != "" {
				if _, ok := a.config.allowed[origin]; !ok {
					writeError(w, http.StatusForbidden, "origin is not allowed")
					return
				}
				w.Header().Set("Access-Control-Allow-Origin", origin)
				w.Header().Set("Access-Control-Allow-Credentials", "true")
				w.Header().Add("Vary", "Origin")
			}
		}
		next.ServeHTTP(w, r)
	})
}

func (a *app) preflight(w http.ResponseWriter, r *http.Request) {
	if r.Header.Get("Origin") == "" {
		writeError(w, http.StatusBadRequest, "origin is required")
		return
	}
	w.Header().Set("Access-Control-Allow-Methods", "GET, PUT, OPTIONS")
	w.Header().Set("Access-Control-Allow-Headers", "Accept, Content-Type, X-Lax-CSRF")
	w.Header().Set("Access-Control-Max-Age", "600")
	w.WriteHeader(http.StatusNoContent)
}

func (a *app) health(w http.ResponseWriter, _ *http.Request) {
	writeJSON(w, http.StatusOK, map[string]string{"status": "ok"})
}

func canonicalPage(raw string) (string, error) {
	parsed, err := url.Parse(raw)
	if err != nil || parsed.Scheme != "https" || parsed.Host != "laxarchive.org" || parsed.User != nil || parsed.RawQuery != "" || parsed.Fragment != "" {
		return "", errors.New("page URL must be a canonical laxarchive.org URL")
	}
	if parsed.RawPath != "" || strings.Contains(parsed.Path, "//") {
		return "", errors.New("page URL is not canonical")
	}
	parts := strings.Split(strings.TrimPrefix(parsed.Path, "/"), "/")
	valid := false
	if len(parts) == 2 && parts[1] == "" && segmentPattern.MatchString(parts[0]) {
		valid = true
	}
	if len(parts) == 2 && segmentPattern.MatchString(parts[0]) && strings.HasSuffix(parts[1], ".html") && segmentPattern.MatchString(strings.TrimSuffix(parts[1], ".html")) {
		valid = true
	}
	if !valid {
		return "", errors.New("page URL is not a submission or concept")
	}
	return "https://laxarchive.org" + parsed.EscapedPath(), nil
}

func validORCID(value string) bool {
	if !orcidPattern.MatchString(value) {
		return false
	}
	digits := strings.ReplaceAll(value, "-", "")
	total := 0
	for _, char := range digits[:15] {
		total = (total + int(char-'0')) * 2
	}
	check := (12 - (total % 11)) % 11
	expected := byte('0' + check)
	if check == 10 {
		expected = 'X'
	}
	return digits[15] == expected
}

func (a *app) currentUser(r *http.Request) (*remarkUser, error) {
	if r.Header.Get("Cookie") == "" {
		return nil, nil
	}
	request, err := http.NewRequestWithContext(r.Context(), http.MethodGet, a.config.remarkUserURL, nil)
	if err != nil {
		return nil, err
	}
	request.Header.Set("Cookie", r.Header.Get("Cookie"))
	request.Header.Set("Accept", "application/json")
	if address := clientIP(r); address != "" {
		request.Header.Set("X-Forwarded-For", address)
		request.Header.Set("X-Real-IP", address)
	}
	result, err := a.client.Do(request)
	if err != nil {
		return nil, err
	}
	defer result.Body.Close()
	if result.StatusCode == http.StatusUnauthorized || result.StatusCode == http.StatusForbidden {
		return nil, nil
	}
	if result.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("Remark42 user endpoint returned %d", result.StatusCode)
	}
	var user remarkUser
	if err = json.NewDecoder(io.LimitReader(result.Body, 32<<10)).Decode(&user); err != nil {
		return nil, err
	}
	if user.ID == "" {
		return nil, errors.New("Remark42 returned an empty user ID")
	}
	return &user, nil
}

func (a *app) pageResponse(r *http.Request, pageURL string) (response, error) {
	result, err := a.store.page(pageURL)
	if err != nil {
		return response{}, err
	}
	answer := response{pageResult: result}
	user, err := a.currentUser(r)
	if err != nil || user == nil {
		return answer, err
	}
	answer.Authenticated = true
	person, found, err := a.store.identity(user.ID)
	if err != nil || !found || strings.TrimSpace(person.Name) == "" {
		return answer, err
	}
	answer.Eligible = true
	answer.Viewer = &person
	answer.ViewerVote, err = a.store.viewerVote(pageURL, user.ID)
	return answer, err
}

func (a *app) getPage(w http.ResponseWriter, r *http.Request) {
	if !a.limits.allow(clientIP(r), false) {
		w.Header().Set("Retry-After", "10")
		writeError(w, http.StatusTooManyRequests, "too many requests")
		return
	}
	pageURL, err := canonicalPage(r.URL.Query().Get("url"))
	if err != nil {
		writeError(w, http.StatusBadRequest, err.Error())
		return
	}
	answer, err := a.pageResponse(r, pageURL)
	if err != nil {
		log.Printf("page response failed: %v", err)
		writeError(w, http.StatusServiceUnavailable, "page responses are temporarily unavailable")
		return
	}
	writeJSON(w, http.StatusOK, answer)
}

func (a *app) getIdentity(w http.ResponseWriter, r *http.Request) {
	if !a.limits.allow(clientIP(r), false) {
		w.Header().Set("Retry-After", "10")
		writeError(w, http.StatusTooManyRequests, "too many requests")
		return
	}
	remarkID := r.URL.Query().Get("remark42_id")
	if !remarkIDPattern.MatchString(remarkID) {
		writeError(w, http.StatusBadRequest, "invalid Remark42 identity")
		return
	}
	person, found, err := a.store.identity(remarkID)
	if err != nil {
		writeError(w, http.StatusServiceUnavailable, "identity lookup is temporarily unavailable")
		return
	}
	if !found || strings.TrimSpace(person.Name) == "" {
		writeError(w, http.StatusNotFound, "public ORCID identity not found")
		return
	}
	w.Header().Set("Cache-Control", "public, max-age=300")
	writePublicJSON(w, http.StatusOK, toPublicIdentity(person))
}

func (a *app) getIdentities(w http.ResponseWriter, r *http.Request) {
	if !a.limits.allow(clientIP(r), false) {
		w.Header().Set("Retry-After", "10")
		writeError(w, http.StatusTooManyRequests, "too many requests")
		return
	}
	ids := r.URL.Query()["remark42_id"]
	if len(ids) == 0 || len(ids) > 50 {
		writeError(w, http.StatusBadRequest, "provide between 1 and 50 Remark42 identities")
		return
	}
	seen := map[string]struct{}{}
	unique := make([]string, 0, len(ids))
	for _, id := range ids {
		if !remarkIDPattern.MatchString(id) {
			writeError(w, http.StatusBadRequest, "invalid Remark42 identity")
			return
		}
		if _, exists := seen[id]; !exists {
			seen[id] = struct{}{}
			unique = append(unique, id)
		}
	}
	people, err := a.store.identities(unique)
	if err != nil {
		writeError(w, http.StatusServiceUnavailable, "identity lookup is temporarily unavailable")
		return
	}
	public := make([]publicIdentity, 0, len(people))
	for _, person := range people {
		public = append(public, toPublicIdentity(person))
	}
	w.Header().Set("Cache-Control", "public, max-age=300")
	writePublicJSON(w, http.StatusOK, map[string][]publicIdentity{"identities": public})
}

func writePublicJSON(w http.ResponseWriter, status int, value any) {
	w.Header().Set("Content-Type", "application/json; charset=utf-8")
	w.Header().Set("X-Content-Type-Options", "nosniff")
	w.WriteHeader(status)
	_ = json.NewEncoder(w).Encode(value)
}

func (a *app) putVote(w http.ResponseWriter, r *http.Request) {
	if !a.limits.allow(clientIP(r), true) {
		w.Header().Set("Retry-After", "10")
		writeError(w, http.StatusTooManyRequests, "too many requests")
		return
	}
	if r.Header.Get("Origin") == "" || r.Header.Get("X-Lax-CSRF") != "1" || !strings.HasPrefix(strings.ToLower(r.Header.Get("Content-Type")), "application/json") {
		writeError(w, http.StatusForbidden, "request failed CSRF validation")
		return
	}
	var input struct {
		URL  string `json:"url"`
		Vote int    `json:"vote"`
	}
	decoder := json.NewDecoder(http.MaxBytesReader(w, r.Body, 1024))
	decoder.DisallowUnknownFields()
	if err := decoder.Decode(&input); err != nil || (input.Vote != -1 && input.Vote != 0 && input.Vote != 1) {
		writeError(w, http.StatusBadRequest, "vote must be -1, 0, or 1")
		return
	}
	pageURL, err := canonicalPage(input.URL)
	if err != nil {
		writeError(w, http.StatusBadRequest, err.Error())
		return
	}
	user, err := a.currentUser(r)
	if err != nil {
		log.Printf("authentication check failed: %v", err)
		writeError(w, http.StatusServiceUnavailable, "authentication is temporarily unavailable")
		return
	}
	if user == nil {
		writeError(w, http.StatusUnauthorized, "Sign in with ORCID to vote.")
		return
	}
	person, found, err := a.store.identity(user.ID)
	if err != nil {
		writeError(w, http.StatusServiceUnavailable, "page responses are temporarily unavailable")
		return
	}
	if !found || strings.TrimSpace(person.Name) == "" {
		writeError(w, http.StatusForbidden, "A public name on your ORCID record is required. Make it public, then sign in again.")
		return
	}
	if err = a.store.setVote(pageURL, user.ID, input.Vote); err != nil {
		log.Printf("save vote failed: %v", err)
		writeError(w, http.StatusServiceUnavailable, "unable to save your response")
		return
	}
	answer, err := a.pageResponse(r, pageURL)
	if err != nil {
		writeError(w, http.StatusServiceUnavailable, "response saved, but totals could not be refreshed")
		return
	}
	writeJSON(w, http.StatusOK, answer)
}

func (a *app) orcidUserInfo(w http.ResponseWriter, r *http.Request) {
	authorization := r.Header.Get("Authorization")
	if !strings.HasPrefix(authorization, "Bearer ") || len(authorization) > 4096 {
		writeError(w, http.StatusUnauthorized, "valid bearer token required")
		return
	}
	request, err := http.NewRequestWithContext(r.Context(), http.MethodGet, a.config.orcidInfoURL, nil)
	if err != nil {
		writeError(w, http.StatusInternalServerError, "ORCID profile validation failed")
		return
	}
	request.Header.Set("Authorization", authorization)
	request.Header.Set("Accept", "application/json")
	result, err := a.client.Do(request)
	if err != nil {
		log.Printf("ORCID userinfo request failed: %v", err)
		writeError(w, http.StatusBadGateway, "ORCID profile validation failed")
		return
	}
	defer result.Body.Close()
	if result.StatusCode != http.StatusOK {
		writeError(w, http.StatusBadGateway, "ORCID profile validation failed")
		return
	}
	var claims map[string]any
	if err = json.NewDecoder(io.LimitReader(result.Body, 64<<10)).Decode(&claims); err != nil {
		writeError(w, http.StatusBadGateway, "ORCID returned an invalid profile")
		return
	}
	orcid, _ := claims["sub"].(string)
	name, _ := claims["name"].(string)
	name = strings.TrimSpace(name)
	if name == "" {
		given, _ := claims["given_name"].(string)
		family, _ := claims["family_name"].(string)
		name = strings.TrimSpace(strings.TrimSpace(given) + " " + strings.TrimSpace(family))
	}
	if !validORCID(orcid) {
		writeError(w, http.StatusForbidden, "ORCID did not provide a valid authenticated iD")
		return
	}
	if name == "" {
		writeError(w, http.StatusForbidden, "Make your name public on your ORCID record before signing in.")
		return
	}
	hash := sha1.Sum([]byte(orcid)) //nolint:gosec -- compatibility identifier, not a credential
	remarkID := a.config.provider + "_" + hex.EncodeToString(hash[:])
	if err = a.store.putIdentity(identity{RemarkID: remarkID, ORCID: orcid, Name: name, Updated: time.Now().UTC()}); err != nil {
		log.Printf("save ORCID identity failed: %v", err)
		writeError(w, http.StatusInternalServerError, "ORCID profile could not be saved")
		return
	}
	writeJSON(w, http.StatusOK, map[string]string{"sub": orcid, "name": name})
}

func (a *app) backupLoop(ctx context.Context) {
	if err := a.store.backup(a.config.backupDir, 14); err != nil {
		log.Printf("initial backup failed: %v", err)
	}
	ticker := time.NewTicker(24 * time.Hour)
	defer ticker.Stop()
	for {
		select {
		case <-ctx.Done():
			return
		case <-ticker.C:
			if err := a.store.backup(a.config.backupDir, 14); err != nil {
				log.Printf("scheduled backup failed: %v", err)
			}
		}
	}
}

type rateEntry struct {
	start time.Time
	count int
}

type rateLimits struct {
	mu      sync.Mutex
	entries map[string]rateEntry
}

func newRateLimits() *rateLimits { return &rateLimits{entries: map[string]rateEntry{}} }

func (r *rateLimits) allow(ip string, write bool) bool {
	r.mu.Lock()
	defer r.mu.Unlock()
	now := time.Now()
	key := ip + fmt.Sprintf("|%t", write)
	entry := r.entries[key]
	window, limit := time.Minute, 60
	if write {
		window, limit = time.Minute, 12
	}
	if entry.start.IsZero() || now.Sub(entry.start) >= window {
		entry = rateEntry{start: now}
	}
	entry.count++
	r.entries[key] = entry
	if len(r.entries) > 2048 {
		for candidate, value := range r.entries {
			if now.Sub(value.start) > 2*time.Minute {
				delete(r.entries, candidate)
			}
		}
	}
	return entry.count <= limit
}

func clientIP(r *http.Request) string {
	if value := net.ParseIP(strings.TrimSpace(r.Header.Get("X-Real-IP"))); value != nil {
		return value.String()
	}
	host, _, err := net.SplitHostPort(r.RemoteAddr)
	if err == nil {
		return host
	}
	return r.RemoteAddr
}
