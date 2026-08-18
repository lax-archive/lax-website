package main

import (
	"crypto/sha1"
	"encoding/hex"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

func testStore(t *testing.T) *store {
	t.Helper()
	result, err := openStore(filepath.Join(t.TempDir(), "reactions.db"))
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = result.close() })
	return result
}

func TestCanonicalPage(t *testing.T) {
	valid := []string{"https://laxarchive.org/Lax2/", "https://laxarchive.org/Lax2/Lax2.C.html"}
	for _, raw := range valid {
		if got, err := canonicalPage(raw); err != nil || got != raw {
			t.Fatalf("canonicalPage(%q) = %q, %v", raw, got, err)
		}
	}
	invalid := []string{"http://laxarchive.org/Lax2/", "https://evil.test/Lax2/", "https://laxarchive.org/Lax2", "https://laxarchive.org/Lax2/?x=1", "https://laxarchive.org/a/b/c.html"}
	for _, raw := range invalid {
		if _, err := canonicalPage(raw); err == nil {
			t.Fatalf("canonicalPage(%q) unexpectedly succeeded", raw)
		}
	}
}

func TestValidORCIDChecksum(t *testing.T) {
	if !validORCID("0000-0002-1825-0097") || !validORCID("0009-0002-0314-6147") {
		t.Fatal("known ORCID iDs were rejected")
	}
	if validORCID("0000-0002-1825-0098") || validORCID("0000-0002-1825-009X") {
		t.Fatal("invalid ORCID checksum was accepted")
	}
}

func TestLegacyORCIDIdentityMatchesRemark42Hash(t *testing.T) {
	const orcid = "0009-0002-0314-6147"
	const legacyRemarkID = "orcid_1cc007f7256c32ff3b8829e4f3d37f83422a18a6"
	if got := remarkIdentityID("orcid", orcid); got != legacyRemarkID {
		t.Fatalf("Remark42 identity mismatch: got %q, want %q", got, legacyRemarkID)
	}
}

func TestHiddenReactionURLIsDerivedFromCanonicalPage(t *testing.T) {
	for page, want := range map[string]string{
		"https://laxarchive.org/Lax2/":            "https://laxarchive.org/_reactions/Lax2/",
		"https://laxarchive.org/Lax2/Lax2.C.html": "https://laxarchive.org/_reactions/Lax2/Lax2.C.html",
	} {
		got, err := hiddenReactionURL(page)
		if err != nil || got != want {
			t.Fatalf("hiddenReactionURL(%q) = %q, %v; want %q", page, got, err, want)
		}
	}
	if _, err := hiddenReactionURL("https://evil.test/Lax2/"); err == nil {
		t.Fatal("non-canonical reaction page was accepted")
	}
}

func TestReactionAggregationUsesLatestValidNamedEvent(t *testing.T) {
	const pageURL = "https://laxarchive.org/Lax2/"
	ids := []string{"orcid_" + strings.Repeat("a", 40), "orcid_" + strings.Repeat("b", 40), "orcid_" + strings.Repeat("c", 40)}
	times := []time.Time{time.Unix(10, 0).UTC(), time.Unix(20, 0).UTC(), time.Unix(30, 0).UTC()}
	remark := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Query().Get("url") != "https://laxarchive.org/_reactions/Lax2/" || r.URL.Query().Get("site") != "remark" || r.URL.Query().Get("format") != "plain" {
			t.Errorf("unsafe find request: %s", r.URL.String())
		}
		comments := []remarkReactionComment{
			{ID: "1", Orig: reactionPrefix + reactionLike, Time: times[0]},
			{ID: "2", Orig: reactionPrefix + reactionDislike, Time: times[1]},
			{ID: "3", Orig: reactionPrefix + reactionRocket, Time: times[2]},
			{ID: "4", Orig: reactionPrefix + reactionClear, Time: times[2]},
			{ID: "5", Orig: "ordinary comment", Time: times[2]},
			{ID: "6", ParentID: "parent", Orig: reactionPrefix + reactionLike, Time: times[2]},
		}
		comments[0].User.ID, comments[1].User.ID = ids[0], ids[0]
		comments[2].User.ID, comments[3].User.ID = ids[1], ids[1]
		comments[4].User.ID, comments[5].User.ID = ids[2], ids[2]
		_ = json.NewEncoder(w).Encode(remarkFindResponse{Comments: comments})
	}))
	defer remark.Close()
	db := testStore(t)
	for index, id := range ids {
		orcid := []string{"0000-0002-1825-0097", "0009-0002-0314-6147", "0000-0001-5109-3700"}[index]
		if err := db.putIdentity(identity{RemarkID: id, ORCID: orcid, Name: "Researcher " + string(rune('A'+index))}); err != nil {
			t.Fatal(err)
		}
	}
	a := &app{config: config{remarkFindURL: remark.URL}, store: db, client: remark.Client()}
	result, err := a.reactionPage(t.Context(), pageURL)
	if err != nil {
		t.Fatal(err)
	}
	if result.Counts[reactionLike] != 0 || result.Counts[reactionDislike] != 1 || result.Counts[reactionRocket] != 0 {
		t.Fatalf("unexpected totals: %+v", result.Counts)
	}
	if result.viewerByRemarkID[ids[0]] != reactionDislike || result.viewerByRemarkID[ids[1]] != "" {
		t.Fatalf("latest event did not win: %+v", result.viewerByRemarkID)
	}
}

func TestAppendReactionConstructsReservedRemark42Comment(t *testing.T) {
	remark := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.Method != http.MethodPost || r.URL.Query().Get("site") != "remark" {
			t.Errorf("unexpected request: %s %s", r.Method, r.URL.String())
		}
		if r.Header.Get("Cookie") == "" || r.Header.Get("X-XSRF-TOKEN") != "xsrf-value" {
			t.Errorf("Remark42 session/XSRF was not forwarded")
		}
		var body struct {
			Text    string `json:"text"`
			Locator struct {
				Site string `json:"site"`
				URL  string `json:"url"`
			} `json:"locator"`
		}
		if err := json.NewDecoder(r.Body).Decode(&body); err != nil {
			t.Fatal(err)
		}
		if body.Text != reactionPrefix+reactionRocket || body.Locator.Site != "remark" || body.Locator.URL != "https://laxarchive.org/_reactions/Lax2/" {
			t.Errorf("unsafe reaction payload: %+v", body)
		}
		w.WriteHeader(http.StatusCreated)
	}))
	defer remark.Close()
	a := &app{config: config{remarkPostURL: remark.URL + "?site=remark"}, client: remark.Client()}
	request := httptest.NewRequest(http.MethodPut, "/reactions/v1/reaction", nil)
	request.AddCookie(&http.Cookie{Name: "JWT", Value: "session"})
	request.AddCookie(&http.Cookie{Name: "XSRF-TOKEN", Value: "xsrf-value"})
	if err := a.appendReaction(request, "https://laxarchive.org/Lax2/", reactionRocket); err != nil {
		t.Fatal(err)
	}
}

func TestStoreOneVotePerUserAndPublicNames(t *testing.T) {
	db := testStore(t)
	for _, person := range []identity{
		{RemarkID: "orcid_a", ORCID: "0000-0001-0000-0001", Name: "Zoë Researcher"},
		{RemarkID: "orcid_b", ORCID: "0000-0001-0000-0002", Name: "Ada Scholar"},
	} {
		if err := db.putIdentity(person); err != nil {
			t.Fatal(err)
		}
	}
	page := "https://laxarchive.org/Lax2/"
	if err := db.setVote(page, "orcid_a", 1); err != nil {
		t.Fatal(err)
	}
	if err := db.setVote(page, "orcid_a", -1); err != nil {
		t.Fatal(err)
	}
	if err := db.setVote(page, "orcid_b", 1); err != nil {
		t.Fatal(err)
	}
	result, err := db.page(page)
	if err != nil {
		t.Fatal(err)
	}
	if result.Likes != 1 || result.Dislikes != 1 {
		t.Fatalf("unexpected totals: %+v", result)
	}
	if result.Voters["likes"][0].Name != "Ada Scholar" || result.Voters["dislikes"][0].Name != "Zoë Researcher" {
		t.Fatalf("unexpected voters: %+v", result.Voters)
	}
	if err := db.setVote(page, "orcid_a", 0); err != nil {
		t.Fatal(err)
	}
	result, _ = db.page(page)
	if result.Dislikes != 0 {
		t.Fatalf("removing vote failed: %+v", result)
	}
}

func TestORCIDAdapterRequiresAndStoresPublicName(t *testing.T) {
	orcid := "0000-0002-1825-0097"
	upstream := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.Header.Get("Authorization") != "Bearer token" {
			t.Errorf("token was not forwarded")
		}
		_ = json.NewEncoder(w).Encode(map[string]string{"sub": orcid, "name": "  Alice Example  "})
	}))
	defer upstream.Close()
	db := testStore(t)
	a := &app{config: config{orcidInfoURL: upstream.URL, provider: "orcid"}, store: db, client: upstream.Client()}
	request := httptest.NewRequest(http.MethodGet, "/internal/orcid/userinfo", nil)
	request.Header.Set("Authorization", "Bearer token")
	recorder := httptest.NewRecorder()
	a.orcidUserInfo(recorder, request)
	if recorder.Code != http.StatusOK {
		t.Fatalf("unexpected response: %d %s", recorder.Code, recorder.Body.String())
	}
	hash := sha1.Sum([]byte(orcid))
	person, found, err := db.identity("orcid_" + hex.EncodeToString(hash[:]))
	if err != nil || !found || person.Name != "Alice Example" || person.ORCID != orcid {
		t.Fatalf("identity not stored: %+v %t %v", person, found, err)
	}

	upstream.Config.Handler = http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) {
		_ = json.NewEncoder(w).Encode(map[string]string{"sub": orcid, "name": "  "})
	})
	recorder = httptest.NewRecorder()
	a.orcidUserInfo(recorder, request)
	if recorder.Code != http.StatusForbidden || !strings.Contains(recorder.Body.String(), "Make your name public") {
		t.Fatalf("private name was not rejected: %d %s", recorder.Code, recorder.Body.String())
	}
}

func TestReactionRequiresOriginAndCSRFHeader(t *testing.T) {
	db := testStore(t)
	a := &app{config: config{allowed: map[string]struct{}{"https://laxarchive.org": {}}}, store: db, limits: newRateLimits()}
	request := httptest.NewRequest(http.MethodPut, "/reactions/v1/reaction", strings.NewReader(`{"url":"https://laxarchive.org/Lax2/","reaction":"like"}`))
	request.Header.Set("Content-Type", "application/json")
	recorder := httptest.NewRecorder()
	a.putReaction(recorder, request)
	if recorder.Code != http.StatusForbidden {
		t.Fatalf("expected CSRF rejection, got %d", recorder.Code)
	}
}

func TestPublicIdentityEndpoint(t *testing.T) {
	db := testStore(t)
	remarkID := "orcid_" + strings.Repeat("a", 40)
	if err := db.putIdentity(identity{RemarkID: remarkID, ORCID: "0000-0002-1825-0097", Name: "Alice Example"}); err != nil {
		t.Fatal(err)
	}
	a := &app{store: db, limits: newRateLimits()}
	request := httptest.NewRequest(http.MethodGet, "/reactions/v1/identity?remark42_id="+remarkID, nil)
	recorder := httptest.NewRecorder()
	a.getIdentity(recorder, request)
	if recorder.Code != http.StatusOK {
		t.Fatalf("unexpected response: %d %s", recorder.Code, recorder.Body.String())
	}
	if recorder.Header().Get("Cache-Control") != "public, max-age=300" {
		t.Fatalf("identity is not cacheable")
	}
	var got publicIdentity
	if err := json.Unmarshal(recorder.Body.Bytes(), &got); err != nil {
		t.Fatal(err)
	}
	if got.RemarkID != remarkID || got.Name != "Alice Example" || got.Profile != "https://orcid.org/0000-0002-1825-0097" || got.AvatarURL != nil {
		t.Fatalf("unexpected identity: %+v", got)
	}
}

func TestSessionEndpointMarksStaleCookieForReauthentication(t *testing.T) {
	remark := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) {
		http.Error(w, "invalid session", http.StatusUnauthorized)
	}))
	defer remark.Close()
	a := &app{
		config: config{remarkUserURL: remark.URL},
		store:  testStore(t),
		client: remark.Client(),
		limits: newRateLimits(),
	}
	request := httptest.NewRequest(http.MethodGet, "/reactions/v1/me", nil)
	request.AddCookie(&http.Cookie{Name: "JWT", Value: "stale-session"})
	recorder := httptest.NewRecorder()
	a.getMe(recorder, request)
	if recorder.Code != http.StatusOK || !strings.Contains(recorder.Body.String(), `"reauthenticate":true`) {
		t.Fatalf("stale session was not identified: %d %s", recorder.Code, recorder.Body.String())
	}
}

func TestSessionEndpointReturnsValidatedPublicORCIDIdentity(t *testing.T) {
	const remarkID = "orcid_aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
	remark := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) {
		_ = json.NewEncoder(w).Encode(remarkUser{ID: remarkID, Name: "Alice Example"})
	}))
	defer remark.Close()
	db := testStore(t)
	if err := db.putIdentity(identity{RemarkID: remarkID, ORCID: "0000-0002-1825-0097", Name: "Alice Example"}); err != nil {
		t.Fatal(err)
	}
	a := &app{
		config: config{remarkUserURL: remark.URL},
		store:  db,
		client: remark.Client(),
		limits: newRateLimits(),
	}
	request := httptest.NewRequest(http.MethodGet, "/reactions/v1/me", nil)
	request.AddCookie(&http.Cookie{Name: "JWT", Value: "valid-session"})
	recorder := httptest.NewRecorder()
	a.getMe(recorder, request)
	if recorder.Code != http.StatusOK {
		t.Fatalf("unexpected session response: %d %s", recorder.Code, recorder.Body.String())
	}
	var got sessionResponse
	if err := json.Unmarshal(recorder.Body.Bytes(), &got); err != nil {
		t.Fatal(err)
	}
	if !got.Authenticated || !got.Eligible || got.Viewer == nil || got.Viewer.RemarkID != remarkID || got.Viewer.ORCID != "0000-0002-1825-0097" || got.Viewer.Profile != "https://orcid.org/0000-0002-1825-0097" {
		t.Fatalf("unexpected public session identity: %+v", got)
	}
}

func TestReactionClearsStaleHttpOnlySession(t *testing.T) {
	remark := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) {
		http.Error(w, "invalid session", http.StatusUnauthorized)
	}))
	defer remark.Close()
	a := &app{
		config: config{remarkUserURL: remark.URL},
		store:  testStore(t),
		client: remark.Client(),
		limits: newRateLimits(),
	}
	request := httptest.NewRequest(http.MethodPut, "/reactions/v1/reaction", strings.NewReader(`{"url":"https://laxarchive.org/Lax2/","reaction":"like"}`))
	request.Header.Set("Origin", "https://laxarchive.org")
	request.Header.Set("Content-Type", "application/json")
	request.Header.Set("X-Lax-CSRF", "1")
	request.AddCookie(&http.Cookie{Name: "JWT", Value: "stale-session"})
	recorder := httptest.NewRecorder()
	a.putReaction(recorder, request)
	if recorder.Code != http.StatusUnauthorized || !strings.Contains(recorder.Body.String(), "Sign in with ORCID again") {
		t.Fatalf("unexpected stale reaction response: %d %s", recorder.Code, recorder.Body.String())
	}
	cookies := recorder.Result().Cookies()
	if len(cookies) != 2 || cookies[0].Name != "JWT" || cookies[0].MaxAge != -1 || !cookies[0].HttpOnly || cookies[0].SameSite != http.SameSiteNoneMode || !cookies[0].Secure {
		t.Fatalf("stale session cookie was not cleared securely: %+v", cookies)
	}
}

func TestBridgeIsRestrictedToConfiguredParents(t *testing.T) {
	a := &app{config: config{bridgeParents: map[string]struct{}{"https://laxarchive.org": {}}}}
	htmlRequest := httptest.NewRequest(http.MethodGet, "/reactions/v1/bridge", nil)
	htmlRecorder := httptest.NewRecorder()
	a.bridgeHTML(htmlRecorder, htmlRequest)
	if htmlRecorder.Code != http.StatusOK || !strings.Contains(htmlRecorder.Header().Get("Content-Security-Policy"), "frame-ancestors https://laxarchive.org") || !strings.Contains(htmlRecorder.Body.String(), "/reactions/v1/bridge.js") {
		t.Fatalf("unexpected bridge page: %d %q %s", htmlRecorder.Code, htmlRecorder.Header().Get("Content-Security-Policy"), htmlRecorder.Body.String())
	}

	scriptRequest := httptest.NewRequest(http.MethodGet, "/reactions/v1/bridge.js", nil)
	scriptRecorder := httptest.NewRecorder()
	a.bridgeScript(scriptRecorder, scriptRequest)
	script := scriptRecorder.Body.String()
	if scriptRecorder.Code != http.StatusOK || !strings.Contains(script, `new Set(["https://laxarchive.org"])`) || strings.Contains(script, `postMessage(value,"*")`) || !strings.Contains(script, `request.action==="comments"`) || !strings.Contains(script, `request.action==="logout"`) {
		t.Fatalf("bridge script does not enforce exact parent origins: %s", scriptRecorder.Body.String())
	}
	for _, expected := range []string{`/api/v1/user?site=remark`, `/api/v1/comment?site=remark`, `X-XSRF-TOKEN`, `X-JWT`, `response.headers`, `pathname==="/auth/logout"`, `type:"session-change"`, `lax-reaction:v1:`} {
		if !strings.Contains(script, expected) {
			t.Fatalf("bridge script does not use the authenticated Remark42 iframe session, missing %q", expected)
		}
	}
	for _, forbidden := range []string{`jwt:activeJWT`, `token:activeJWT`, `xsrf:activeXSRF`} {
		if strings.Contains(script, forbidden) {
			t.Fatalf("bridge script exposes an authentication value to its parent: %q", forbidden)
		}
	}
}
