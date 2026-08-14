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

func TestVoteRequiresOriginAndCSRFHeader(t *testing.T) {
	db := testStore(t)
	a := &app{config: config{allowed: map[string]struct{}{"https://laxarchive.org": {}}}, store: db, limits: newRateLimits()}
	request := httptest.NewRequest(http.MethodPut, "/reactions/v1/vote", strings.NewReader(`{"url":"https://laxarchive.org/Lax2/","vote":1}`))
	request.Header.Set("Content-Type", "application/json")
	recorder := httptest.NewRecorder()
	a.putVote(recorder, request)
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

func TestVoteClearsStaleHttpOnlySession(t *testing.T) {
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
	request := httptest.NewRequest(http.MethodPut, "/reactions/v1/vote", strings.NewReader(`{"url":"https://laxarchive.org/Lax2/","vote":1}`))
	request.Header.Set("Origin", "https://laxarchive.org")
	request.Header.Set("Content-Type", "application/json")
	request.Header.Set("X-Lax-CSRF", "1")
	request.AddCookie(&http.Cookie{Name: "JWT", Value: "stale-session"})
	recorder := httptest.NewRecorder()
	a.putVote(recorder, request)
	if recorder.Code != http.StatusUnauthorized || !strings.Contains(recorder.Body.String(), "Sign in with ORCID again") {
		t.Fatalf("unexpected stale vote response: %d %s", recorder.Code, recorder.Body.String())
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
	if scriptRecorder.Code != http.StatusOK || !strings.Contains(scriptRecorder.Body.String(), `new Set(["https://laxarchive.org"])`) || strings.Contains(scriptRecorder.Body.String(), `postMessage(value,"*")`) {
		t.Fatalf("bridge script does not enforce exact parent origins: %s", scriptRecorder.Body.String())
	}
}
