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
	"sort"
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
	remarkFindURL string
	remarkPostURL string
	orcidInfoURL  string
	provider      string
	allowed       map[string]struct{}
	bridgeParents map[string]struct{}
	publicOrigin  string
}

type remarkUser struct {
	ID   string `json:"id"`
	Name string `json:"name"`
}

type response struct {
	reactionPageResult
	ViewerReaction string      `json:"viewer_reaction"`
	ViewerFlag     *publicFlag `json:"viewer_flag,omitempty"`
	Authenticated  bool        `json:"authenticated"`
	Eligible       bool        `json:"eligible"`
	Reauthenticate bool        `json:"reauthenticate"`
	Viewer         *identity   `json:"viewer,omitempty"`
}

type sessionResponse struct {
	Authenticated  bool            `json:"authenticated"`
	Eligible       bool            `json:"eligible"`
	Reauthenticate bool            `json:"reauthenticate"`
	Viewer         *publicIdentity `json:"viewer,omitempty"`
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
	bridgeParents := map[string]struct{}{}
	for _, origin := range strings.Split(env("BRIDGE_PARENT_ORIGINS", "https://laxarchive.org,https://www.laxarchive.org,http://localhost:3000,http://127.0.0.1:3000"), ",") {
		if origin = strings.TrimSpace(origin); origin != "" {
			bridgeParents[origin] = struct{}{}
		}
	}
	return config{
		address:       env("LISTEN_ADDR", ":8081"),
		databasePath:  env("DATABASE_PATH", "/var/lib/reactions/reactions.db"),
		backupDir:     env("BACKUP_DIR", "/var/lib/reactions/backups"),
		remarkUserURL: env("REMARK_USER_URL", "http://remark42:8080/api/v1/user?site=remark"),
		remarkFindURL: env("REMARK_FIND_URL", "http://remark42:8080/api/v1/find"),
		remarkPostURL: env("REMARK_POST_URL", "http://remark42:8080/api/v1/comment?site=remark"),
		orcidInfoURL:  env("ORCID_USERINFO_URL", "https://orcid.org/oauth/userinfo"),
		provider:      env("AUTH_PROVIDER", "orcid"),
		allowed:       allowed,
		bridgeParents: bridgeParents,
		publicOrigin:  strings.TrimSuffix(env("PUBLIC_ORIGIN", "https://comments.laxarchive.org"), "/"),
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
	mux.HandleFunc("GET /reactions/v1/bridge", application.bridgeHTML)
	mux.HandleFunc("GET /reactions/v1/bridge.js", application.bridgeScript)
	mux.HandleFunc("OPTIONS /reactions/v1/{rest...}", application.preflight)
	mux.HandleFunc("GET /reactions/v1/me", application.getMe)
	mux.HandleFunc("GET /reactions/v1/page", application.getPage)
	mux.HandleFunc("GET /reactions/v1/identity", application.getIdentity)
	mux.HandleFunc("GET /reactions/v1/identities", application.getIdentities)
	mux.HandleFunc("PUT /reactions/v1/reaction", application.putReaction)
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

func remarkIdentityID(provider, orcid string) string {
	hash := sha1.Sum([]byte(orcid)) //nolint:gosec -- compatibility identifier, not a credential
	return provider + "_" + hex.EncodeToString(hash[:])
}

func (a *app) security(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("X-Content-Type-Options", "nosniff")
		w.Header().Set("Referrer-Policy", "strict-origin-when-cross-origin")
		w.Header().Set("Content-Security-Policy", "default-src 'none'; frame-ancestors 'none'")
		if strings.HasPrefix(r.URL.Path, "/reactions/") {
			origin := r.Header.Get("Origin")
			if origin != "" {
				_, allowed := a.config.allowed[origin]
				if origin == a.config.publicOrigin {
					allowed = true
				}
				if !allowed {
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

func (a *app) bridgeHTML(w http.ResponseWriter, _ *http.Request) {
	parents := make([]string, 0, len(a.config.bridgeParents))
	for origin := range a.config.bridgeParents {
		if parsed, err := url.Parse(origin); err == nil && (parsed.Scheme == "https" || parsed.Scheme == "http") && parsed.Host != "" && parsed.Path == "" && parsed.RawQuery == "" && parsed.Fragment == "" {
			parents = append(parents, origin)
		}
	}
	sort.Strings(parents)
	w.Header().Set("Content-Type", "text/html; charset=utf-8")
	w.Header().Set("Cache-Control", "no-store")
	w.Header().Set("Content-Security-Policy", "default-src 'none'; script-src 'self'; connect-src 'self'; frame-ancestors "+strings.Join(parents, " "))
	_, _ = io.WriteString(w, `<!doctype html><html lang="en"><meta charset="utf-8"><title>Reactions bridge</title><script src="/reactions/v1/bridge.js" defer></script></html>`)
}

func (a *app) bridgeScript(w http.ResponseWriter, _ *http.Request) {
	parents := make([]string, 0, len(a.config.bridgeParents))
	for origin := range a.config.bridgeParents {
		parents = append(parents, origin)
	}
	sort.Strings(parents)
	encoded, _ := json.Marshal(parents)
	w.Header().Set("Content-Type", "text/javascript; charset=utf-8")
	w.Header().Set("Cache-Control", "no-store")
	const bridgeSource = `(function(){
"use strict";
const allowed=new Set(__ALLOWED_PARENTS__);
const parentOrigin=(()=>{try{return new URL(document.referrer).origin}catch{return ""}})();
if(!allowed.has(parentOrigin))return;
const send=(value)=>window.parent.postMessage(value,parentOrigin);
let announce=()=>{};
let notifySessionChange=()=>{};
let activeJWT="";
let activeXSRF="";
let sessionCache=null;
let sessionCacheAt=0;
let sessionPromise=null;
const clearSessionCache=()=>{sessionCache=null;sessionCacheAt=0};
const nativeFetch=window.fetch.bind(window);
const rememberHeaders=(headers)=>{
  if(!headers)return;
  const values=new Headers(headers);
  const jwt=values.get("X-JWT");
  const xsrf=values.get("X-XSRF-TOKEN");
  const changedJWT=Boolean(jwt)&&jwt!==activeJWT;
  if(jwt)activeJWT=jwt;
  if(xsrf)activeXSRF=xsrf;
  if(changedJWT){clearSessionCache();notifySessionChange()}
};
window.fetch=async(input,init)=>{
  let local=false;
  let requestURL=null;
  try{
    const raw=typeof input==="string"?input:input.url;
    requestURL=new URL(raw,window.location.href);
    local=requestURL.origin===window.location.origin;
    if(local){
      if(input instanceof Request)rememberHeaders(input.headers);
      if(init&&init.headers)rememberHeaders(init.headers);
    }
  }catch{}
  const response=await nativeFetch(input,init);
  if(local){
    rememberHeaders(response.headers);
    const loggedOut=requestURL&&requestURL.pathname==="/auth/logout"&&response.ok;
    const rejectedSession=(response.status===401||response.status===403)&&Boolean(activeJWT);
    if(loggedOut||rejectedSession){
      activeJWT="";
      activeXSRF="";
      clearSessionCache();
      notifySessionChange();
    }
  }
  return response;
};
const authHeaders=(values={})=>{
  const headers=new Headers(values);
  if(activeJWT)headers.set("X-JWT",activeJWT);
  const xsrf=activeXSRF||cookie("XSRF-TOKEN");
  if(xsrf)headers.set("X-XSRF-TOKEN",xsrf);
  return headers;
};
const fail=(message,status=503)=>Object.assign(new Error(message),{status});
const readJSON=async(response)=>{try{return await response.json()}catch{return {}}};
const canonicalPage=(raw)=>{
  const value=new URL(raw);
  if(value.origin!=="https://laxarchive.org"||value.username||value.password||value.search||value.hash)throw fail("invalid page URL",400);
  const submission=/^\/[A-Za-z0-9][A-Za-z0-9._-]*\/$/.test(value.pathname);
  const concept=/^\/[A-Za-z0-9][A-Za-z0-9._-]*\/[A-Za-z0-9][A-Za-z0-9._-]*\.html$/.test(value.pathname);
  if(!submission&&!concept)throw fail("invalid page URL",400);
  return value.toString();
};
const remarkUser=async()=>{
  const response=await fetch("/api/v1/user?site=remark",{credentials:"include",cache:"no-store",headers:authHeaders({Accept:"application/json"})});
  if(response.status===401||response.status===403)return null;
  if(!response.ok)throw fail("authentication is temporarily unavailable");
  const user=await readJSON(response);
  return user&&typeof user.id==="string"&&/^orcid_[a-f0-9]{40}$/.test(user.id)?user:null;
};
const session=async()=>{
  if(sessionCache&&Date.now()-sessionCacheAt<2000)return sessionCache;
  if(sessionPromise)return sessionPromise;
  sessionPromise=(async()=>{
    const user=await remarkUser();
    if(!user)return {authenticated:false,eligible:false,reauthenticate:false};
    const response=await fetch("/reactions/v1/identity?remark42_id="+encodeURIComponent(user.id),{cache:"no-store",headers:{Accept:"application/json"}});
    if(!response.ok)return {authenticated:true,eligible:false,reauthenticate:false};
    const viewer=await readJSON(response);
    return {authenticated:true,eligible:true,reauthenticate:false,viewer};
  })();
  try{
    sessionCache=await sessionPromise;
    sessionCacheAt=Date.now();
    return sessionCache;
  }finally{sessionPromise=null}
};
const page=async(raw)=>{
  const url=canonicalPage(raw);
  const [pageResponse,viewerSession]=await Promise.all([
    fetch("/reactions/v1/page?url="+encodeURIComponent(url),{cache:"no-store",headers:{Accept:"application/json"}}),
    session()
  ]);
  const data=await readJSON(pageResponse);
  if(!pageResponse.ok)throw fail(data.error||"page responses are temporarily unavailable",pageResponse.status);
  Object.assign(data,viewerSession,{viewer_reaction:"",viewer_flag:null});
  if(viewerSession.eligible&&viewerSession.viewer){
    for(const reaction of ["endorse","flag"]){
      const voters=Array.isArray(data.voters&&data.voters[reaction])?data.voters[reaction]:[];
      if(voters.some((voter)=>voter&&voter.orcid===viewerSession.viewer.orcid_id)){
        data.viewer_reaction=reaction;
        if(reaction==="flag")data.viewer_flag=(Array.isArray(data.flags)?data.flags:[]).find((flag)=>flag&&flag.author&&flag.author.orcid===viewerSession.viewer.orcid_id)||null;
        break
      }
    }
  }
  return data;
};
const cookie=(name)=>{
  const prefix=name+"=";
  const item=document.cookie.split(";").map((value)=>value.trim()).find((value)=>value.startsWith(prefix));
  return item?decodeURIComponent(item.slice(prefix.length)):"";
};
const flagMessage=(value)=>{
  const message=typeof value==="string"?value.replace(/\r\n/g,"\n").trim():"";
  if(!message||new TextEncoder().encode(message).length>2000||message.includes("\u0000"))throw fail("A flag explanation is required and must be under 2,000 bytes.",400);
  return message;
};
const sourceLine=(start,end)=>{
  start=Number.isInteger(start)?start:0;end=Number.isInteger(end)?end:0;
  if(start===0&&end===0)return [0,0];
  if(start<1||end!==start||end>1000000)throw fail("Choose one valid source line.",400);
  return [start,end];
};
const reviewMarker=(reaction,message,start,end)=>{
  if(reaction==="endorse")return "✅ Endorsed\n\nlax-review:v2:endorse";
  if(reaction==="clear")return "↩️ Review cleared\n\nlax-review:v2:clear";
  if(reaction!=="flag")throw fail("Invalid review.",400);
  const line=sourceLine(start,end);
  return "🚩 "+flagMessage(message)+"\n\nlax-review:v2:flag:"+line[0]+":"+line[1];
};
const saveReaction=async(raw,reaction,message="",lineStart=0,lineEnd=0)=>{
  const current=await page(raw);
  if(!current.eligible)throw fail("Sign in with ORCID to review.",401);
  const xsrf=activeXSRF||cookie("XSRF-TOKEN");
  if(!xsrf)throw fail("Your comment session is not ready. Refresh the page and try again.",401);
  if(new URL(current.url).pathname.endsWith("/")&&(lineStart||lineEnd))throw fail("Submission flags cannot reference concept source lines.",400);
  const hidden=new URL(current.url);
  hidden.pathname="/_reactions"+hidden.pathname;
  const next=reaction==="endorse"&&current.viewer_reaction==="endorse"?"clear":reaction;
  const marker=reviewMarker(next,message,lineStart,lineEnd);
  const response=await fetch("/api/v1/comment?site=remark",{
    method:"POST",credentials:"include",
    headers:authHeaders({Accept:"application/json","Content-Type":"application/json","X-XSRF-TOKEN":xsrf}),
    body:JSON.stringify({text:marker,title:"Lax Archive review",locator:{site:"remark",url:hidden.toString()}})
  });
  const result=await readJSON(response);
  if(!response.ok)throw fail(result.error||"unable to save your response",response.status);
  return page(current.url);
};
window.addEventListener("message",async(event)=>{
  if(!allowed.has(event.origin)||!event.data||event.data.source!=="lax-reactions"||typeof event.data.id!=="string")return;
  const request=event.data;
  try{
    let data={};
    if(request.action==="page"&&typeof request.url==="string")data=await page(request.url);
    else if(request.action==="me")data=await session();
    else if(request.action==="reaction"&&typeof request.url==="string"&&["endorse","flag","clear"].includes(request.reaction))data=await saveReaction(request.url,request.reaction,request.message,request.line_start,request.line_end);
    else if(request.action==="comments"&&typeof request.site==="string"&&/^[a-zA-Z0-9._-]{1,64}$/.test(request.site)&&typeof request.user==="string"&&/^orcid_[a-f0-9]{40}$/.test(request.user)&&Number.isInteger(request.skip)&&request.skip>=0&&Number.isInteger(request.limit)&&request.limit>=1&&request.limit<=100){
      const response=await fetch("/api/v1/comments?site="+encodeURIComponent(request.site)+"&user="+encodeURIComponent(request.user)+"&skip="+request.skip+"&limit="+request.limit,{credentials:"include",cache:"no-store",headers:{Accept:"application/json"}});
      data=await readJSON(response);
      if(!response.ok)throw fail(data.error||"comments are temporarily unavailable",response.status);
    }else if(request.action==="logout"){
      const response=await fetch("/auth/logout",{credentials:"include",cache:"no-store"});
      if(!response.ok)throw fail("sign out failed",response.status);
    }else throw fail("invalid bridge request",400);
    send({source:"lax-reactions",id:request.id,ok:true,status:200,data});
  }catch(error){
    send({source:"lax-reactions",id:request.id,ok:false,status:Number(error&&error.status)||503,data:{error:error instanceof Error?error.message:"Account service is temporarily unavailable."}});
  }
});
announce=()=>send({source:"lax-reactions",type:"ready"});
notifySessionChange=()=>send({source:"lax-reactions",type:"session-change"});
announce();
for(const delay of [250,1000,3000])setTimeout(announce,delay);
})();`
	script := strings.Replace(bridgeSource, "__ALLOWED_PARENTS__", string(encoded), 1)
	_, _ = io.WriteString(w, script)
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
	result, err := a.reactionPage(r.Context(), pageURL)
	if err != nil {
		return response{}, err
	}
	answer := response{reactionPageResult: result}
	user, err := a.currentUser(r)
	if err != nil || user == nil {
		answer.Reauthenticate = user == nil && hasRemarkSession(r)
		return answer, err
	}
	answer.Authenticated = true
	person, found, err := a.store.identity(user.ID)
	if err != nil || !found || strings.TrimSpace(person.Name) == "" {
		return answer, err
	}
	answer.Eligible = true
	answer.Viewer = &person
	viewerReview := result.viewerByRemarkID[user.ID]
	answer.ViewerReaction = viewerReview.Kind
	if viewerReview.Kind == reviewFlag {
		for index := range result.Flags {
			if result.Flags[index].Author.ORCID == person.ORCID {
				answer.ViewerFlag = &result.Flags[index]
				break
			}
		}
	}
	answer.reactionPageResult.viewerByRemarkID = nil
	return answer, nil
}

func hasRemarkSession(r *http.Request) bool {
	cookie, err := r.Cookie("JWT")
	return err == nil && strings.TrimSpace(cookie.Value) != ""
}

func clearRemarkSession(w http.ResponseWriter) {
	for _, cookie := range []*http.Cookie{
		{Name: "JWT", Value: "", Path: "/", MaxAge: -1, HttpOnly: true, Secure: true, SameSite: http.SameSiteNoneMode},
		{Name: "XSRF-TOKEN", Value: "", Path: "/", MaxAge: -1, Secure: true, SameSite: http.SameSiteNoneMode},
	} {
		http.SetCookie(w, cookie)
	}
}

func (a *app) getMe(w http.ResponseWriter, r *http.Request) {
	if !a.limits.allow(clientIP(r), false) {
		w.Header().Set("Retry-After", "10")
		writeError(w, http.StatusTooManyRequests, "too many requests")
		return
	}
	answer := sessionResponse{}
	user, err := a.currentUser(r)
	if err != nil {
		log.Printf("session response failed: %v", err)
		writeError(w, http.StatusServiceUnavailable, "authentication is temporarily unavailable")
		return
	}
	if user == nil {
		answer.Reauthenticate = hasRemarkSession(r)
		writeJSON(w, http.StatusOK, answer)
		return
	}
	answer.Authenticated = true
	person, found, err := a.store.identity(user.ID)
	if err != nil {
		writeError(w, http.StatusServiceUnavailable, "identity lookup is temporarily unavailable")
		return
	}
	if found && strings.TrimSpace(person.Name) != "" {
		answer.Eligible = true
		public := toPublicIdentity(person)
		answer.Viewer = &public
	}
	writeJSON(w, http.StatusOK, answer)
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

func (a *app) putReaction(w http.ResponseWriter, r *http.Request) {
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
		URL       string `json:"url"`
		Reaction  string `json:"reaction"`
		Message   string `json:"message,omitempty"`
		LineStart int    `json:"line_start,omitempty"`
		LineEnd   int    `json:"line_end,omitempty"`
	}
	decoder := json.NewDecoder(http.MaxBytesReader(w, r.Body, 8<<10))
	decoder.DisallowUnknownFields()
	if err := decoder.Decode(&input); err != nil || !validReview(input.Reaction) {
		writeError(w, http.StatusBadRequest, "review must be endorse, flag, or clear")
		return
	}
	pageURL, err := canonicalPage(input.URL)
	if err != nil {
		writeError(w, http.StatusBadRequest, err.Error())
		return
	}
	event := reviewEvent{Kind: input.Reaction, Message: input.Message, LineStart: input.LineStart, LineEnd: input.LineEnd}
	if strings.HasSuffix(pageURL, "/") && (event.LineStart != 0 || event.LineEnd != 0) {
		writeError(w, http.StatusBadRequest, "submission flags cannot reference concept source lines")
		return
	}
	if _, err = reviewMarker(event); err != nil {
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
		if hasRemarkSession(r) {
			clearRemarkSession(w)
			writeError(w, http.StatusUnauthorized, "Your session is no longer valid. Sign in with ORCID again.")
			return
		}
		writeError(w, http.StatusUnauthorized, "Sign in with ORCID to review.")
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
	current, err := a.reactionPage(r.Context(), pageURL)
	if err != nil {
		writeError(w, http.StatusServiceUnavailable, "unable to read current reactions")
		return
	}
	if input.Reaction == reviewEndorse && current.viewerByRemarkID[user.ID].Kind == reviewEndorse {
		event = reviewEvent{Kind: reviewClear}
	}
	if err = a.appendReview(r, pageURL, event); err != nil {
		log.Printf("save review failed: %v", err)
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
	remarkID := remarkIdentityID(a.config.provider, orcid)
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
