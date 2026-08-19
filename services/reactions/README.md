# Lax community review service

This companion service adds two page-level review actions per ORCID identity
and canonical submission/concept URL:

- `✅ Endorse` says that the page is correct.
- `🚩 Flag` says that something may be false and requires a public explanation.
  A concept flag may also reference a contiguous range of Lean source lines.

It deliberately reuses the HttpOnly Remark42 session instead of creating
browser-readable credentials or a second account system.

Each change is an append-only Remark42 comment on a deterministic hidden
thread below `https://laxarchive.org/_reactions/`. The service-owned bridge,
never the parent website, constructs the hidden locator and a reserved
`lax-review:v2:*` marker. A flag's human-readable comment begins with `🚩` and
the reserved final line carries its validated source range. The latest valid
top-level event per Remark42 user ID wins; endorsing again or removing a flag
appends a `clear` event. Legacy reaction markers are deliberately ignored so
an old unexplained dislike cannot silently become a public accusation.

Normal discussion threads therefore never contain these structured review
events. Flag explanations appear only in the dedicated flag view and, when a
valid range is present, beside the annotated source lines. Review history is
covered by Remark42's existing backups. Product comment views explicitly
reject the reserved hidden path.

During ORCID login, Remark42 calls the service's internal user-info adapter.
The adapter forwards the bearer token to ORCID without storing or logging it,
requires an authenticated ORCID iD and public display name, and stores the
name/iD mapping used for public voter lists. Remark42 receives only the
normalized `sub` and `name` claims. Reauthentication refreshes the stored name.

The public API is mounted at `/reactions/v1/` behind the same Caddy origin as
Remark42. Mutations require an allowed `Origin`, JSON content type, and the
`X-Lax-CSRF: 1` header. The service validates the Remark42 session server-side,
rate-limits reads and writes, and accepts only canonical production URLs.

Persistent data and 14 daily online backups live below `/var/lib/reactions`.

The public service is hosted at `https://comments.laxarchive.org`. Keeping the
comment service below the same registrable domain as `laxarchive.org` avoids
third-party cookie partitioning across Firefox, Safari, and Chromium browsers.
The ORCID application redirect URI is
`https://comments.laxarchive.org/auth/orcid/callback`.

Firefox can partition the Remark42 cookie used in the comment iframe from a
top-level cross-origin fetch. `/reactions/v1/bridge` is a minimal same-origin
iframe bridge for page and reaction requests. It checks the user and writes the
reserved hidden comment through Remark42 in the same browser context as the
working discussion iframe. Remark42 rotates its short-lived `X-JWT` header and
keeps that value in frontend memory; the bridge observes and reuses the header
only inside the iframe so Firefox's partitioned-cookie behavior cannot split
the two features. No credential is logged, persisted, or sent to the parent;
only public aggregation and identity lookup go through the companion API. Both
sides require exact origins, the bridge is frame-restricted by CSP, and the
HttpOnly session remains confined to the comments origin. `GET
/reactions/v1/me` remains the direct-client compatibility path and reports
`reauthenticate:true` for a stale Remark42 cookie.

The bridge also emits a credential-free session-change signal when Remark42
logs in, logs out, or rejects an expired token. The parent immediately
rechecks both the header account and page reactions, so the two views cannot
retain a stale signed-in or signed-out state after an action in the discussion.
Archive login controls use a same-tab OAuth round trip rather than a popup;
the callback therefore returns to a fresh page where the header, reactions,
and embedded discussion initialize from one session at the same time.

`deploy/install-iframe-bridge.sh` idempotently adds the service-owned bridge
script to the mounted Remark42 `iframe.html`. Run it whenever the custom
Remark42 web bundle is replaced.

Public validated identity lookup is available for account and comment UIs:

```text
GET /reactions/v1/identity?remark42_id=orcid_<40 lowercase hex>
GET /reactions/v1/identities?remark42_id=<id>&remark42_id=<id>  (maximum 50)
```

The single response is `{remark42_id, orcid_id, name, profile_url,
avatar_url:null}`; unknown or unvalidated users return 404. The batch response
is `{identities:[...]}` and omits unknown users. Both are public, contain no
tokens or private claims, and are cacheable for five minutes.

```sh
docker build -t lax-reactions .
docker run --rm -p 8081:8081 \
  -e REMARK_USER_URL=http://remark42:8080/api/v1/user?site=remark \
  -e REMARK_FIND_URL=http://remark42:8080/api/v1/find \
  -e 'REMARK_POST_URL=http://remark42:8080/api/v1/comment?site=remark' \
  -v /var/lib/reactions:/var/lib/reactions lax-reactions
```
