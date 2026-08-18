# Lax page reactions

This companion service adds one page-level like, dislike, or rocket reaction
per ORCID identity and canonical submission/concept URL. It deliberately
reuses the HttpOnly Remark42 session instead of creating browser-readable
credentials or a second account system.

Each change is an append-only Remark42 comment on a deterministic hidden
thread below `https://laxarchive.org/_reactions/`. The service-owned bridge,
never the parent website, constructs the hidden locator and the reserved
`lax-reaction:v1:<reaction>` marker. The latest valid top-level event per
Remark42 user ID wins; selecting an active reaction appends a `clear` event.
Normal discussion threads therefore remain unchanged, while the reaction
history is covered by Remark42's existing backups. Product comment views
explicitly reject the reserved hidden path.

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
working discussion iframe; only public aggregation and identity lookup go
through the companion API. Both sides require exact origins and window
references, the bridge is frame-restricted by CSP, and the HttpOnly JWT is
never exposed. `GET /reactions/v1/me` remains the direct-client compatibility
path and reports `reauthenticate:true` for a stale Remark42 cookie.

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
