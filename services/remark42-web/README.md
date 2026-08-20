# Lax Remark42 frontend

This is a narrow source-level customization of Remark42 v1.16.4, pinned to
upstream commit `6e7820d2b726ff96b686aff80e8e642ee06bfbfd` (the exact version used by the
server image). The base64 file decodes to a normal Git patch. Keeping it
encoded prevents the repository patch tool from interpreting the nested Git
patch as instructions; `build.sh` always verifies it with `git apply --check`.

The customization does three things:

- when ORCID is the only provider, the sign-in control opens ORCID directly;
- validated ORCID names come from `/reactions/v1/identity`, so an old embedded
  `noname_*` value is never presented as the researcher's name;
- validated names are accessible links to the canonical public ORCID profile,
  rather than controls that open Remark42's internal user profile.

Build and test it locally:

```sh
services/remark42-web/build.sh /tmp/lax-remark42-web
```

The generated directory is deployment output and must not be committed. It is
copied to `/opt/remark42/custom-web` on Lightsail and mounted at `/srv/web` by
`compose.web.yaml`. On a Remark42 upgrade, change the pinned commit, regenerate
the source patch against that commit, and run the complete build before
deploying. The existing custom directory and Compose override are the rollback
artifacts.
