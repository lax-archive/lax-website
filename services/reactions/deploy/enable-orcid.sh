#!/bin/sh
set -eu
cd /opt/remark42
test -s orcid.env || {
  echo "Create /opt/remark42/orcid.env from orcid.env.example and add the ORCID credentials." >&2
  exit 1
}
docker compose --env-file .env --env-file orcid.env \
  -f compose.yaml -f compose.orcid.yaml -f compose.reactions.yaml config >/dev/null
docker compose --env-file .env --env-file orcid.env \
  -f compose.yaml -f compose.orcid.yaml -f compose.reactions.yaml up -d
