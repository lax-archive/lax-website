#!/bin/sh
set -eu

output=${1:?usage: build.sh OUTPUT_DIRECTORY}
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
source_dir=$(mktemp -d "${TMPDIR:-/tmp}/lax-remark42-web.XXXXXX")
trap 'rm -rf "$source_dir"' EXIT HUP INT TERM

git clone --filter=blob:none https://github.com/umputun/remark42.git "$source_dir"
git -C "$source_dir" checkout --detach 6e7820d2b726ff96b686aff80e8e642ee06bfbfd

patch_file="$source_dir/lax-orcid.patch"
if ! base64 -D <"$script_dir/lax-orcid.patch.b64" >"$patch_file" 2>/dev/null; then
  base64 -d <"$script_dir/lax-orcid.patch.b64" >"$patch_file"
fi
git -C "$source_dir" apply --check "$patch_file"
git -C "$source_dir" apply "$patch_file"

cd "$source_dir/frontend"
CI=1 corepack pnpm install --frozen-lockfile
corepack pnpm --filter @remark42/app type-check
corepack pnpm --filter @remark42/app test -- --runInBand \
  app/components/auth/auth.spec.tsx \
  app/components/comment/comment.test.tsx
corepack pnpm --filter @remark42/app build

mkdir -p "$output"
cp -R apps/remark42/public/. "$output/"
printf '%s\n' 'remark42 6e7820d2b726ff96b686aff80e8e642ee06bfbfd + lax-orcid.patch' >"$output/LAX_BUILD"
