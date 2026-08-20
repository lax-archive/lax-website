#!/bin/sh
set -eu

iframe_file="${1:-/opt/remark42/custom-web/iframe.html}"
bridge_tag='<script src="/reactions/v1/bridge.js"></script>'
old_bridge_tag='<script src="/reactions/v1/bridge.js" defer></script>'

if grep -Fq "$bridge_tag" "$iframe_file"; then
  exit 0
fi

temporary_file="${iframe_file}.lax-bridge.tmp"
if grep -Fq "$old_bridge_tag" "$iframe_file"; then
  sed "s#$old_bridge_tag#$bridge_tag#" "$iframe_file" > "$temporary_file"
else
  sed "s#</head>#$bridge_tag\n</head>#" "$iframe_file" > "$temporary_file"
fi
chmod --reference="$iframe_file" "$temporary_file"
chown --reference="$iframe_file" "$temporary_file"
mv "$temporary_file" "$iframe_file"
