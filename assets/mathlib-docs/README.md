# Mathlib documentation link index

`declarations.json.gz` is a vendored build input, not a website asset. It
contains only declaration names and documentation paths from Mathlib's public
doc-gen index, sorted by name and compressed. The renderer reads it once;
visitors receive ordinary links, never this index. `snapshot.json` records
both the downloaded input's SHA-256 and the vendored file's SHA-256.

This snapshot was retrieved on 2026-09-30. Its destinations point to the
current public documentation, not to a submission's historical Mathlib
version. Link titles say so. Unknown names use verified source-module links
at the submission's full Mathlib commit, or remain plain if unavailable.

To intentionally refresh the snapshot, download the `source` URL recorded in
`snapshot.json`, then run:

```sh
node scripts/vendor-mathlib-docs.mjs /path/to/declaration-data.bmp
```

Review the changed hashes and declaration count, update the retrieval date
above, and verify links before committing the refreshed snapshot. Normal
builds and `references:fetch` never refresh it.

Upstream: https://leanprover-community.github.io/mathlib4_docs/
Mathlib source is licensed under Apache-2.0. This index contains names and
URLs only, with no copied documentation text.
