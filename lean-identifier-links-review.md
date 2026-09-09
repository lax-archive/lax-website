# Lean identifier navigation review

Implemented and reviewed on `codex/fix-lean-identifier-links`, based on website
commit `5e93143b`. The user approved publication to `main` on 2026-09-09.

## Problem and final design

The original static-link approach fits the website, but its name lookup knew
concept and statement IDs rather than all ordinary declarations. It missed
`Lax17.Treewidth.treewidth` and `Lax17.GridMinor.ContainsGridMinor`. Inferring
short aliases from imported source also confused namespaces and shadowing.
Repeated whole-source replacements made rendering scale poorly.

A lexical inventory fixed ordinary names and the unqualified occurrences of
`HasTreewidthAtMost`, but could not resolve typed projections, record keys,
aliases or arbitrary Lean syntax reliably. Adding more spelling rules would
reimplement part of Lean and still leave gaps.

The final archive build uses Lean's own `.ilean` reference maps. They already
exist in every current concept's sealed capture; no archive schema change,
recompilation, Lean installation in CI, or execution of submissions is needed.
Lean records each constant's owning module, full declaration name, definition
span and usage spans, including field information. The frontend deliberately
omits local variables. The website consumes version 5 of this format, using
its LSP UTF-16 positions against the exact displayed source.

Primary implementation references:
[Lean reference serialization and field handling](https://github.com/leanprover/lean4/blob/v4.30.0/src/Lean/Server/References.lean)
and [the frontend's ilean output](https://github.com/leanprover/lean4/blob/v4.30.0/src/Lean/Elab/Frontend.lean).
The archive's capture format 1 uses sorted, epoch-zero, uncompressed ustar
(`lax/src/submission-validation/captures/seal.ts`).

`references:fetch` caches verified compiler metadata before building.
`loadSubmissions` attaches parsed references; `source-links.ts` indexes
destinations and consumes recorded usages. The existing highlighter wraps
original highlighted text with static relative anchors. Both concept pages
and paper cards share this index and target canonical concept pages.

This handles record literals and updates, fields on different types sharing
the same spelling, namespace aliases, private globals, inductive constructors
and generated helpers. Helpers without their own source span navigate to
their nearest enclosing declaration; a module is the fallback only when no
enclosing declaration has a span. No such module-only fallback is needed by
the current archive's referenced globals.

Definition sites remain plain, including structure field declarations and
compiler-reported uses overlapping a definition. Locals and external library
names, including Mathlib and Lean's standard library, remain plain. Imported
archive module names still link to their concept pages. Duplicate compiler
spans such as `T` and `T.{u}` link only the precise name, leaving `u` plain.

Lean's reference maps omit namespace operands. A supplemental index of
archive namespaces and declarations links `open` operands to their owning
concept page, or to a declaration's comments when opening a type namespace.
Lookup respects the current namespace, its parents, `_root_`, and the
module's archive import closure. Unknown or ambiguous destinations stay
plain. Selective openings, hiding and renaming do not turn selected names
into namespace guesses; their declaration links still come from Lean.
Comments, strings, syntax quotations and section labels are excluded.
Standalone submission namespace names, such as `open Lax17`, `namespace
Lax17` and `end Lax17`, link to the submission index. Visible submission IDs
in page metadata, version banners and paper references link there too. The ID
beneath a submission's own title stays plain to avoid a self-link.

The conservative lexical implementation remains available for local `lax`
callers without captures and explicit `--no-references` builds. Normal CLI,
CI and branch-preview builds require captured references; missing or
unsupported metadata produces a build error instead of silently falling
back to incomplete navigation.

## Landing and presentation

Links land at the beginning of preceding comments, including field comments,
or at the declaration's attributes/modifiers when no comments precede it.
Statements retain their stable `s-…` IDs at that same comment start.
The reported targets remain `Lax17.Treewidth.html#L62`,
`Lax17.GridMinor.html#L20`, and `Lax17.Treewidth.html#L57` for the three uses
of `HasTreewidthAtMost`. `D.Node`, `D.bag` and `D.nodeFintype` now link their
field components to the respective field comments.

Native fragment navigation aligns the target below the sticky header, with
CSS providing enough trailing scroll space even on short pages. Hover and
keyboard focus use bold text, preserve syntax colours, and have no underline.
The proof/review rails allow pointer events only on their actual controls,
so padding cannot intercept a neighbouring source link.

## Scaling

- Current data: 402 concept modules in 35 nonempty captures. The ilean
  payloads total 1,455,837 bytes. Fetching them uses 112 bounded HTTP ranges
  totalling 6,937,930 bytes, rather than downloading approximately 1.59 GB
  of capture file contents. A warm fetch makes no registry requests.
- Nearby members share a request, with gaps limited to 64 KiB and groups to
  2 MiB (one individually bounded larger member can use a larger range).
  Capture manifests are bounded and indexed once per submission. Cache files
  are named by content digest and reused across database updates and branches.
- Each immutable site model builds its source/target index once and caches
  resolved links. Semantic lookup uses exact owning-module/name pairs rather
  than searching imports for each occurrence. Overlap handling sorts ranges
  and sweeps definition sites. Rendering walks highlighted fragments without
  repeated whole-source substitutions or a line-count × reference-count loop.
- No browser-side index, extra script, runtime network request, dependency or
  CSP exception is introduced. Other site features still have their existing
  dependency-graph costs; this is not a claim that the whole build is linear.

## Integrity and security boundaries

- Only strict, digest-addressed public GHCR references are accepted. Downloads
  use anonymous pull tokens, fixed HTTPS hosts, bounded redirects and timeouts.
  Tokens go only to GHCR, never to the signed storage redirect. Token responses
  cannot redirect, and credentials, alternate ports and off-list hosts are
  rejected on blob redirects.
- Byte-range requests require HTTP 206 and an exact Content-Range. Ignored
  ranges never cause a full capture download. Responses are size-bounded while
  streaming, including when no Content-Length is supplied; truncated or
  oversized ranges fail before any cache entry is published.
- Capture format, paths, duplicate entries, file/directory collisions, counts
  and sizes are checked. The offsets mirror the recorded tar traversal, but
  are never trusted alone: each requested member's ustar checksum, path,
  regular-file type and size must match, followed by SHA-256 verification
  against the database manifest. Tar files are never extracted.
- Each displayed source must match its captured source's size and SHA-256.
  Metadata is capped at 8 MiB per module, parsed as inert JSON, and checked for
  module identity, supported version, schema, range bounds, direction and
  Unicode boundaries. Cache reads recheck size and digest; writes use a unique
  temporary file and atomic rename. Wrong metadata cannot silently generate
  links for a newer source revision.
- Hrefs are constructed from generated archive destinations, with encoded
  components. The renderer separately rejects active schemes/external hrefs
  and escapes source labels. Compiler names, quoted identifiers and metadata
  never become executable code or raw HTML. Syntax-highlighting failure still
  produces escaped text with links and comment math.

## Validation

Validation used the read-only database at
`66e58be2c0e10217a9959307d2a6d1a069e3394c`, including all 402 concepts,
265 proofs and three papers with PDFs and reflow bundles.

- All 402 captured reference files were fetched and verified from GHCR.
- An independent metadata audit found 4,634 archive constant usages: 15
  overlap definition sites and are intentionally plain; all remaining 4,619
  have navigation to the compiler-recorded owning module. Duplicate universe
  spans account for multiple metadata records sharing one precise link.
- An independent source audit found 513 archive namespace operands across
  337 `open` commands; all 513 have links. Namespace navigation preserves
  the existing coverage of all 4,619 eligible compiler-recorded usages.
- Concept pages contain 5,650 source links including imported modules. Across
  paper cards and concept pages, all 9,716 source links and all static local
  links resolve. No duplicate IDs, changed CSP values or displayed-source
  differences were found across 717 HTML pages. Dynamic paper passage anchors
  are excluded from static checking; every source target is checked against
  an emitted ID.
- Two complete builds produced identical 834-file output trees.
- `npm run check` passed 187 tests. The six browser tests normally skipped
  without Chromium also passed with system Chrome. They cover desktop/mobile,
  JavaScript enabled/disabled, native comment alignment, bold focus, proof-rail
  hit testing, record keys, record updates, typed projections, opened type
  namespaces, and the paper viewer. Existing tests
  retain namespace, source preservation, escaping,
  thousands-of-links, statement anchors and repeated-card coverage.
- A checked-in Lean 4.30.0 reference fixture exercises actual compiler output,
  including aliases, same-spelling fields, private globals, local shadowing,
  generated/inductive constructors, Unicode and HTML-like identifier text.
  Registry tests cover corrupt metadata/headers, wrong source, stale cache,
  traversal paths, symlinks in tar headers, invalid redirects, ignored/wrong
  ranges, truncation and streamed oversize responses.

These checks establish the stated coverage and regression properties for the
current archive. Future compiler or capture format changes need explicit
support; an unknown format fails the build rather than emitting guessed links.
