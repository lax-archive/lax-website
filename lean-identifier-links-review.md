# Lean identifier navigation review

Reviewed and fixed on `codex/fix-lean-identifier-links`, based on website
commit `5e93143b` (including the three identifier-link commits).

## Findings and changes

The original build-time approach fits the static website and its CSP, but
the implementation had three problems:

1. Its archive cross-reference resolver knew concept and statement IDs,
   not the full names of ordinary definitions. The imported-name scan added
   short aliases but discarded namespace information. Thus
   `Lax17.Treewidth.treewidth` and `Lax17.GridMinor.ContainsGridMinor` were
   missed even though their defining modules were present.
2. A unique short spelling in the import closure does not establish what a
   Lean occurrence means. Local binders and open namespaces can change its
   meaning. Even dotted syntax can be local (`let N.value := …; N.value`).
3. Masking each link rebuilt the source repeatedly; restoring it scanned
   every replacement on every source line. It also changed the text Shiki
   highlighted. Imported source was reparsed for each dependent page.

The replacement separates a shared lexical inventory, destination lookup,
and rendering. Ordinary namespace and section commands determine the names
of declarations, independently of module filenames. Exact, unambiguous
qualified names are resolved within the current concept's import closure.
Definition destinations use existing `L<n>` source anchors; statements keep
their existing `s-…` anchors. Declaration sites and module names also link.
The reported references now target `Lax17.Treewidth.html#L67` and
`Lax17.GridMinor.html#L21`.

Unrestricted short-name aliases were deliberately removed. Potential local
shadows are suppressed conservatively across the file. Private globals are
not exported into the reference inventory. Names not verified by this
inventory remain plain; the implementation does not manufacture a link by
truncating a name until a module prefix matches.

The renderer decorates the original highlighted text, wrapping all coloured
fragments of an identifier in one anchor. It processes comment math through
the same range mechanism, so no placeholder strings or HTML substitutions
are needed. Paper cards use the same resolver and canonical concept-page
destinations, without adding source IDs to repeated cards. Hover and keyboard
focus underline links while retaining syntax colours.

## Scaling

Each build model owns a cached declaration inventory and resolved links;
there is no persistent cache to go stale between database builds. Only
candidate identifier tokens are retained after scanning. Import traversal
is iterative and cycle-safe. Repeated occurrences reuse their destination
lookup, including unresolved and ambiguous results. Rendering groups source
ranges by line and walks the highlighted fragments once, rather than doing
a line-count × reference-count replacement loop.

A warmed local Node comparison, using the same
source text and destination in both renderers, measured:

| References | Original renderer | Fixed renderer |
| ---: | ---: | ---: |
| 1,000 | 1,211 ms | 77 ms |
| 2,000 | 4,162 ms | 79 ms |
| 4,000 | 17,873 ms | 162 ms |

These are illustrative local measurements, not production latency promises.
Other site features still traverse dependency graphs; this change does not
claim to make the whole generator linear in archive size.

## Security and regression checks

- Link destinations come from archive pages, with encoded path and fragment
  components. The renderer accepts relative archive-page hrefs and escapes
  HTML; it rejects active schemes and external URLs. Source labels remain
  escaped text, including quoted Lean identifiers containing HTML syntax.
- The lexer skips nested comments, strings, raw strings, character literals,
  quoted names used as data, and parenthesized syntax quotations. Identifier
  boundaries include primes, `!`, `?`, subscripts and Lean's Unicode letters.
  UTF-16 offsets preserve astral characters and CRLF line numbering.
- The feature adds no dependencies, browser scripts, network lookups,
  compiler execution, or CSP relaxations. Syntax-highlighting failure still
  produces escaped text with safe links and comment math.
- Regression tests cover the reported references, namespace/section nesting,
  rooted and quoted names, private declarations, collisions, import cycles,
  local shadows, strings/comments/quotations, source preservation, malformed
  hrefs/ranges, repeated paper cards, and thousands of references.

Validation used read-only database commit
`66e58be2c0e10217a9959307d2a6d1a069e3394c`, with 402 concepts, 265 proofs and
all three cached PDFs/reflow bundles. Two complete builds produced identical
834-file trees. Across their 717 HTML pages, all 5,456 source links and
61,807 static local links resolved; there were no duplicate IDs, changed
CSP values, or displayed source-text differences from the original build.
Dynamic paper passage anchors were excluded from the static anchor check;
source-link destinations were all checked against actual emitted IDs.

`npm run check` passed 171 tests; its five normally skipped browser tests
were also run separately with system Chrome. The browser suite's resize wait
was made null-safe because reflow can temporarily detach a card while it is
being polled. Separate checks exercised the two reported links by keyboard
at desktop and mobile widths, under both root and branch-preview URLs, and
with JavaScript disabled. Concept navigation produced no CSP violations or
page errors. Native link clicks from both reflow and PDF paper cards reached
their canonical concept pages.

## Deliberate limits

This is a lexical navigation aid, not a substitute for Lean's elaborator.
It cannot guarantee semantic resolution for arbitrary Lean extensions and
scope rules. Bare references, generated structure fields/constructors,
notation, macros, `export` aliases and external Mathlib names need
compiler-produced reference metadata for complete coverage. That should be
an upstream archive-build feature; the website should consume validated
metadata rather than grow a second implementation of Lean name resolution.

The checks above establish specific regression and security properties;
they are not a guarantee that all possible Lean programs or browser states
are free of bugs.
