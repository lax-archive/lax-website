# Lax Website

This repository is the complete, standalone source for the Lax Lean Archive
website. It owns:

- editorial Markdown in `content/`;
- HTML rendering and page templates in `src/sitegen/`;
- browser JavaScript, CSS, vendored Latin Modern fonts, and the vendored
  pdf.js build behind the paper viewer (`assets/site/pdfjs/`, refreshed
  from the pinned `pdfjs-dist` dev dependency by `npm run pdfjs:vendor`) in
  `assets/site/`;
- the command-line build and local preview server;
- tests for rendering, links, graphs, math, source display, and security;
- continuous integration and GitHub Pages deployment workflows.

Archive submissions are data, not website source. The generator reads the
public [`lax-archive/lax-database`](https://github.com/lax-archive/lax-database)
repository and never modifies it.

A manifest with `unlisted: true` keeps its submission, concept, proof, and
paper pages available by direct URL, but omits the record from archive-wide
browse, search, topic, review, comment-activity, proof-obligation, and
machine-readable index surfaces. Those direct pages also ask search engines
not to index them. A manifest with `anonymous: true` remains discoverable but
withholds authorship, citation, and source-repository details.

## Requirements

- Node.js 20 or newer
- npm
- a local checkout of `lax-archive/lax-database`
- for archive graph measurement: pinned Chrome for Testing `150.0.7871.124`,
  or a complete exact-metrics cache. Set `GRAPH_CHROME` to that executable.
  CI provisions it; installing the packaged local renderer does not.

## Local setup

```sh
npm ci
git clone https://github.com/lax-archive/lax-database.git data/lax-db
npm run check
```

Build the complete static website into `_site/`:

```sh
npm run papers:fetch   # once per database change; see "Papers" below
npm run references:fetch
npm run site:build
```

Quick local builds can skip the papers and compiler reference cache:

```sh
npm run site:build -- --no-papers --no-references
```

Preview it locally and rebuild when database, content, or assets change:

```sh
npm run site:serve
```

The preview is available at <http://localhost:3000/>. Override defaults when
needed:

```sh
npm run site:serve -- --database /path/to/lax-db --out /tmp/lax-site --port 8080
```

Submission, concept, and proof source links target immutable commits on
GitHub, GitLab.com, Codeberg, or Bitbucket Cloud according to the repository
host stored in the Archive database.

## Papers

A submission may carry a LaTeX paper that the archive compiled itself. Its
record names the PDF by digest (`paper.pdf.registryBlob`, a blob of the
submission's capture in the public `ghcr.io` registry); the bytes are not
in `lax-database`. `npm run papers:fetch` downloads every referenced PDF the
local cache lacks into `data/papers/<digest>.pdf` (anonymously, verified
against the digest), and `site:build` then emits `<id>/paper.pdf` beside
`<id>/paper.html` — the page that shows the PDF with a card for every
passage the author marked (a concept, a proof, or a submission), placed
beside the passage by `assets/site/manuscript.js`: each passage is one
flat region per column (the geometry in `manuscript-place.js`) over a
lighter shadow a fixed margin wider than the passage, and a band from that
shadow's edge across the gutter to its card, split-diff style; a card opens
while hovered and stays open when clicked; a concept card carries the
concept's Lean source with the module docstring elided. The page opens
with the sidebar collapsed for the room. `--papers DIR` moves the cache; a
production build refuses to run with a paper missing from it, and
`--no-papers` builds the page without the viewer instead, for quick local
builds.

A record may additionally carry a derived reflowable rendering of the same
paper (`paper.web`, a ReflowTeX bundle sealed by the archive — see
`paper-web-plan.md` in the `lax` repository). `npm run papers:fetch` also
downloads those bundles into `data/bundles/<digest>.tar` (`--bundles DIR`
moves the cache), and `site:build` then renders `paper.html` as the reflowed
paper — re-typeset as SVG at the reader's width by the vendored viewer
(`assets/site/reflowtex/`, AGPL, the source served unminified), the marked
passages exposed as `#m<n>` anchors the cards attach to
(`assets/site/manuscript-reflow.js`) — while the paper as printed keeps
its own address, `<id>/paper-pdf.html`, emitted beside every cached PDF
whether or not a reflow page stands in front of it. Every link into a
paper (the submission page's button, the "In the paper" lists) targets
`paper.html`: the reflowed text where there is one, the printed paper
otherwise; a page with both surfaces links the other from a switch above
the paper, carrying the `#m<n>` fragment across. On a screen narrower than
the site's mobile breakpoint the reflowed paper drops to one column: no
rail, and a tap on a passage opens its card in the text right under the
passage (the viewer's lax fork keeps a slot after the segment holding a
mark), closed again by its ×, its head, or the passage. The build
content-hashes every served font under the site root's `fonts/`, embeds
the protobuf blocks inline up to a ~2 MiB budget (past it they are emitted
as `<id>/paper-web/*.pb` files the viewer fetches same-origin), and gates
every bundle's recorded schema against the viewer's supported set
(`assets/site/reflowtex/supported-schemas.json`) — a mismatch drops that
page to the printed surface with a build warning, never a broken reflow
page. `--no-papers` suppresses bundles along with PDFs — one flag — so
preview builds keep today's card-list page (a preview's `paper.html`
bytes therefore differ from production's, deterministically per flag set).

## Content

- `content/landing.md` supplies the landing-page introduction.
- `content/contributing.md` generates `/contributing.html`.
- `content/about.md` generates `/about.html`, linked from the header.
  Its `{{concept-proof-flip}}` marker inserts the concept/proof flip card
  from `src/sitegen/pages/proof-flip.ts`, with hover, touch and keyboard controls.
- `content/workshop.md` generates `/workshop/` and embeds the workshop
  preregistration form.
- Submission, concept, and proof pages come from `record.json` and
  `build-output.json` in `lax-db`.
- Submission/concept titles and annotation headings accept inline Markdown and
  TeX. Abstracts, concept/proof descriptions, and annotation sections accept
  the full Markdown grammar. KaTeX-compatible TeX can use `\(...\)` or `$...$`
  inline and `\[...\]` or `$$...$$` for display math.
- In the line-numbered Lean source, `$...$` and `$$...$$` inside comments are
  rendered as inline and display math; dollar text in Lean code and strings is
  left unchanged.
- Lean source links, on concept pages and paper cards, use Lean's resolved
  references from the submission's sealed `.ilean` files. This covers archive
  declarations, structure keys and projections, aliases, private globals and
  constructors, with type and scope information from the validated build.
  Mathlib constants and Lean core/standard-library types such as `Nat` link
  to their exact declarations in the public Mathlib documentation, including
  `abbrev` declarations. Uses of archive abbreviations link to their source
  declarations. The compressed, checksummed index in `assets/mathlib-docs/`
  is a fixed build input, loaded once and never sent to browsers; its refresh
  procedure is documented there. The documentation describes the current
  version, which may differ from the submission's Mathlib pin. Links use
  the compact hover label “mathlib ↗” or “lean ↗”.
  For declarations absent from the index, `references:fetch` verifies the
  defining module at the submission's full Mathlib commit and caches whether
  it exists; a verified module gets a pinned GitHub source link. Missing
  modules remain plain. Local variables, other external libraries, and names
  at their own definition sites stay plain. Imported archive module names link
  to their concept pages; Mathlib import names in the Lean source link to their
  module documentation. Archive namespaces in `open` commands link to their
  owning concept or declaration; standalone submission namespaces such as
  `Lax17` link to the submission page, as do displayed `lax-17` metadata labels
  on other pages. The ID beneath a submission's own title stays plain.
  Namespace navigation uses known, unambiguous destinations within the
  module's archive imports. External `open scoped` names link to their
  documented declaration when one exists (for example `SimpleGraph` or
  `ENNReal`); `BigOperators` and `Classical` link to their defining documentation
  modules. Archive namespace destinations take precedence, and unknown scopes
  stay plain. Declaration uses link to the
  beginning of the declaration's preceding comments (or its attributes and
  modifiers when there are no comments); statements retain their `s-…` anchors
  at the same comment start. Source targets align below the sticky header, with
  enough scroll space for short pages. Hover and keyboard focus use bold
  text. Generated helpers without their own source span link to the nearest
  enclosing declaration, or the module if no enclosing span exists.
- `npm run references:fetch` fills the references cache from the existing
  public captures, one way per record shape. A spec-1 record lists its
  capture's files, so the cache gets `data/references/<sha256>.ilean` per
  module: bounded HTTP ranges of the capture tar, each tar header and member
  digest checked, the displayed source verified against the capture
  manifest. A spec-2 record (see "Two content specs" below) lists no files
  but names a `references` layer beside its capture — the concept sources
  and their `.ilean` files as one small tar — which is downloaded whole,
  verified by its digest and size, and cached as
  `data/references/<digest>.references.tar`; its source members must be
  byte-equal to the displayed source. Neither path extracts tar paths to
  disk or compiles submissions. The command also checks any needed Mathlib
  source fallbacks, storing the results under
  `data/references/mathlib-sources/`. Builds reverify cached bytes and
  validate Lean's version-5 JSON and UTF-16 ranges. Missing, stale or
  unsupported metadata fails a normal archive build
  with an explanatory error. `--references DIR` moves the cache. Both CI and
  branch deployments fetch it before building.
- Local `lax` callers without sealed captures, and explicit `--no-references`
  builds, retain conservative lexical navigation. That fallback does not
  promise complete coverage: fields, aliases and potentially shadowed names
  need compiler metadata. Normal archive and preview builds use the metadata.
- Archive source links are static relative URLs; Mathlib links are restricted
  to the public Lean/Mathlib documentation and pinned `leanprover-community/mathlib4`
  source paths. They preserve syntax colours, source text and line anchors,
  work in branch previews, and
  require no browser scripts, external requests or CSP changes. Each build
  scans each concept once for its declaration inventory and caches resolved
  links; rendering walks highlighted fragments without repeated whole-source
  replacements or scanning every reference on every line.
- Records whose state is still `init` are id reservations, not submissions;
  website builds ignore them completely.
- Manifests with `anonymous: true` keep their mathematical content visible,
  but presentation surfaces replace author identities, source-repository
  links, endorser identities, citations, and references with explicit
  anonymous-review notices.
- A record with a `paper` block additionally gets `<id>/paper.html` (and
  `paper.pdf` when the papers cache holds it); concept and proof pages the
  paper marks link back to their passages.

## Environments and the epoch

A record is built in one *environment* — a Lean toolchain and the mathlib
release it pins, named by the Lean version string (`v4.33.0`) that the
record's `manifest.leanVersion` carries. One of them is the archive's
*epoch*, the environment this year's submissions are recommended to use;
only submissions in the same environment can cite each other. The site's copy
of the epoch is `EPOCH` in `src/config.ts`, edited once a year at the epoch
bump; `generateSite(submissions, outDir, epoch)` takes an override as its
third argument (an epoch id, or an options object carrying `epoch`), which is
how `lax serve` shows the epoch the installed CLI's own environment table
names rather than the pinned renderer's.

Three surfaces follow from it:

- **The off-epoch notice**, beside the draft banner on submission, concept,
  proof, and paper pages of any record outside the epoch: the environment, the
  epoch, and the one consequence — only submissions in that environment can
  cite the work. It uses the draft banner's box in a muted palette and no
  warning mark, because the record is neither wrong nor at risk. Records in
  the epoch get an `epoch` label beside the masthead's `Lean` pin instead.
- **The environment facet**, `data-env` on every listing row and the
  environment folded into the row's `data-tags`, so environments are chips in
  the existing topic strip rather than a second control. The chips appear only
  once the archive holds work in more than one environment. Listings put the
  epoch's submissions first and the other environments newest first, inside
  the existing registered/work-in-progress groups.
- **`index.json` and `environments.json`** at the site root: every rendered
  record with its state, environment, title, `supersedes`/`supersededBy`,
  concepts (id, title, type) and proof ids; and the epoch with each
  environment's content spec (`specVersion`, see below) and a registered
  and draft count. They exist so an agent need not clone
  `lax-database` or scrape the HTML, and `content/contributing.md` links
  both. Like every other output they are deterministic.

## Two content specs

An environment also fixes what a statement and a proof *are* — its
**content spec** — and a record repeats it as `manifest.specVersion`. Spec 1
is the archive as it launched: statements are Lean `axiom`s, proofs are
checked by the archive's pipeline. Spec 2 (environments from `v4.35.0`;
`axiomfree-plan.md` in the `lax` repository) states claims as tagged `Prop`
definitions, records each proof as a **telescope** — its hypotheses in
binder order and its conclusion — and certifies every edge of a record's
proof network with Lean's own `lake comparator`, whose verdict the record
carries as a `certificate`. The loader (`src/database.ts`) reads both record
shapes into one in-memory model, keyed on that spec: a spec-2 record stores
no field a reader derives, so the loader fills the manifest's id from the
record's, derives each proof's `conclusion` and sorted `assumptions` from its
telescope, and reads the paper's `folder`/`main`/`engine` from the manifest.
The site model, the proof network and every page then run unchanged on both.

What a spec-2 record shows beyond a spec-1 one:

- **the telescope on proof cards** — hypotheses in binder order, named
  `h₁ … hₙ` as the record's Challenge names them, each linked to its exact
  statement, non-default binders labelled — in place of the derived
  assumption list;
- **the certified mark**, "certified: `lake comparator` (toolchain, kernels)",
  with the bundle digest and the rerun command (`lax certify <record>
  --run`, or `lake comparator --config comparator.json` in the fetched
  bundle): a chip on each proof card, a line under the judgment on the
  proof page and under the proof network on the record page. A spec-2
  record without proofs ran nothing and shows no mark. The grounded or
  conditional status the site composes from several edges is shown as
  before and labelled as composed by the site, never as certified;
- **the Challenge**, `Challenge.lean` verbatim as a collapsed Lean code
  block under the proof network, beside the bundle digest and the digests
  of the Challenge and Solution exports the judge compared (the solution
  digest is shown when the record carries it) — it is what makes the mark
  checkable by a reader;
- **the trust note**, one sentence on the record page naming the
  environment: the edges are certified by Lean's comparator; the concept
  packages a record depends on are trusted for their meaning, as in every
  environment; certificates are rerunnable.

A statement's raw `body` (the inspector's core-notation rendering) is carried
in the model but not shown: the author's source, with its notation, remains
the displayed form of every statement.

The spec version of an environment comes from its records' manifests. For an
environment the archive holds no work in — the epoch listed at zero right
after a bump — `environments.json` takes it from `generateSite`'s
`environmentSpecVersions` option (how `lax serve` can pass its own table),
then from `ENVIRONMENT_SPEC_VERSIONS` in `src/config.ts`, edited at each
admission that changes the spec.

`lax serve` keeps its own copy of this loader (`src/cli/website.ts` in the
`lax` repository) and today withholds a spec-2 capture's `registryBlob`
from the renderer, because the renderer before this one addressed the
capture tar by its file list and refused a capture without one. This
renderer never reads that address for a spec-2 record — it reads the
`references` layer's — so the lax copy may stop withholding it once lax is
re-pinned to this renderer; the two copies are to be unified after the
spec-1 port.

The generated HTML is deterministic. Math is rendered at build time with
KaTeX, highlighting with Shiki, all runtime assets are local, and the page
shell applies a strict Content Security Policy.

## Graph drawing

Archive builds prepare concept, submission and proof graphs before writing
pages. A first-party core assigns ranks and semantic ports, orders layers,
places measured boxes, and searches bounded routing candidates. An independent
validator checks complete quantized geometry and serialized curves. Public
pages contain linked, accessible SVGs that work without JavaScript. The browser
adds inspectors, highlighting, pan/zoom, fullscreen and prepared view switches;
it downloads no graph-layout engine and performs no layout search.

The archive measurement host uses the site's bundled fonts and exact SVG ink
bounds, including wrapped lines. Obtain the pinned executable from
[Chrome for Testing](https://googlechromelabs.github.io/chrome-for-testing/)
and point `GRAPH_CHROME` at it. An unexpected browser version, unsupported
glyph, lost edge, invalid attachment or geometry collision stops an archive
build. The previous output is retained while preparation and staged writes run.

```sh
GRAPH_CHROME=/path/to/chrome npm run site:build
GRAPH_CHROME=/path/to/chrome npm run check
```

The default `.lax-graph-cache/` stores exact label metrics, content-addressed
geometry and separate algorithm diagnostics. Cache keys include font and style
signatures, semantic port constraints, the display projection, engine version
and selection profile. Corrupt entries are rebuilt. Cache hits and misses
produce the same published bytes; elapsed times and host information appear
only in an optional build report:

```sh
npm run site:build -- --graph-cache /tmp/lax-graphs \
  --graph-report /tmp/lax-graph-build.json
```

Concept ancestry and descendant controls select at most four precomputed
states. Larger alternate SVG payloads are same-origin static files, loaded
only when selected. `--self-contained-graphs` embeds every supported state for
`file:` exports. These exports still use the site's accompanying local assets.

`npm run site:serve` and packaged `generateSite()` callers default to local
mode. If exact cached metrics are unavailable, a separately packaged helper
measures new labels in the user's browser and runs the same core in a worker.
This path requires the local HTTP preview; it does not install a browser,
fetch a layout library, or appear in archive assets. Hosts can explicitly use
`{ graphs: { mode: "archive", measurement: { provider, providerId } } }` to
supply their own exact measurement service. An epoch string remains supported
as `generateSite()`'s third argument for existing `lax serve` callers.

Algorithm methods, fixture provenance, supported work budgets and comparison
commands are in [docs/graph-layout](docs/graph-layout/README.md). The frozen
archive corpus is separate from synthetic diagnostic graphs. Optional Graphviz
and ELK comparison scripts are development tools; neither is a dependency of
the normal build or visitors' assets.

Test-created temporary sites are removed after each suite. Set
`LAX_KEEP_TEST_OUTPUT=1` when deliberately keeping them for debugging.

Historical website-only plans and migration notes from the original monorepo
are preserved under `old-logic/`. They are archival and are never rendered or
deployed.

## Automation and triggers

`.github/workflows/ci.yml` verifies pull requests and pushes, builds against
the real public archive database (fetching papers, reflow bundles and compiler
references through local caches), and uploads the rendered site as an artifact.

`.github/workflows/deploy-pages.yml` builds and deploys GitHub Pages when:

- any branch changes;
- a maintainer starts it manually;
- another system sends the `lax-db-updated` repository dispatch event;
- the hourly fallback notices database changes after a missed dispatch.

The default branch is published at the Pages root. Every other branch is
published independently below `/previews/<branch-slug>/`, with the papers'
PDFs like production, and the shareable preview directory is available at
`/previews/`. Pushing a branch updates only
its preview; deleting the branch removes it. The workflow retains the complete
published tree on the generated `gh-pages` branch so one branch cannot overwrite
another branch's preview. Every deployment (including the hourly fallback)
reconciles previews with live source branches, expires previews after 14 days,
and retains at most the five most recently updated previews. A new push
recreates an expired preview. Cleanup removes only published preview files;
it does not delete source branches, production content, or renderer archives.
A failed or empty remote branch listing stops cleanup rather than deleting
previews from an incomplete snapshot.

To trigger an immediate rebuild from an authorized external workflow:

```sh
gh api --method POST repos/lax-archive/lax-website/dispatches \
  -f event_type=lax-db-updated
```

The scheduled build makes deployment correct even before the archive server
or database mirror sends that event.

### When a rebuild goes wrong

One malformed record must not stall every later rebuild. The loader and the
generator treat each record as its own boundary: a record whose files do not
parse, or whose pages cannot be rendered, is left out with its reason named,
and the site is built from the rest. `site:build --build-report FILE` writes
the list of skipped records; the deploy workflow turns it into run
annotations and, for production, an issue titled "Website build skipped
records" (`.github/scripts/rebuild-alert.mjs`). A production rebuild that
fails outright opens "Website rebuild failed" the same way. Either title is
opened once and stays the alarm until a maintainer closes it, however often
the hourly schedule fires; a later failure opens a new issue only while none
with that title is open.

The build also writes `404.html` (served by Pages for any missing address —
a deleted record has no page and lands there), `robots.txt` (crawl
everything except `/previews/`, which would otherwise be indexed as a
duplicate of the site per retained branch), and `sitemap.xml` (every page of
every listed record).

## Deployment boundary

The workflow deploys to GitHub Pages. Pointing `laxarchive.org` at that
deployment is a separate DNS decision; this repository deliberately does
not change the live domain or the archive API endpoint.

## Provenance

The initial renderer, assets, tests, and content were extracted from
`lax-archive/lax` at tag `v0.1.17` (`edcb3bb`) so website work can evolve
independently from the CLI and archive server.
