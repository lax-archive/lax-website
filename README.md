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

## Requirements

- Node.js 20 or newer
- npm
- a local checkout of `lax-archive/lax-database`

## Local setup

```sh
npm ci
git clone https://github.com/lax-archive/lax-database.git data/lax-db
npm run check
```

Build the complete static website into `_site/`:

```sh
npm run papers:fetch   # once per database change; see "Papers" below
npm run site:build
```

Previews and quick local builds can skip the papers entirely:

```sh
npm run site:build -- --no-papers
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

## Papers

A submission may carry a LaTeX paper that the archive compiled itself. Its
record names the PDF by digest (`paper.pdf.registryBlob`, a blob of the
submission's capture in the public `ghcr.io` registry); the bytes are not
in `lax-database`. `npm run papers:fetch` downloads every referenced PDF the
local cache lacks into `data/papers/<digest>.pdf` (anonymously, verified
against the digest), and `site:build` then emits `<id>/paper.pdf` beside
`<id>/paper.html` — the page that shows the PDF with a card for every
passage the author marked (a concept, a proof, or a submission), placed
beside the passage by `assets/site/manuscript.js`. `--papers DIR` moves the
cache; a production build refuses to run with a paper missing from it, and
`--no-papers` builds the page without the viewer instead, which is what
branch previews do.

## Content

- `content/landing.md` supplies the landing-page introduction.
- `content/contributing.md` generates `/contributing.html`.
- Submission, concept, and proof pages come from `record.json` and
  `build-output.json` in `lax-db`.
- Submission/concept titles and annotation headings accept inline Markdown and
  TeX. Abstracts, concept/proof descriptions, and annotation sections accept
  the full Markdown grammar. KaTeX-compatible TeX can use `\(...\)` or `$...$`
  inline and `\[...\]` or `$$...$$` for display math.
- In the line-numbered Lean source, `$...$` and `$$...$$` inside comments are
  rendered as inline and display math; dollar text in Lean code and strings is
  left unchanged.
- Records whose state is still `init` are id reservations, not submissions;
  website builds ignore them completely.
- A record with a `paper` block additionally gets `<id>/paper.html` (and
  `paper.pdf` when the papers cache holds it); concept and proof pages the
  paper marks link back to their passages.

The generated HTML is deterministic. Math is rendered at build time with
KaTeX, highlighting with Shiki, all runtime assets are local, and the page
shell applies a strict Content Security Policy.

Historical website-only plans and migration notes from the original monorepo
are preserved under `old-logic/`. They are archival and are never rendered or
deployed.

## Automation and triggers

`.github/workflows/ci.yml` verifies pull requests and pushes, builds against
the real public archive database (fetching the compiled papers through a
cached `data/papers/`), and uploads the rendered site as an artifact.

`.github/workflows/deploy-pages.yml` builds and deploys GitHub Pages when:

- any branch changes;
- a maintainer starts it manually;
- another system sends the `lax-db-updated` repository dispatch event;
- the hourly fallback notices database changes after a missed dispatch.

The default branch is published at the Pages root, with the papers' PDFs.
Every other branch is published independently below
`/previews/<branch-slug>/` without them (`--no-papers`), and the shareable
preview directory is available at `/previews/`. Pushing a branch updates only
its preview; deleting the branch removes it. The workflow retains the complete
published tree on the generated `gh-pages` branch so one branch cannot overwrite
another branch's preview.

To trigger an immediate rebuild from an authorized external workflow:

```sh
gh api --method POST repos/lax-archive/lax-website/dispatches \
  -f event_type=lax-db-updated
```

The scheduled build makes deployment correct even before the archive server
or database mirror sends that event.

## Deployment boundary

The workflow deploys to GitHub Pages. Pointing `laxarchive.org` at that
deployment is a separate DNS decision; this repository deliberately does
not change the live domain or the archive API endpoint.

## Provenance

The initial renderer, assets, tests, and content were extracted from
`lax-archive/lax` at tag `v0.1.17` (`edcb3bb`) so website work can evolve
independently from the CLI and archive server.
