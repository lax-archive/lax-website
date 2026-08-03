# Lax Website

This repository is the complete, standalone source for the Lax Lean Archive
website. It owns:

- editorial Markdown in `content/`;
- HTML rendering and page templates in `src/sitegen/`;
- browser JavaScript, CSS, and vendored Latin Modern fonts in `assets/site/`;
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
npm run site:build
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

## Content

- `content/landing.md` supplies the landing-page introduction.
- `content/contributing.md` generates `/contributing.html`.
- Submission, concept, and proof pages come from `record.json` and
  `build-output.json` in `lax-db`.
- Records whose state is still `init` are id reservations, not submissions;
  website builds ignore them completely.

The generated HTML is deterministic. Math is rendered at build time with
KaTeX, highlighting with Shiki, all runtime assets are local, and the page
shell applies a strict Content Security Policy.

Historical website-only plans and migration notes from the original monorepo
are preserved under `old-logic/`. They are archival and are never rendered or
deployed.

## Automation and triggers

`.github/workflows/ci.yml` verifies pull requests and pushes, builds against
the real public archive database, and uploads the rendered site as an
artifact.

`.github/workflows/deploy-pages.yml` builds and deploys GitHub Pages when:

- any branch changes;
- a maintainer starts it manually;
- another system sends the `lax-db-updated` repository dispatch event;
- the hourly fallback notices database changes after a missed dispatch.

The default branch is published at the Pages root. Every other branch is
published independently below `/previews/<branch-slug>/`, and the shareable
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
