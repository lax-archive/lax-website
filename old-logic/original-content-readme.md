# Website texts

Static-page texts for the archive website, written 2026-07-26 as part of
the go-live UX pass.

- `landing.md` — **live**: wired into sitegen 2026-07-28
  (`src/sitegen/landing.ts` loads it, the index page renders it above the
  submissions library). It ships with the npm package, so editing it here
  changes the deployed site on the next release + regeneration. HTML
  comments are stripped before rendering — they hold sections not yet
  published (the Contributing link, the Background section). Rendering
  conventions: the page title is the generator's; the first paragraph
  becomes the centered lede under it; a list directly under a `##` heading
  renders as a card grid (the "What you can do here" actions), while lists
  after a paragraph stay plain.
- `contributing.md` — still a standalone draft, not yet wired in; that
  remains a TODO.md item. Internal links are written relative, as they
  will resolve once the page is generated into the site root.
