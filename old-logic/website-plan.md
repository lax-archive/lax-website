Status: implemented 2026-07-27 (sitegen + assets + tests; see TODO.md's
"Website: claim pages" entry for the summary of what landed). Rounds below
record each follow-up pass, newest last.

Round 7 (2026-07-28): the way out to the Lean proofs. The site shows no
proof code by design, which left the link to it as an afterthought in the
proof page's microline. It is now the page's main remaining action — a
bordered button with the GitHub mark, under the judgment card, deep-linking
the proof's own `.lean` file — and the two surfaces that list proofs
without showing them carry the package link beside them: a footer row under
the submission page's proof list and an inline link on the **Proof network**
figure title, both pointing at `proofs/` (a *tree* link; `githubSource`'s
`path` argument means a file, so the directory goes in as the folder).
`sourceLink`/`sourceButton`/`proofsSource` in `pages/shared.ts` are the one
place that grammar lives; `.source-link` lost its `.section-heading` scope
so figure titles can use it too.

Round 6 (2026-07-28): map defaults and the submission map.
- concept-map defaults are now the same on both page kinds: ancestors
  shown, descendants hidden. Only the submission page changed (it hid
  both); the concept page already did this. Both closures always ran over
  the whole archive — `upstreamClosure`/`downstreamClosure` walk
  `conceptHome`/`importers`, which span every submission — and a test now
  pins that.
- the submission page gained a **Submission map** (`src/sitegen/graphs.ts`,
  `submissionGraph`): the same figure one level up, showing what this
  submission transitively builds on and what transitively builds on it,
  over the whole archive. No toggles — both directions are always drawn.
  A submission with neither gets a sentence instead of an empty figure.
- the relation (`SiteModel.submissionUses`/`submissionUsedBy`) is the union
  of two sources: every cross-submission reference the content makes (a
  concept importing a foreign concept, a proof naming a foreign statement)
  and the packages the two lakefiles require (`requiredByConcepts` /
  `requiredByProofs`, `<id>Proofs` mapped back to `<id>`, `mathlib`
  dropped). A reference cannot exist without its require, but a require can
  be declared without a reference, so the requires complete the list and
  the references are the visible reason for most of it.
- `dag.js` grew one `drawDag` that both layered figures call — same
  Sugiyama layout, ports, routing, and hover-lit edges. It assumes an
  acyclic input, which both relations are: concept imports are Lean
  imports, and the archive admits a dependency only on a submission that
  already exists. The proof network keeps its own SCC-condensing renderer,
  since the proof hypergraph is the one that *can* cycle.
- the demo archive violated that invariant (Lax8's proof concluded a Lax9
  claim while Lax9's proof assumed a Lax8 claim — mutually impossible under
  registration order). The foreign grounding proof moved to a new later
  submission Lax11, keeping both showcase features and making the demo's
  submission graph a four-deep chain.

Round 5 (2026-07-27):
- one cycle notion in the proof network: the grounded/ungrounded split is
  gone (nodes inside a cycle already carry their own proven/open fills);
  every SCC enclosure is the neutral box labeled "cycle", the warn-palette
  dashed variant and its legend entry are deleted.
- both concept maps carry two all-or-nothing toggles: "Show/Hide
  ancestors" (id `concept-expand`, the full upstream closure) and
  "Show/Hide descendants" (id `concept-descend`, the full downstream
  closure). The always-visible core is exactly the page's roots; the old
  in-between direct-context level is gone. Defaults: ancestors shown on
  concept pages, everything hidden on submission pages. Descendants'
  unrelated imports stay out of view. The concept page's ext legend label
  became direction-neutral ("Related concept").

Round 4 (2026-07-27): sidebar badges/proofs, hide reserved-only records,
proof-network height, the demo archive, compiled references, prefix
pruning everywhere, index-sidebar grammar:
- sidebar concept entries carry the same status badges as the concept
  list (✓/× marks, green/yellow tints), and a "Proofs" group follows
  under a "Concepts" heading — ⊢-chip rows, prefix-pruned names, its own
  "proof" option in the type filter; group headings hide with their
  group when filtered (sidebar.js).
- reserved-only records (no build output) are gone from the landing
  library, the stats line, and the index sidebar; their pages stay
  reachable by direct link.
- proof-network rows compacted (rowGap 48→26) so one claim→⊢→claim step
  roughly matches the concept map's 76px layer rhythm.
- references compile via src/sitegen/bibtex.ts (authors, italic title,
  venue vol(no):pages, year, doi/arXiv/url links; TeX accents and
  ligatures de-TeX'd); unparseable entries fall back to raw source.
- the concept map's own-prefix pruning now applies across pages:
  submission concept list, judgment cards (claims), deps columns, and
  proof-id sublines (spec-mandated `<id>Proofs.` prefix); full ids stay
  in tooltips and hrefs.
- `npm run site:demo` (scripts/demo-site.ts) serves a synthetic archive
  exercising the full spectrum: grounded AC↔Zorn↔well-ordering cycle
  (grounded by a foreign Lax8 proof), an ungrounded continuum cycle,
  multi-assumption and conditional proofs, foreign strokes, a draft,
  a hidden reserved-only record, and compiled references.
- the index sidebar drops its one-off bordered submission cards for the
  flat entry grammar every other sidebar uses: id as the leading chip
  (mono, dimmed), ellipsized title, draft badge after.


----------------------------

Follow-up, same day — visual-language consistency pass (to be evaluated
by eye): one color grammar across lists, badges, and both graph figures
(fill = proven status green/yellow/neutral, stroke = origin accent/gray;
warn palette for ungrounded cycles — dropped again in round 5); ⊢ boxed
as a proof badge
chip parallel to the type badge; type badges with a ✓/× mark tinted by
status; identifiers set in the text face everywhere outside true code
surfaces; network statement nodes labeled by their home concept; hover +
HTML tooltips on all graph nodes in both figures; stray colors and radii
promoted to :root tokens. The grammar is documented in the header
comment of assets/site/style.css.

Round 2, after review by eye: graph node labels join the lists' text
face and link color (mono is code-surfaces only now); badges drop the
saturated fills for light tints, and the badge legend shrinks below the
list it explains; proof-list items lead with the judgment card (whole
surface links to the proof page via an overlay, claim links stay live),
the id becomes a dimmed subline, the description leaves the list; the
proof list shares the concept list's white box. The "untyped" state is
gone entirely: concept `type` is required (Inspect violation + sitegen
fail-fast, spec-notes.md entry of 2026-07-27).

Round 3: figure titles extracted from the graph chrome into the text
flow (h4.figure-title, styled like block headings; the proof network's
toolbar dissolved, its reading hint now leads the legend), and inline
code in annotation prose resized to sit proportionally inside Latin
Modern lines (0.78em, line-height 1).

## submission view

0. frontmatter and abstract, as exists already

1. the list of new concepts. Concepts via the multi-column layout that already exists. feel free to polish it (e.g. make it adaptive if it isnt already)

2. the list of new proofs. they are showed as a list of assumptions column with a conclusion after. e.g.

---------------
|assumption 1 |
|assumption 2 | --> conclusion
|assumption 3 |
---------------
---------------
|assumption 1 |
|assumption 2 | --> conclusion
|assumption 3 |
---------------
---------------
|assumption 1 |
|assumption 2 | --> conclusion
|assumption 3 |
---------------
very light box on the left. visually appealing. the assumptions and conclusions should have the same visual style as the list of concepts above. via the 1-axiom rule, they are actually concepts (and not axioms as before)

3. then the dependency view. give it a more catchy name please!

4. then the derivation view. also a better suited name here!

rethink names from first principles and documentation.


## concept view

1. dependency view. also with better naming of all expansion options and legend.

2. proof view. here all proofs with the current concept as root pop up. giving a full overview if the thing is true relative to what. 

then description and lean as usual

## proof view

each proof entry should become its own page, linked to when clicking on a proof. i have no clear idea what this page should look like, so follow your instincts here.


--------------------

last, in tihs section (example below), the naming convention for imports imported etc should be polished:


Imported

    Lax11.GraphEncoding
    Lax11.RamComputes

Imported by

none
Mathlib imports

    Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
    Mathlib.Data.Nat.Lattice


generally, naming legends and everything should be rethought from first principles and spec whereever you encouter something you think is worth improving.

you are free to implement things yourself or to delegate to subworkers. as you seem fit.
