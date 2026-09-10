# About Lax

## Let's stay in control of mathematics

AI is about to massively accelerate mathematical research. This will push the
classical system of peer review and publishing beyond its limits. We need new,
scalable mechanisms for digesting mathematics, or we risk losing control of
our own field.

Publications serve (at least) two purposes:

- **Correctness**: establishing which things are true, via rigorous technical
  arguments.
- **Understanding**: explaining why these things are true, by providing
  intuition, clarity, and abstractions.

Proof systems like Lean provide a scalable way of ensuring the *correctness*
of mathematics. This frees humans to spend their finite attention where it
really matters: building intuition, clarity, and abstractions. Lax is a
community-run archive that annotates natural-language mathematics with Lean.
Think of it as an arXiv for formalization: independent, citable submissions
that people can read, software can check, and later work can build upon.

## What a submission is

A Lax submission is a commit in a public git repository. It holds

- **concepts**: small Lean files, one per mathematical definition or claim.
  A concept pairs a natural-language statement, as it would appear in a paper,
  with a faithful Lean encoding. Claims are stated as Lean `axiom`s, without
  proof. Concepts depend only on other concepts and on mathlib, and they are
  written in plain, tactic-free Lean that a reader without a proof-assistant
  background can follow;
- **proofs**: a separate Lean package that restates each claim as a `theorem`
  and proves it, using no axioms beyond Lean's own. Each proof records which
  concepts it rests on and which one it concludes;
- optionally a **paper**: a LaTeX document whose passages are annotated with
  the concepts and proofs they correspond to. The same source can go to arXiv
  and to Lax; the website renders it reflowed for the screen, beside the
  as-printed PDF, with the Lean beside each marked passage.

The concepts are the surface of the archive: they are what the website shows,
what readers review, and what later submissions import. The proofs are the
evidence behind that surface. They may be long, and are typically written by
AI agents; Lean's kernel certifies that they prove exactly the published
claim, and nothing else about them is judged.

Together, the proofs of a submission form its *proof network*: which claims
are proven outright, which are proven relative to others, and which
[proof obligations](open-proof-obligations.html) remain open. Any later
submission can discharge an open obligation, and every result that rested on
it is proven from that moment on. Stating a claim and proving it can thus be
separate contributions by separate people.

## Principles

**The paper stays the paper.** Mathematics is still written for people to
read. Lax does not ask for a different way of writing; it annotates what is
written, where it stands, with the Lean that pins its meaning down.

**Claims are separated from proofs.** Lean guarantees that a proof is
correct. What Lean cannot check is whether the formal statement says what the
mathematics means. Lax puts all human attention there: concepts are small
and legible, and every one of them can be discussed, endorsed, or flagged on
its page. Proofs are treated as opaque blobs, held to no standard but the
kernel's.

**Nobody hands down the definitions.** Concepts are shared across
submissions. Whoever formalizes a paper first writes the definitions it
needs; later papers import them instead of fixing their own, and common
standards emerge by selection rather than by decree. Lax is a bet that formal
mathematics can grow the way informal mathematics always has: as a literature
of independent papers that build on one another without a central authority.

**Submissions are immutable and citable.** As on arXiv, a registered
submission never changes. Every page carries a ready-made BibTeX entry, and a
revision is a new submission that supersedes the old one, which the website
points readers to. Because Lean submissions can only build on each other when
they share a mathlib version, Lax declares a *baseline* version of mathlib
that advances rarely; submissions on any version are archived, but only those
on the baseline can be built upon.

**Everything is open.** The command-line tool, the website generator, the
submission pipeline, the archive's metadata, every submission, and every
generated artifact are public and reusable under open licenses.

**Trust is earned, not asked for.** A claim marked as proven on the website
means our pipeline verified the proof. If you would rather not take our word
for it, the Lean code of every submission is public, and you can reproduce
the relevant part of the pipeline yourself: check that the project builds,
that the proof package uses no extra axioms, and that the type of each
`axiom` in the concepts matches the type of the corresponding `theorem` in
the proofs. The versions of Lean, Lake, and mathlib are part of the
submission's metadata. Run such checks in a sandbox: Lean code written by an
agent need not be safe, even when the submitter is someone you know.

## How Lax is built

Lax consists of three parts, all of them open source:

- the **command-line tool**, `lax`, published on npm. It creates the layout
  of a submission, builds and previews it, and submits it. Its built-in guide
  (`lax print instructions`) is written for coding agents, so that an agent
  can carry a formalization from the first concept to the finished proofs;
- the **submission pipeline**, which runs as a GitHub Actions workflow. A
  submission is a pointer to a commit in a public git repository; the pipeline
  fetches it, builds it, verifies the proofs against the concepts, and records
  the result in the archive's metadata repository;
- the **website**, a static site generated from that metadata and the built
  submissions, and served from GitHub Pages. Readers sign in with their ORCID
  iD to comment on and endorse concepts.

The archive's metadata, the submissions, and the generated artifacts are all
public: the website can be rebuilt by anyone, and so can any submission.

## Where to go next

- [An Introduction to Lax](lax-242665/paper.html), itself a Lax submission,
  walks through concepts, proofs, and papers on a running example.
- [Getting started](contributing.html) explains what happens at each step of
  a submission.
- The [FAQ](index.html#faq) answers the questions we are asked most.

## Who we are

Lax is a project by Édouard Bonnet (CNRS, ENS Lyon), Jan Dreier (TU Wien and
HPI Potsdam), and Clemens Kuske (TU Wien and HPI Potsdam). We are curious to know
what you think we should do next: submit your formalized results, review
concepts, and reach out with comments and suggestions.
