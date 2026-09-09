# Lax: let's stay in control of mathematics

AI is about to massively accelerate mathematical research. This will push the
classical system of peer review and publishing beyond its limits. We need new,
scalable mechanisms for digesting mathematics, or we risk losing control of
our own field.

We believe proof systems like Lean provide a scalable way of ensuring the
*correctness* of mathematics. This frees humans to spend their finite
attention where it really matters: building *intuition*, *clarity*, and
*abstractions*.

## How it works

**The paper stays the paper.** Lax annotates natural-language mathematics
with Lean. Each definition or claim, where it stands in the paper, is tied
to a *concept*: a reusable block that pairs a mathematical statement with a
faithful Lean encoding. Each proof is tied to Lean code that derives one
concept from others. Freely composable across papers.

## Proof network

**Nothing is taken on faith.** A submission's proof network shows every
claim it states, every proof it holds, and what each proof rests on: which
claims are proven outright, which are proven relative to others, and which
[proof obligations](open-proof-obligations.html) remain open. Any later
submission can discharge an open obligation, and every result that rested
on it is proven from that moment on.

## Get started right away

Set up, once per machine:

```
npm install -g lax-archive && lax doctor
```

Hand your coding agent a prompt like:

```
Run `lax print instructions` and follow the guide it prints
to formalize <my result>.
```

## Foundations

Concepts are shared across submissions. A paper that needs a model of
computation imports the archive's word RAM rather than fixing its own; a
bound on twin-width is stated against the archive's twin-width. The
definitions below are the ones later submissions already build on.

- Lax67.Ram
- Lax48.Treewidth
- Lax48.TwinWidth
- Lax12.NowhereDenseClasses
- Lax11.GraphEncoding
