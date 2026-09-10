# Let's stay in control of mathematics

AI is about to massively accelerate mathematical research. This will push the
classical system of peer review and publishing beyond its limits. We need new,
scalable mechanisms for digesting mathematics, or we risk losing control of
our own field.

Proof systems like Lean provide a scalable way of ensuring the
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

Lax takes care of guiding your agent through the whole process.

## Build foundations together

Concepts are shared across submissions. Nobody hands down the
definitions: whoever formalizes a paper first writes the ones it needs,
and later papers import them instead of fixing their own. A model of
computation, a width measure, a graph encoding: the definitions below are
the ones other submissions already build on, and every new submission adds
to them.

- Lax67.Ram
- Lax48.Treewidth
- Lax48.TwinWidth
- Lax12.NowhereDenseClasses
- Lax11.GraphEncoding
