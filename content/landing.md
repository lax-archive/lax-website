# Lax: let's stay in control of mathematics

AI is about to massively accelerate mathematical research. This will push the
classical system of peer review and publishing beyond its limits. We need new,
scalable mechanisms for digesting mathematics, or we risk losing control of
our own field.

Publications serve (at least) two purposes:

- **Correctness**: establishing which things are true, via rigorous technical
  arguments.
- **Understanding**: explaining why these things are true, by providing
  intuition, clarity, and abstractions.

We believe proof systems like Lean provide a scalable way of ensuring the
*correctness* of mathematics. This frees humans to spend their finite
attention where it really matters: building intuition, clarity, and
abstractions. Lax is a community-run archive that annotates natural-language
mathematics with Lean theorems.

## Concepts

Natural-language mathematics is annotated with *concepts*: reusable blocks
that pair a mathematical idea with a faithful Lean encoding. Concepts are
reusable across submissions, so what the community has verified and endorsed
becomes the foundation the next result stands on.

By annotating intermediate lemmas with formalizations too, authors provide
trust not only in the correctness of the result, but also in the mechanism
leading to it.

## Proof network

The proof network between these concepts provides a high-level overview of
the ideas, as well as authority over which statements are proven, relative
to which other ones, and which
[proof obligations](open-proof-obligations.html) still remain.
