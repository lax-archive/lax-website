# Let's stay in control of mathematics

Mathematical research is about to be drastically accelerated. This will push
the classical system of peer review and publishing beyond its limits. We need new,
scalable mechanisms for digesting mathematics, or we risk losing control of
our field.

Proof assistants like Lean provide a scalable way of ensuring *correctness*.\
Lax builds on this foundation to make formal mathematics scalable for humans
too, by organizing results and making them easy to review and reuse.

## How it works

**Concepts and proofs.** Lax annotates natural-language mathematics with Lean.
Each definition or claim is tied to a *concept*: a pair formed by a
mathematical statement and a faithful Lean encoding. Each proof is tied to
Lean code that derives one concept from others. Concepts and proofs can be
reused across submissions.

## Proof network

**Proof network.** Explore how proofs compose and which claims are proven.
Any later submission can discharge an
[open obligation](open-proof-obligations.html), and every result that
rested on it is then proven.

## Get started right away

{{setup-tabs}}

Hand your coding agent a prompt like:

```
Run `lax print instructions` and follow the guide to formalize <my result>.
```

Then your agent takes over and guides you through the process.

## Community and Feedback

### Join the conversation

Lax is shaped by the people who use and review it. [Join the Lax
Discord](https://discord.gg/8GRt8GsxAd) to ask questions, exchange ideas, and
share feedback, or email us at
[lax.lean.archive@gmail.com](mailto:lax.lean.archive@gmail.com). You can also
meet the community at the [Lax Online Meeting](workshop/).

## Build foundations together

Concepts are shared across submissions. Below are some definitions other
submissions already build on.

- Lax67.Ram
- Lax48.TwinWidth
- Lax434930.NondeterministicPolynomialTime
- Lax132576.RationalFunctions
- Lax12.NowhereDenseClasses
- Lax11.GraphEncoding
