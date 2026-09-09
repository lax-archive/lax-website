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
with Lean: each definition or lemma, where it stands, is tied to a *concept*,
a reusable block that pairs a mathematical idea with a faithful Lean
encoding. Concepts can be shared and built upon across submissions.

## Proofs

**Proofs compose.** A proof derives one concept from others, and Lax records
exactly what it rests on. Annotating the lemmas along the way gives trust
not only in the theorem but in every step leading there.

## Proof network

**Nothing is taken on faith.** The proof network gives a high-level overview
of the ideas, and says which statements are proven relative to which others,
and which [proof obligations](open-proof-obligations.html) still remain.
Any later submission can discharge an open obligation, and every result that
rested on it is proven from that moment on.

## What it is for

### While you write

Write the paper as you always have. Pin the definitions and lemmas that
matter to Lean statements, and let an agent grind out the proofs while you
keep writing. You decide what the statements mean; the machine decides
whether the proofs go through. When a formalization attempt fails, that is
usually where the gap in your own argument is, and you find it before a
referee does.

### Peer review

Referees spend most of their time checking whether the details work, and
almost none on whether the ideas are good. A Lax-annotated submission moves
the first part to the machine: a referee sees which claims carry a verified
proof, which are stated but open, and which definitions others have
endorsed, and spends the report on the mathematics. Submissions can stay
anonymous while under review, so the formal side is checked without
unblinding anyone.

### Digesting existing results

A proof that exists is a different thing from a proof that is understood.
Take a result someone else has verified and write the exposition that makes
it clear: a cleaner definition, a sharper intermediate lemma, a different
route to the same theorem. Your commentary is pinned to the same verified
statements, so it inherits their correctness and adds what was missing.
Understanding becomes a contribution the archive records and credits.
