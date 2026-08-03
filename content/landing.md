To formalized mathematics what arXiv is to preprints: a network of
independent, citable submissions building on one another.

Submissions are written in Lean, a proof assistant in which mathematics is
code. Lean checks correctness, not meaning: it certifies that a theorem is
true, but not that it says what the author intended.

Lax separates submissions into **concepts** and **proofs**.

- **Concepts** are the minimal code surface required to determine meaning. They
  demand careful human reading to ensure they match the author's intent.
- **Proofs** are verified by Lean's kernel. They are therefore free to be long,
  unreadable, or machine-generated.

In Lax, proofs merely establish **what** is true, not **why** it is true.
The latter lives in the accompanying exposition and papers.


## What you can do here

- **Read.** Browse submissions and their concepts as human-readable statements
  alongside their Lean source. Every claim shows its evidence: which proofs
  establish it, under which assumptions.
- **Review.** Correctness is machine-checked, but whether a concept says what
  it claims to say needs human eyes. Read a concept, and endorse or flag it.
- **Submit.** Publish your own formalization. You may build upon definitions
  and theorems of existing submissions.
- **Cite.** Every page carries a ready-made BibTeX entry.

## Creating your own submission

The fastest way to contribute is to hand your AI agent (preferably a frontier
model like Claude Fable) a prompt like:

```
Use Lax to formalize <my result>. Steps:
- Install the lax CLI (npm install -g lax-archive) and familiarize
  yourself with the tool, e.g. by reading `lax spec`.
- Design the concepts: find the cleanest partition of the mathematics
  into individual concepts, reusing suitable concepts from other submissions
  where possible, and ask me for feedback on the design.
  Favor code that is easy to review, also for non-experts.
- Write the concepts and show them to me via `lax serve`.
- Once I have approved the concepts, write the proofs. For this step,
  act as supervisor and delegate individual proofs to subagents to
  keep your own context clean.
```
Prefer to work hands-on, or want to know what happens at each step? See
[Contributing](contributing.html).

<!--## Background-->
<!---->
<!--Technically, a concept states a claim as a Lean ``axiom``, and a proof-->
<!--discharges it by providing a ``theorem`` whose statement is definitionally-->
<!--equal to that axiom.-->
<!--Our server (todo give guarantees).-->
