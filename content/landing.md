Formalized mathematics, in public.

Lax is an open archive for contemporary mathematics written in Lean. Think of
it as an arXiv for formalization: independent, citable submissions that people
can read, software can check, and future work can build upon.

## How Lax works

- **Concepts carry meaning.** Small, transparent files state the definitions
  and claims. People review them to decide whether the formal statement really
  matches the mathematics the author intended.
- **Proofs establish correctness.** Separate proof packages provide the
  evidence. They may be long or machine-generated; Lean's kernel checks that
  they prove exactly the published claim.

## The paper in brief

The Lax paper explains the archive as an open path from a mathematical result
to a durable, inspectable formalization.

- **Open by default.** The command-line tool, submission metadata, source code,
  generated artifacts, and website are public and reusable.
- **Designed for current research.** Lax focuses on contemporary results whose
  complete formal proofs may be produced by AI agents, while keeping the
  mathematical surface concise enough for human review.
- **Useful beyond verification.** Publishing makes a formalization visible,
  legible, citable, and easy for later submissions to reuse.
- **Trust can be earned independently.** Anyone can rebuild a submission,
  inspect which axioms it uses, and check that a proof's type matches its
  concept. Untrusted Lean projects should always be tested in a sandbox.

[Read the complete Lax paper](assets/lax-white-paper.pdf)

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
