Formalized mathematics that can be read, checked, and built upon.

Lax is an open archive for contemporary mathematics written in Lean. Think of
it as an arXiv for formalization: independent, citable submissions that people
can read, software can check, and future work can build upon.

## What you can do here

- **Read.** Browse submissions and their concepts as human-readable statements
  alongside their Lean source. Every claim shows its evidence: which proofs
  establish it, under which assumptions.
- **Review.** Browse claims that do not yet have a grounded proof, read their
  formal statements, and identify a route to proving them.
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
