Formalized mathematics that can be read, checked, and built upon.

Lax is an open archive for contemporary mathematics written in Lean. Think of
it as an arXiv for formalization: independent, citable submissions that people
can read, software can check, and future work can build upon.

## What you can do here

- **Read.** Browse submissions and their concepts as human-readable statements
  alongside their Lean source. Every claim shows its evidence: which proofs
  establish it, under which assumptions.
- **Review.** Review a concept or submission, endorse correct mathematics, or
  flag possible flaws.
- **Submit.** Publish your own formalization. You may build upon definitions
  and theorems of existing submissions.
- **Cite.** Every page carries a ready-made BibTeX entry.

## Creating your own submission

Contributing is a two-step process.

1. **Set up**, once per machine:

   ```sh
   npm install -g lax-archive
   lax login     # sign in with GitHub (identity only, no repo access)
   lax doctor    # checks your setup and installs whatever is missing
   ```

2. **Hand your coding agent** a prompt like:

   ```
   Run `lax print instructions` and follow the guide it prints
   to formalize <my result>.
   ```

Prefer to work hands-on, or want to know what happens at each step? See
[Getting started](contributing.html).

<!--## Background-->
<!---->
<!--Technically, a concept states a claim as a Lean ``axiom``, and a proof-->
<!--discharges it by providing a ``theorem`` whose statement is definitionally-->
<!--equal to that axiom.-->
<!--Our server (todo give guarantees).-->
