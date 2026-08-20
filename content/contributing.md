# Getting started

A submission is a self-contained Lean development, concepts and proofs with
structured annotations, that you author in your own git repository, build
locally, and submit as a *(repository, commit, folder)* triple. The archive
clones your pushed commit and validates it again on trusted infrastructure
before anything is published. Your code stays in your repository; the
archive links to it rather than hosting a copy.

## Setup

You need **Linux or macOS** with ~10 GB free disk, **Node.js ≥ 20**, **git**,
and a **GitHub account** — submissions are authenticated with your GitHub
identity. Then:

```sh
npm install -g lax-archive
lax login     # sign in with GitHub (identity only, no repo access)
lax doctor    # checks your setup and installs whatever is missing
```

`lax doctor` installs everything building requires: the Lean toolchain and
prebuilt mathlib (a large download, once per machine), plus a local copy of
the archive database.

## The workflow

The fastest route is to let a coding agent do the work: run `lax print
instructions` and hand its output to your agent, along with the result you
want formalized. The steps below are that same workflow, by hand.

1. **Create a submission.** From inside a public git repository of yours:

   ```sh
   lax init my-submission
   ```

   The archive allocates your submission id and scaffolds a complete Lean
   workspace with mathlib pinned and prebuilt.

2. **Author.** Write your concepts and proofs in the scaffold. The
   annotation format is defined in the spec (`lax print spec`), and the
   submissions already on the site are working examples.

3. **Build locally, iterate until clean.**

   ```sh
   lax build my-submission
   ```

   This is the same pipeline the archive enforces, and `lax serve
   my-submission` previews your submission's pages as the archive will
   render them.

4. **Push, then submit.** The archive builds your *pushed* commit, not your
   working tree. Commit, push, then:

   ```sh
   lax submit my-submission
   ```

   The archive validates the commit while the CLI follows along and prints
   any findings in your terminal. Success puts the submission in the
   **draft** state: visible on the site, still replaceable by you.

5. **Register** when it is final:

   ```sh
   lax register my-submission
   ```

   A registered submission is citable and cannot be replaced afterwards,
   so the CLI asks you to confirm.

## Good to know

Owners are GitHub identities. Use `lax owners` to share a submission with
co-authors before registration.
