# Contributing

A submission is a self-contained Lean development, concepts and proofs with
structured annotations, that you author in your own git repository, build
locally, and submit as a *(repository, commit, folder)* triple. The archive
clones your pushed commit and builds it again on its own server before
anything is published. Nothing is uploaded; the archive references your
repository rather than hosting it.

## Prerequisites

- **Linux or macOS**, with ~10 GB free disk (mathlib artifacts, downloaded
  once).
- **Node.js ≥ 20** and **git**.
- **elan**, the Lean toolchain manager:
  `curl -sSf https://elan.lean-lang.org/elan-init.sh | sh`
- A **GitHub account**. Submissions are authenticated with your GitHub
  identity.

Then install the CLI and check your setup:

```sh
npm install -g lax-archive
lax login     # GitHub device flow; grants no scopes, identity only
lax doctor    # verifies tools, login, and connectivity, and suggests fixes
```

## The workflow

1. **Create a submission.** From inside a git repository of yours:

   ```sh
   lax init my-submission
   ```

   The archive allocates your submission id (`LaxN`) and scaffolds a
   complete Lean workspace with mathlib pinned and prebuilt. The first run
   downloads mathlib artifacts once; after that, builds start in seconds.

2. **Author.** Write your concepts and proofs in the scaffold. The
   normative reference for the annotation format is the spec (`lax spec`).
   The submissions already on the site are working examples.

3. **Build locally, iterate until clean.**

   ```sh
   lax build my-submission
   ```

   This is the same pipeline the server enforces. `--only concepts|proofs`
   narrows iteration, and `lax serve my-submission` previews your
   submission's pages as the archive will render them.

4. **Push, then submit.** The server builds your *pushed* commit, not your
   working tree. Commit, push to a repository the server can clone (public
   GitHub is the easy case), then:

   ```sh
   lax submit my-submission
   ```

   The server clones and builds, which takes about a minute; the CLI polls.
   Success puts the submission in the **draft** state: visible on the site,
   still replaceable by you.

5. **Register** when it is final:

   ```sh
   lax submit my-submission --register
   ```

   A registered submission is citable and cannot be replaced afterwards,
   so the CLI asks you to confirm.

## Good to know

Owners are GitHub identities. Use `lax set-owners` to share a submission
with co-authors before registration.
