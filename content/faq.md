# Frequently asked questions

Short answers about submissions, peer review, compatibility, and how Lax fits
into the formalization ecosystem.

## How does Lax relate to projects such as Merely True and Tau Ceti?

In Merely True and Tau Ceti, individual contributions blend into a shared
library. Lax keeps each submission as a distinct, citable unit. This is closer
to academic publishing culture: a submission can be cited directly or attached
— anonymously, if needed — to a conference or journal submission for review.

Like Lean Pool and the [Palomar Registry](https://palomar-registry.org/), Lax
archives individual submissions. The important difference is that Lax
submissions can build on one another. A base submission might define a concept
such as treewidth; later submissions can cite and import it instead of asking
the community to vet the same definition again.

## How can Lax help with conference and journal review?

A paper accompanied by a Lax submission gives reviewers a shorter route to
checking that its formal statements are correct. Lax exposes the semantic
closure of each statement: the definitions, assumptions, and results on which
it depends. Reviewers can therefore focus their limited time on the ideas and
techniques, while readers can inspect full proofs whenever those details matter
to them.

## Can I use Lax for anonymous peer review?

Yes. List the author as **Anonymous author** and keep the submission in draft
mode during review. You can replace the placeholder with the real author name
before registering the final, permanent version.

## Can I work on two submissions in parallel locally?

Yes. Keep each submission in a separate repository checkout or Git worktree,
then run Lax from the corresponding project directory. That keeps each
submission's manifest and working tree independent while sharing the installed
toolchain.

## Which operating systems does Lax support?

Lax is tested on Linux and macOS. On Windows, use the Windows Subsystem for
Linux (WSL); native Windows support is not currently tested.

## Does my submission need to be hosted on GitHub?

No. Lax accepts submissions hosted on [GitHub](https://github.com/),
[GitLab.com](https://gitlab.com/), [Codeberg](https://codeberg.org/), and
[Bitbucket Cloud](https://bitbucket.org/). If your preferred Git host is
missing, contact the Lax team so support can be considered.

## How do dependencies stay compatible as mathlib changes?

Submissions that build on one another need compatible Lean, mathlib, and other
dependency versions. Lax therefore plans to use long epochs that freeze those
versions across the archive. When a new epoch is needed, the community can
carry useful submissions forward based on demand: if you build on something,
help bump it. Epoch length will follow how the archive and its community evolve.
