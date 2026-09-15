# FAQ

## How do I create my own submission?

Contributing is a two-step process. Set up once per machine with
`npm install -g lax-archive` followed by `lax doctor`, then hand your coding
agent a prompt such as "Run `lax print instructions` and follow the guide
to formalize `<my result>`." See [Getting started](contributing.html) for
what happens at each step.

## How does Lax relate to Merely True, Tau Ceti, Lean Pool, and the Palomar Registry?

In Merely True and Tau Ceti, individual contributions blend into a shared
library. Lax keeps each submission as a distinct, citable unit. This is closer
to academic publishing culture: a submission can be cited directly or attached
to a conference or journal submission for review, anonymously if needed.

Like Lean Pool and the Palomar Registry, Lax archives individual submissions.
The important difference is that Lax submissions can build on one another. A
base submission might define a concept such as treewidth, the RAM model, game
semantics, or an orbifold. Following submissions can import it instead of
reformalizing it and asking the community to vet the same definition again.

## How can Lax help with conference and journal review?

A paper accompanied by a Lax submission gives reviewers a shorter route to
checking that its formal statements are correct. Lax exposes the semantic
closure of each statement: a minimal set of declarations that fully specifies
it. Reviewers can therefore focus their limited time on the ideas and
techniques.

## Can I use Lax for anonymous peer review?

Yes. Set `anonymous: true` in `manifest.yaml` and submit as usual. The site
then withholds author names, the citation, the bibliography, and every link to
your source repository. This is presentation-level anonymity compatible with
light double-blind review. The repository and your work stay public.

## Can I work on two submissions in parallel locally?

Yes. If one depends on the other, its pinned require must match the
dependency's archive record, so every edit to the dependency would otherwise
need a submit first. Instead, keep both in one repository and add a Lake
package override in `.lake/package-overrides.json` that points the
dependency's package name at the sibling folder. Plain `lake build` then reads
the working tree while the pin stays untouched. When the dependency is ready,
submit it, update the pin, and run `lax build`, which rebuilds from the pins
alone.

## Why are files, not declarations, the basic unit of Lax?

Because many mathematical concepts cannot be expressed in a single
declaration. Treewidth, for example, needs a structure for tree
decompositions, a definition of their width, and a definition of the parameter
as a minimum over them. These only make sense together, and a reader vetting
the definition needs to see all of them. Lax therefore treats the file as the
atomic unit of a concept.

## What if I can only formalize my paper's content, not its large dependencies?

State each result you rely on as a concept without a proof. You can leave it
as an open obligation of your own submission, or put it in a separate
concept-only submission dedicated to that result.

## Which operating systems does Lax support?

Lax is tested on Linux and macOS. On Windows, use the Windows Subsystem for
Linux (WSL). Native Windows support is not currently tested.

## Does my submission need to be hosted on GitHub?

No. Lax accepts submissions hosted on [GitHub](https://github.com/),
[GitLab.com](https://gitlab.com/), [Codeberg](https://codeberg.org/), and
[Bitbucket Cloud](https://bitbucket.org/). If your preferred Git host is
missing, please contact us.

## How do dependencies stay compatible as mathlib changes?

Submissions that build on one another need compatible Lean, mathlib, and other
dependency versions. Lax therefore plans to use long epochs that freeze those
versions across the archive. When a new epoch is needed, the community can
carry useful submissions forward based on demand. Epoch length will follow how
the archive and its community evolve.

## Won't publishing formalizations accelerate loss of control of mathematics?

Published formalizations can be used to autonomously prove new theorems.
However, we believe the benefits of maintaining these formalizations within
our community, and using them to understand new mathematics, outweigh the
risks.
