# About Lax

As the production of proofs accelerates, mathematicians need effective ways to assess what has been established and decide where to invest their time and attention. If the peer-review process is not supported and reshaped, it is at risk of quickly deteriorating. Formal verification can help with these emerging challenges. Fortunately, autoformalization is also improving at a fast pace. It should therefore become a routine part of mathematical publishing.

Lax is an open archive for mathematics formalized in Lean. It exposes the appropriate surface of definitions and claims for review, and records the checked proofs and assumptions behind them.
Each submission is an independent contribution on which later Lax entries can build.

We believe the paper should remain the primary means of explaining mathematical results and communicating the underlying ideas. Lax augments that exposition with links to formal statements and checked proofs. These annotations give readers more freedom in how they follow the argument: they can skip a verified technical lemma to focus on the main idea, or study its proof because it contains a technique they need. Of course, from the point of view of authors or submitters, the benefits include the peace of mind that comes from knowing a result is correct (once the formalization has been confirmed to be faithful).

## Lax Submission

A Lax submission is a commit in a public Git repository. It holds

- **concepts**: small Lean files presenting a definition, a claim, or a coherent set of definitions and claims.
  A concept pairs a natural-language statement with a (hopefully) faithful Lean encoding. Claims are stated as Lean `axiom`s, without
  proof. Concepts depend only on other Lax concepts and on mathlib.
  They are written in plain, tactic-free Lean that a reader without a proof-assistant background can follow.
  Concepts form the surface exposed on the website for readers to review;
- **proofs**: a separate Lean package that restates each claim as a `theorem` and proves it.
  Proofs are not required to be well written. Lean's kernel certifies that they prove precisely the claims stated in the corresponding concepts.
  Providing a human-friendly proof remains the paper's job;
- a **paper**: an optional LaTeX document whose passages are annotated with the concepts and proofs they correspond to.
  The same source can go to arXiv and to Lax. The website presents a reflowable version, with Lean code beside each marked passage.

To summarize:

- The concepts are the surface: what readers review and endorse.
- The proofs are the evidence supporting the surface.

The archive is fully compositional. New submissions can reuse existing concepts and proofs.

{{concept-proof-flip}}

The proofs of a submission form its *proof network*. This simply illustrates the proof dependencies.
A [proof obligation](open-proof-obligations.html) is a statement that remains unproven.
A later submission can discharge an open obligation.
Every statement that depended on it is then proven.

## How Lax is built

Lax consists of three parts, all of them open source:

- the **command-line tool**, `lax`, published on npm. It creates the layout of a submission.
  Then it builds and previews it, and finally submits it.
  Its built-in guide (`lax print instructions`) is written for coding agents, so that an agent
  can autonomously carry a formalization from start to finish;
- the **submission pipeline**, which runs as a GitHub Actions workflow. A
  submission, we recall, is a pointer to a commit in a public Git repository.
  The pipeline fetches it, builds it, verifies the proofs against the concepts, and records the result in the archive's metadata repository;
- the **website**, a static site generated from that metadata and the built
  submissions. It is served from GitHub Pages. Lax can also serve your local version.
  You sign in with your ORCID iD to endorse or flag concepts, or leave comments.

The archive's code, metadata, the submissions, and the generated artifacts are all public.

## Where to go next

- [An Introduction to Lax](lax-242665/paper.html), itself a Lax submission.
- The [FAQ](index.html#faq) may answer some of your questions.
- Join the [Lax Discord](https://discord.gg/hgWMN5ztca) to ask questions,
  compare formalization experiences, and share feedback with the community.
- For direct feedback or questions you would rather send privately, email
  [lax.lean.archive@gmail.com](mailto:lax.lean.archive@gmail.com).

## Who we are

Lax is a project by Édouard Bonnet (CNRS, ENS Lyon, LIP), Jan Dreier (TU Wien and
HPI Potsdam), and Clemens Kuske (TU Wien and HPI Potsdam).

## Acknowledgments

We thank Szymon Toruńczyk for his several submissions and suggestions, Mikolaj Bojańczyk and Fatemeh Ghasemi for early tests, and Holger Dell for detailed feedback. We also thank Marcin Pilipczuk, Nikolas Mählmann, Louis Esperet, and Lance Fortnow for pointers, comments, and encouragement.
