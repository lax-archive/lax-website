# Let's stay in control of mathematics

AI is about to massively accelerate mathematical research. This will push the
classical system of peer review and publishing beyond its limits. We need new,
scalable mechanisms for digesting mathematics, or we risk losing control of
our own field.

Proof assistants like Lean provide a scalable way of ensuring *correctness*.\
Lax builds on this foundation to make formal mathematics scalable for humans
too, by organizing results and making them easy to review and reuse.

## How it works

**Concepts and proofs.** Lax annotates natural-language mathematics with Lean.
Each definition or claim is tied to a *concept*: a reusable block that pairs a
mathematical statement with a faithful Lean encoding. Each proof is tied to
Lean code that derives one concept from others. Concepts and proofs can be
reused across submissions.

## Proof network

**Proof network.** Explore how proofs compose, which claims are proven,
and which are not yet. Any later submission can discharge an
[open obligation](open-proof-obligations.html), and every result that
rested on it is proven from that moment on.

## Get started right away

### Linux / macOS

Set up, once per machine:

```
npm install -g lax-archive && lax doctor
```

Hand your coding agent a prompt like:

```
Run `lax print instructions` and follow the guide to formalize <my result>.
```

Then your agent takes over and guides you through the process.

### Windows

First, open PowerShell as administrator and install a
[Linux terminal with WSL](https://learn.microsoft.com/en-us/windows/wsl/install):

```
wsl --install
```

After restarting, open Ubuntu.

Set up, once per machine:

```
npm install -g lax-archive
lax doctor
```

Hand your coding agent a prompt like:

```
Run `lax print instructions` and follow the guide to formalize <my result>.
```

Then your agent takes over and guides you through the process.

## Build foundations together

Concepts are shared across submissions. Below are some definitions other
submissions already build on.

- Lax67.Ram
- Lax48.TwinWidth
- Lax434930.NondeterministicPolynomialTime
- Lax132576.RationalFunctions
- Lax12.NowhereDenseClasses
- Lax11.GraphEncoding
