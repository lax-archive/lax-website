# Let's stay in control of mathematics

AI is about to massively accelerate mathematical research. This will push the
classical system of peer review and publishing beyond its limits. We need new,
scalable mechanisms for digesting mathematics, or we risk losing control of
our own field.

Proof systems like Lean provide a scalable way of ensuring the
*correctness* of mathematics. This frees humans to spend their finite
attention on developing *intuition*, *clarity*, and *abstractions*.

## How it works

**The paper stays the paper.** Lax annotates natural-language mathematics
with Lean. Each definition or claim, where it stands in the paper, is tied
to a *concept*: a reusable block that pairs a mathematical statement with a
faithful Lean encoding. Each proof is tied to Lean code that derives one
concept from others. Freely composable across papers.

## Proof network

*Proofs compose.* Explore which claims are proven, relative to which others.
Later submissions can discharge an [open obligation](open-proof-obligations.html).

## Get started right away

### Linux / macOS

Set up, once per machine:

```
npm install -g lax-archive && lax doctor
```

Hand your coding agent a prompt like:

```
Run `lax print instructions` and follow the guide it prints
to formalize <my result>.
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
Run `lax print instructions` and follow the guide it prints
to formalize <my result>.
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
