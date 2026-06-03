# Contextual Capabilities

This repository contains a small formal model of contextual capabilities.
Its main purpose is to guide the design of new secure programming languages.
The model studies how a language can make authority explicit and statically
tracked without forcing every intermediate function to thread the same
capability parameters through its signature.

The core idea is that a capability is still an ordinary typed value, but it can
be provided by the surrounding program context. Code deeper in a call chain may
use that capability when the context supplies it, while the type system records
which capabilities a term may access. This keeps capability use reviewable and
testable, but avoids turning capabilities into hidden ambient authority.

## Contents

- `lambda_cc.v` mechanizes the calculus and soundness proof in Coq.
- `paper/` contains the accompanying paper describing the calculus,
  operational semantics, type system, security intuition, and proof strategy.

## Checking the Coq Development

```sh
coqc lambda_cc.v
```

## Building the Paper

```sh
cd paper
make
```

The paper builds `paper/main.pdf`.

## Citation

If you use this model, please cite:

```bibtex
@misc{lambda-cc,
  author = {Fengyun Liu},
  title = {A Mathematical Model of Contextual Capabilities},
  note = {TypeScope. Mechanized Coq development and accompanying paper},
  year = {2026}
}
```
