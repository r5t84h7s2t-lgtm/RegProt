# RegProt Isabelle/HOL Artifact

This artifact contains the Isabelle/HOL development accompanying the
submitted paper on AArch64 register protection. The active session is
`RegProt`; all theories used by the paper are rooted at `src/`.

## Requirements

- Isabelle2025
- The `HOL-Library` session distributed with Isabelle2025

## Build

From this directory, run:

```sh
isabelle build -D . RegProt
```

Alternatively, if `isabelle` is on `PATH`, run:

```sh
make check
```

A successful build checks every theory listed in `ROOT`, including the global
security-model interpretation and the MTE and TTBR1 property theories.

## Structure

```text
src/machine/       AArch64 register datatypes, state, accessors, and defaults
src/handlers/      Hand-written Isabelle functional handler models
src/framework/     Security-model and register-strategy locales
src/instances/     Per-register locale interpretations and local theorems
src/system/        Global state machine and SecurityModel interpretation
src/properties/    Attack-facing properties derived from the global model
```

The SCTLR definitions and proofs shown in the paper are in
`src/instances/SCTLR.thy`. The global well-formedness and consistency predicates
are in `src/system/RegProt_Model.thy`.
