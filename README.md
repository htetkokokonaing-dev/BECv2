# Boundary Excess Calculus v2.0

**Lean-supported verified milestone kernels for boundary-threshold reasoning.**

This repository is the GitHub-ready clean source package for BEC v2.0. It contains the Lean 4 / Mathlib milestone kernels that were checked separately and then packaged into the M15/M16 release evidence.

## Formal claim

BEC v2.0 provides a Lean-supported, audit-backed boundary-threshold framework with verified milestone kernels for:

- universe formation and graph-based certificate routing;
- compiler normal forms;
- stochastic certificate transfer;
- Boolean topology;
- Boundary Type Theory foundations;
- polyhedral slack certificates;
- dynamic generator certificates;
- solver-backend certificate importing;
- categorical morphism and conservative comparison.

## Claim boundary

This repository does **not** claim that the entire monograph has been fully mechanized. It also does **not** claim that BEC replaces ZFC, HoTT, topology, probability theory, measure theory, category theory, or numerical optimization. The verified claim is the milestone kernel chain and the associated audit evidence.

## Repository layout

```text
BECv2/
  BECv2.lean
  BECv2/
    M1_MinKernel.lean
    M2_Compiler.lean
    M3_Probability.lean
    M4_Topology.lean
    M5_BTT.lean
    M8_PolyhedralSolver.lean
    M9_Dynamic.lean
    M13_BackendImporter.lean
    M14_Categorical.lean
  scripts/
    check_all.sh
    blocked_token_scan.sh
  paper/
    BECv2_M16_FinalMonographAssembly.pdf
    BECv2_M16_FinalMonographAssembly.tex
    BECv2_M16_FinalMonographAssembly.md
  audit/
    SHA256_LEDGER.md
    packages/
    logs/
  release/
    BECv2_M15_PublicationRelease_M1_M14.zip
    BECv2_M16_FinalMonographRelease.zip
```

## Reproduce

From the repository root:

```bash
lake update
lake exe cache get
./scripts/check_all.sh
```

For a minimal source-only check:

```bash
lake env lean BECv2.lean
```

The scripts also run a blocked-token scan for:

```text
sorry
admit
axiom
unsafe
```

## Citation

See `CITATION.cff`.

## Suggested public wording

> Boundary Excess Calculus v2.0 is a Lean-supported, audit-backed framework for boundary-threshold reasoning with verified milestone kernels M1-M14.

## DOI

This release is archived on Zenodo:

DOI: 10.5281/zenodo.21127911
