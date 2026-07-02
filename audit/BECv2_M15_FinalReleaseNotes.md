# BEC v2.0 Final Release Notes — M15

## Release title

Boundary Excess Calculus v2.0: Verified Milestone Kernel Chain M1-M14

## Core release statement

BEC v2.0 now has a Lean 4.31.0 / Mathlib verified milestone chain through M14, with a publication-level reproducibility package at M15.

## Verified milestones

- M1: Universe + Graph + Licensed Route Kernel.
- M2: Compiler Normal Form Soundness.
- M3: Probability / Stochastic Certificate Kernel.
- M4: Topology Boolean Closure Kernel.
- M5: Boundary Type Theory Foundation Kernel.
- M6: Audit Manifest M1-M5.
- M7: All-in-One Kernel M1-M5.
- M8: Polyhedral Solver Kernel.
- M9: Dynamic Generator Kernel.
- M10: Final Audit Bundle M1-M9.
- M11: Monograph Integration Package.
- M12: Extended All-in-One Kernel M1-M5 + M8 + M9.
- M13: Solver Backend Importer.
- M14: Categorical Morphism / Lax Comparison Kernel.
- M15: Publication / Reproducibility Package.

## Most important methodological point

BEC v2.0 does not rely on unscoped claims of universality. Its verified core is deliberately staged:

1. define a kernel;
2. compile-check the kernel;
3. scan for blocked placeholders;
4. record logs and SHA256;
5. integrate into a conservative audit ledger.

## Suggested citation wording

Use:

> The BEC v2.0 formal release provides a staged Lean 4 / Mathlib audit chain through M14, with separately reproducible milestone packages and a final M15 publication bundle.

Avoid:

> The whole BEC monograph is fully formalized.

Avoid:

> BEC supersedes all mathematical foundations.
