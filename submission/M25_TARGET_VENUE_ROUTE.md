# M25 Target Venue and Submission Route

## Project

Boundary Excess Calculus v2.0

## Public records

GitHub repository:
https://github.com/htetkokokonaing-dev/BECv2

Zenodo DOI:
https://doi.org/10.5281/zenodo.21127911

GitHub release:
v2.0.0

## Current verification status

- Public GitHub repository: complete
- GitHub Actions Lean workflow: passing
- GitHub release: published
- Zenodo DOI: published
- Final PDF/DOCX submission files: prepared

## Recommended submission route

The recommended route is staged:

1. Maintain GitHub + Zenodo as the permanent verification record.
2. Prepare a preprint-style submission package.
3. Frame the manuscript as a bounded formal-methods / mathematical-software artifact.
4. Submit to a formalization-oriented or proof-engineering venue.
5. Use JOSS only if the paper is rewritten as a software-focused short paper.
6. Consider CPP/ITP-style conference submission only after strengthening the proof-engineering narrative.

## Best first framing

The strongest first framing is:

**Lean-supported verified milestone kernels for boundary-threshold reasoning.**

This emphasizes:

- Lean 4 / Mathlib source code;
- CI-backed verification;
- audit logs;
- SHA256 checksum records;
- GitHub release;
- Zenodo DOI;
- bounded formal claim.

## Recommended target classes

### Route A: Preprint first

Use the final PDF and source materials as a preprint package.

Purpose:

- establish public priority;
- make GitHub and DOI citable;
- allow later journal or conference submission.

### Route B: Formalized reasoning journal

Suitable framing:

- formalized reasoning;
- mechanized mathematics support artifact;
- Lean-supported milestone verification;
- proof-engineering report.

### Route C: Mathematical software / research software journal

Suitable only if the manuscript is rewritten as a software-paper.

Required emphasis:

- what the software does;
- who should use it;
- installation and reproducibility;
- examples;
- tests and CI;
- limitations.

### Route D: Formal verification conference

Suitable after the submission is sharpened around:

- proof engineering;
- certified kernels;
- formal verification architecture;
- comparison with existing Lean formalization practices.

## Not recommended framing

Avoid framing BEC v2.0 as:

- a replacement for ZFC, HoTT, topology, probability, measure theory, category theory, or optimization;
- a complete new foundation for all mathematics;
- a fully mechanized monograph;
- a universal solver;
- a complete proof of all exposition in the manuscript.

## Final M25 decision

The project is ready for venue-specific preparation.

Recommended next stage:

M26 = venue-specific manuscript adaptation.

M26 should prepare one of the following:

1. Preprint package;
2. Formalized reasoning journal package;
3. JOSS-style software paper package;
4. Formal verification conference package.
