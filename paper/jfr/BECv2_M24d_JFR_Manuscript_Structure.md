# Boundary Excess Calculus v2.0: Lean-Supported Verified Milestone Kernels for Boundary-Threshold Reasoning

Author: Htet Ko Ko Naing  
Affiliation: Independent Researcher  
ORCID: 0009-0000-6140-0495  

GitHub: https://github.com/htetkokokonaing-dev/BECv2  
Zenodo DOI: https://doi.org/10.5281/zenodo.21127911  

---

## Abstract

To be revised in Step 2.

---

## Keywords

Lean 4; Mathlib; formal verification; formalized reasoning; proof engineering; boundary-threshold reasoning; certified kernels; reproducibility.

---

# 1. Introduction and Motivation

Purpose:

- Explain what boundary-threshold reasoning is.
- Explain why typed certificates and claim boundaries are needed.
- Explain why Lean 4 / Mathlib verification is useful here.
- Explain that BEC v2.0 is not a universal solver or a replacement foundation.

Core message:

Boundary Excess Calculus v2.0 is a bounded formal-methods artifact. It provides a Lean-supported milestone kernel chain for selected boundary-threshold reasoning components, together with public CI, audit logs, SHA256 checksum records, GitHub release evidence, and Zenodo archival DOI.

---

# 2. Contributions

This paper contributes:

1. A bounded formal claim discipline for boundary-threshold reasoning.
2. A Lean 4 / Mathlib milestone kernel chain M1-M14.
3. A typed certificate-routing structure separating verified kernels from external solver or stochastic evidence.
4. A public reproducibility record with CI, audit logs, checksums, GitHub release, and Zenodo DOI.
5. A worked polyhedral certificate example.
6. Selected Lean code excerpts from the verified repository.

---

# 3. Formal Claim Boundary

This work does not claim that the entire monograph is fully mechanized.

The verified claim is limited to:

- the Lean-supported milestone kernel chain;
- the associated source files;
- the audit logs;
- the checksum records;
- the GitHub Actions verification record;
- the GitHub release and Zenodo archive.

This work does not claim to replace ZFC, HoTT, topology, probability theory, measure theory, category theory, optimization theory, or solver frameworks.

---

# 4. Lean-Supported Milestone Kernels

This section will summarize M1-M14.

Planned content:

- milestone table;
- what each milestone verifies;
- what each milestone does not verify;
- link to audit and checksum records.

---

# 5. Worked Numeric Example

This section will add a concrete polyhedral certificate example.

Example direction:

Let A = { y in Q : 0 <= y <= 1 }.  
Let x = 3/2.  
Choose y = 1 and r = 1/2.  
Then |x - y| = 1/2 <= r.

This illustrates a boundary certificate rather than a universal optimization result.

---

# 6. Selected Lean Code Excerpts

This section will include verified code excerpts from the repository.

Planned excerpts:

- M8 polyhedral slack certificate theorem;
- M13 backend importer witness structure;
- possibly blocked-token / audit note.

Important rule:

Do not invent Lean code here. Use excerpts from CI-passing source files only.

---

# 7. Related Work and Comparison

This section will compare BEC v2.0 with:

- Lean 4 and Mathlib formalization practice;
- proof assistant libraries;
- solver certificate workflows;
- linear programming / polyhedral certificates;
- stochastic bounds such as Hoeffding-style deviation certificates;
- topology and closure operators;
- category-theoretic comparison structures.

The section should explain differences, not only list references.

---

# 8. Reproducibility and Availability

Public repository:

https://github.com/htetkokokonaing-dev/BECv2

Zenodo DOI:

https://doi.org/10.5281/zenodo.21127911

This section will describe:

- Lean version;
- Mathlib/Lake environment;
- GitHub Actions;
- audit logs;
- SHA256 ledger;
- release packages.

---

# 9. Limitations

Limitations:

- The full monograph is not fully mechanized.
- The verified object is the milestone kernel chain.
- External solver outputs require typed import witnesses.
- Stochastic claims require supplied deviation witnesses.
- Worked examples are illustrative, not exhaustive.
- The repository is a bounded formal artifact, not a universal solver.

---

# 10. Conclusion and Future Work

This section will conclude that BEC v2.0 contributes a public, CI-checked Lean milestone chain and an audit-backed method for keeping boundary-threshold claims explicit.

Future work:

- expand worked examples;
- formalize richer semantic layers;
- improve reviewer-readable Lean source formatting;
- add more independent case studies;
- prepare venue-specific JFR formatting.

---

# References

To be carried over from M24c and expanded as needed.

---

# Appendix A. Lean Excerpts

To be filled in Step 5.

---

# Appendix B. Reproducibility Ledger

To be filled from audit logs and release records.
