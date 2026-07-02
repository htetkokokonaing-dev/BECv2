---
title: "Boundary Excess Calculus v2.0"
subtitle: "Final Monograph Assembly - Verified Kernel Release M1-M15"
author: "Htet Ko Ko Naing, Independent Researcher, ORCID: 0009-0000-6140-0495"
date: "2026-07-02"
geometry: margin=1in
fontsize: 11pt
---

# Formal Claim Boundary

Boundary Excess Calculus v2.0 (BEC v2.0) is a boundary-threshold calculus with a staged Lean 4 / Mathlib verification program. The current release is a verified kernel chain, not a claim that every theorem in the full monograph has been mechanized.

The formal claim of this release is:

> BEC v2.0 has a Lean 4.31.0 / Mathlib checked milestone chain M1-M14, with a final M15 publication and reproducibility package containing pass logs, blocked-token scans, SHA256 ledgers, and release documentation.

The following stronger claims are explicitly not made:

1. BEC does not replace ZFC, HoTT, topology, measure theory, probability theory, stochastic analysis, or category theory.
2. BEC is not presented as an unrestricted universal solver.
3. The entire monograph is not claimed to be fully mechanized.
4. External solver outputs are trusted only after passing typed certificate-import witnesses.
5. Stochastic certificates are not silently promoted to deterministic certificates.

# 1. Foundational Framework and Universe Core

A BEC v2.0 universe is an eleven-tuple

$$
B=(X, Ref, V,\le_V,0_V,\top_V,op,E,Assump,Claim,Cert).
$$

Here $X$ is the carrier of objects, $Ref$ is the type of reference boundaries, and $V$ is the value object into which boundary excess is measured. The relation $\le_V$ is a preorder on $V$, $0_V$ is the zero-excess element, $\top_V$ is a maximal or failure-tolerant bound, and $op:V\times V\to V$ is the additive or compositional excess operation used by licensed aggregation. The excess map is

$$
E:Ref\times X\to V.
$$

The last three components are logical: $Assump$ is the type of assumptions, $Claim$ is the type of BEC-native claims, and $Cert:Claim\to Type$ is the certificate family. A certificate is not a proof of an arbitrary proposition; it is a typed witness for a BEC-native claim under explicit routing discipline.

For $A\in Ref$ and $r,s\in V$, the basic threshold and shell operators are

$$
T_r(A)=\{x\in X:E(A,x)\le_V r\},
$$

$$
T^{<}_r(A)=\{x\in X:E(A,x)<_V r\},
$$

$$
S_{r,s}(A)=\{x\in X:r<_V E(A,x)\le_V s\}.
$$

A metric instance takes $V=[0,\infty]$ and

$$
E(A,x)=\inf_{a\in A}d(x,a).
$$

A topological Boolean instance takes $V=\{0,1\}$, where $0$ means closure membership and $1$ records excess from closure membership.

# 2. Boundary-Threshold Graph Layer

A Boundary-Threshold Graph is a five-tuple

$$
G_B=(N,E_G,\ell,\gamma,\omega).
$$

The node type $N$ consists of typed claims. The edge relation $E_G\subseteq N\times N$ records claim-routing pathways. The map $\ell$ records the target claim level, $\gamma$ gives the assumption gate required to traverse an edge, and $\omega$ is the obstruction record emitted when the gate is not licensed.

A route is safe only when each edge is licensed. Thus BEC route transport has the form

$$
\operatorname{LicensedRoute}(G_B,\Gamma,p,q)
\Rightarrow Cert(p)\to Cert(q).
$$

If a license is missing, BEC does not promote the claim. It reports an obstruction. This is the central discipline that persists from v1.0 through v2.0.

# 3. Computational Engine

BEC v2.0 restricts computational claims to BEC-shaped problems. A problem is BEC-shaped when it is expressible as a boundary, threshold, shell, profile, or certificate-routing claim over explicit carriers, references, metrics, orders, or finite profiles.

## 3.1 Polyhedral $L_\infty$ case

Let

$$
A=\{y\in\mathbb{Q}^n:My\le b\}.
$$

For $x\in\mathbb{Q}^n$, the claim

$$
E_\infty(A,x)\le r
$$

is represented by the linear feasibility system

$$
\exists y\in\mathbb{Q}^n\;\bigl(My\le b\;\wedge\;\forall i,\; -r\le x_i-y_i\le r\bigr).
$$

Equivalently, using slack variables $u_i\ge 0$, it is enough to require

$$
x_i-y_i\le u_i,
\qquad
 y_i-x_i\le u_i,
\qquad
u_i\le r.
$$

Then

$$
|x_i-y_i|\le r
$$

for every coordinate $i$.

## 3.2 Polyhedral $L_1$ case

The $L_1$ threshold is encoded by slack variables

$$
u_i\ge 0,
\qquad x_i-y_i\le u_i,
\qquad y_i-x_i\le u_i,
\qquad \sum_i u_i\le r.
$$

This implies

$$
\sum_i |x_i-y_i|\le r.
$$

M8 verifies these two certificate shapes in Lean over rational vectors. M13 extends the layer with a backend-import interface: a solver export becomes a BEC certificate only when a Lean-side import witness supplies status acceptance, norm agreement, radius agreement, polyhedron membership, nonnegative slack variables, and the appropriate slack inequalities.

# 4. Compiler Normal Forms

The compiler layer is not a universal mathematical compiler. It is a typed front end for the fragment of inputs that already lie within BEC's boundary-threshold vocabulary. Its soundness statement is:

$$
\operatorname{normalizeProblem}(P)=\operatorname{ok}(N)
\Rightarrow
\operatorname{NativeNormalForm}(N).
$$

Thus successful compilation produces only BEC-native normal forms. Failed compilation is not a defect; it is part of the safety boundary. The compiler refuses to erase assumptions, silently coerce stochastic claims into deterministic ones, or create unlicensed certificate transport.

# 5. Stochastic Boundary Calculus

Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space. A stochastic boundary claim has the form

$$
\mathbb P(E(A,Y)\le \tau)\ge \alpha.
$$

For two events

$$
P=\{E(A,Y)\le \tau\},\qquad Q=\{E(Y,B)\le \sigma\},
$$

if $P\cap Q\subseteq R$, then the union bound gives

$$
\mathbb P(R)
\ge \mathbb P(P\cap Q)
=1-\mathbb P(P^c\cup Q^c)
\ge 1-\mathbb P(P^c)-\mathbb P(Q^c)
\ge \alpha+\beta-1.
$$

This is the verified M3 stochastic-transfer kernel. Empirical certificates follow the Hoeffding shape

$$
\mathbb P(|\widehat p-p|\le \varepsilon)\ge 1-2\exp(-2n\varepsilon^2),
$$

and the deterministic Lean-side certificate rule records only the algebraic consequence

$$
|\widehat p-p|\le\varepsilon,
\qquad \alpha\le \widehat p-\varepsilon
\Rightarrow
\alpha\le p.
$$

The exponential confidence expression is analytic data; the verified core checks the implication once the deviation witness is supplied.

# 6. Dynamic Boundary Layer

The dynamic layer records generator inequalities of the form

$$
\partial_t\phi+\mathcal L_t\phi\le -\kappa\phi+c.
$$

A dynamic risk certificate records a positive radius $r>0$, moment bound $M\ge 0$, and safety parameter $\alpha$ satisfying

$$
\alpha\le 1-\frac{M}{r}.
$$

M9 verifies that the moment-radius safety inequality is recovered from the certificate data and that cut-locus local-time corrections are explicit nonnegative bookkeeping terms. The release does not claim a full mechanization of Itô-Tanaka analysis; it verifies the structural certificate layer required to prevent unlicensed dynamic boundary claims.

# 7. Boolean Topology Fragment

For a Kuratowski closure operator $C$, define Boolean excess by

$$
E_C(A,x)=0 \iff x\in C(A),
\qquad
E_C(A,x)=1 \iff x\notin C(A).
$$

The zero threshold then recovers closure:

$$
T_0(A)=\{x:E_C(A,x)\le 0\}=C(A).
$$

M4 verifies this Boolean closure-excess fragment. The claim is conservative: topology is represented as a Boolean BEC fragment; BEC is not asserted to replace topology or its foundations.

# 8. Boundary Type Theory

Boundary Type Theory (BTT) is the type-theoretic layer for BEC-native judgments. Its primitive forms include context formation, boundary type formation, reference formation, excess judgment, threshold judgment, shell judgment, route judgment, certificate judgment, and obstruction judgment.

A typical soundness rule is

$$
Cert_\Gamma(\varphi)\Rightarrow \Gamma\models\varphi.
$$

M5 verifies the minimum BTT carrier, primitive judgment type, certificate soundness, obstruction honesty construction, and conservative interpretation soundness. BTT is a layer for threshold reasoning; it is not a replacement for all type theory.

# 9. Categorical Comparison Layer

A claim kernel consists of claims, certificates, routes, route identity, route composition, and certificate transport. For routes

$$
\rho:p\to q,
\qquad
\sigma:q\to r,
$$

BEC requires

$$
transport(\sigma\circ\rho,c)=transport(\sigma,transport(\rho,c)).
$$

A kernel morphism preserves certificate transport:

$$
F(transport_K(\rho,c))=transport_L(F\rho,Fc).
$$

M14 verifies the categorical morphism, lax comparison, conservative pullback, graph paths, and graph-path certificate transport. This is the precise categorical comparison claim licensed by the release.

# 10. Lean Verification Ledger

The recorded environment is

$$
\text{Lean }4.31.0,\qquad \text{Mathlib/Lake},\qquad \text{aarch64-unknown-linux-gnu}.
$$

Each checked milestone package contains a Lean file, shell check script, pass log, blocked-token scan, and SHA256 evidence. The blocked-token scan checks for

$$
\texttt{sorry},\quad \texttt{admit},\quad \texttt{axiom},\quad \texttt{unsafe}.
$$

The complete release ledger is included in the M15 publication package.

# 11. Milestone Status

| Milestone | Scope | Status |
|---|---|---|
| M1 | Universe + Graph + Licensed Route Kernel | PASS |
| M2 | Compiler Normal Form Soundness | PASS |
| M3 | Probability / Stochastic Certificate Kernel | PASS |
| M4 | Topology Boolean Closure Kernel | PASS |
| M5 | Boundary Type Theory Foundation Kernel | PASS |
| M6 | Audit Manifest M1-M5 | GENERATED |
| M7 | All-in-One Kernel M1-M5 | PASS |
| M8 | Polyhedral Solver Kernel | PASS |
| M9 | Dynamic Generator Kernel | PASS |
| M10 | Final Audit Bundle M1-M9 | GENERATED |
| M11 | Monograph Integration Package | GENERATED |
| M12 | Extended All-in-One Kernel M1-M5 + M8 + M9 | PASS |
| M13 | Solver Backend Importer | PASS |
| M14 | Categorical Morphism / Lax Comparison Kernel | PASS |
| M15 | Publication / Reproducibility Package | GENERATED |

# 12. Package SHA256 Ledger

The full package SHA256 ledger is stored in the accompanying M15 ledger and M16 machine-readable JSON file. The compact table below gives SHA256 prefixes for visual audit in the PDF edition.

| Milestone | Artifact | SHA256 prefix |
|---|---|---|
| M1 | Universe + Graph + Licensed Route Kernel | `52719cb28ec77997` |
| M2 | Compiler Normal Form Soundness | `d0c230856cbd0a05` |
| M3 | Probability / Stochastic Certificate Kernel | `e1a76a74d612483a` |
| M4 | Topology Boolean Closure Kernel | `8a68bc95eee2eccc` |
| M5 | Boundary Type Theory Foundation Kernel | `a497c7668fafa52d` |
| M6 | Audit Manifest M1-M5 | `660bde6fe57e4498` |
| M7 | All-in-One Kernel M1-M5 | `f58f7c861b1f78ea` |
| M8 | Polyhedral Solver Kernel | `231180aaecaf372d` |
| M9 | Dynamic Generator Kernel | `f70e426f01c4eacf` |
| M10 | Final Audit Bundle M1-M9 | `6cee643452a78a80` |
| M11 | Monograph Integration Package | `d5df73b30f93cd9d` |
| M12 | Extended All-in-One Kernel | `486bae681a3f2392` |
| M13 | Solver Backend Importer | `69a21a366e3d20f9` |
| M14 | Categorical Morphism Kernel | `20dc9851cad6d1a9` |
| M15 | Publication Package | `306c3fe0e2f59486` |

# 13. Release Statement

BEC v2.0 is now assembled as a Lean-supported, audit-backed boundary-threshold framework with verified milestone kernels for universe formation, graph-based route licensing, compiler normal forms, stochastic certificate transfer, Boolean topology, Boundary Type Theory, polyhedral slack certificates, dynamic generator certificates, backend certificate importing, and categorical comparison.

The release is intentionally conservative. Its strength is the explicit distinction between drafted mathematical architecture, checked Lean kernels, external solver evidence, stochastic analytic assumptions, and publication claims.
