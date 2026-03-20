# `Bridge.lean` -- Informal Summary

> **Source**: [`Pphi2/Bridge.lean`](../../Pphi2/Bridge.lean)
> **Generated**: 2026-03-20

## Overview
Bridges the pphi2 lattice construction and a hypothetical Phi4 continuum construction, proving they produce the same measure on $\mathcal{S}'(\mathbb{R}^2)$ at weak coupling (via moment determinacy + Schwinger function agreement). Enables axiom transfer: OS2 (Euclidean invariance) from Phi4 to pphi2, and OS3 (reflection positivity) from pphi2 to Phi4, eliminating the hardest argument in each project.

## Status
**Main result**: Core results depend on 3 axioms (`measure_determined_by_schwinger`, `schwinger_agreement`, `os2_from_phi4`)
**Length**: 481 lines, 5 definitions + 7 theorems + 3 axioms

---

### Definitions
- `IsPphi2ContinuumLimit`: $\mu$ arises as weak limit of continuum-embedded lattice measures along $a_n \to 0$.
- `IsPhi4ContinuumLimit`: $\mu$ arises as infinite-volume limit of Phi4 finite-volume measures.
- `isPhi4`: Predicate for $\varphi^4$ interaction ($P(\tau) = \lambda\tau^4$).
- `IsWeakCoupling`: Coupling is small enough for cluster expansion convergence.

### `IsPphi2ContinuumLimit.toIsPphi2Limit`
Concrete continuum limit satisfies the abstract `IsPphi2Limit` predicate (definitional).

### Axioms
- **`measure_determined_by_schwinger`**: Probability measures with finite exponential moments are determined by their Schwinger functions (moment determinacy).
- **`schwinger_agreement`**: At weak coupling, pphi2 and Phi4 Schwinger functions agree.
- **`os2_from_phi4`**: The Phi4 continuum measure is $E(2)$-invariant (manifest in continuum).

### `same_continuum_measure`
$\mu_{\text{latt}} = \mu_{\text{cont}}$ at weak coupling. Proved from moment determinacy + Schwinger agreement.

### `os2_for_pphi2_via_phi4`
OS2 transferred to pphi2 via measure equality -- bypasses Ward identity.

### `os3_from_pphi2`
OS3 for pphi2's continuum limit via transfer matrix + weak limit inheritance.

### `os3_for_phi4_via_pphi2`
OS3 transferred to Phi4 via measure equality -- bypasses Dirichlet/Neumann bounds.

### `full_os_via_bridge`, `phi4_full_os_via_bridge`
Full OS axiom bundles using optimal proof sources from each project.

---
*This file has **5** definitions, **7** theorems, and **3** axioms.*
