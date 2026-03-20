# `AxiomInheritance.lean` — Informal Summary

> **Source**: [`Pphi2/ContinuumLimit/AxiomInheritance.lean`](../../Pphi2/ContinuumLimit/AxiomInheritance.lean)
>
> **Generated**: 2026-03-20

## Overview
Shows that OS axioms verified on the lattice transfer to the continuum limit measure $\mu = \lim \nu_{a_n}$. Contains a proved OS1 regularity result (trivial $|\cos| \le 1$ bound), a time reflection map on $\mathcal{S}'(\mathbb{R}^2)$, and an axiom for OS3 reflection positivity inheritance.

## Status
**Main result**: OS1 proved; OS3 inheritance axiomatized
**Length**: 165 lines, 4 definitions + 2 theorems + 1 axiom

---

### `os1_inheritance` (theorem, proved)
For any probability measure $\mu$, $|\int \cos(\omega(f))\, d\mu| \le 1$. **Proved** by $|\cos| \le 1$ and triangle inequality.

### `timeReflLinear`, `timeReflCLE`, `continuumTimeReflection`
Time reflection $(t, x) \mapsto (-t, x)$ as a linear map, a continuous linear equivalence on $\mathbb{R}^2$, and the induced CLM on $\mathcal{S}(\mathbb{R}^2)$ via `SchwartzMap.compCLMOfContinuousLinearEquiv`.

### `distribTimeReflection`
```lean
def distribTimeReflection : Configuration (ContinuumTestFunction 2) →
    Configuration (ContinuumTestFunction 2)
```
Time reflection on distributions: $(\Theta^* \omega)(f) = \omega(\Theta f)$.

### `distribTimeReflection_apply` (simp lemma, proved)
$(\Theta^* \omega)(f) = \omega(\Theta f)$.

### `os3_inheritance` (axiom)
For any bounded continuous $F$ depending on positive-time evaluations, $\int F(\omega) F(\Theta^* \omega)\, d\mu \ge 0$. This is the abstract reflection positivity condition inherited via weak limits. Requires `IsPphi2Limit`.

**Dependencies**: `OS3_RP_Inheritance.lean`, `OS4_MassGap.lean`.

---
*This file has **4** definitions and **2** theorems (0 with sorry) + **1** axiom.*
