# `OS3_RP_Inheritance.lean` -- Informal Summary

> **Source**: [`Pphi2/OSProofs/OS3_RP_Inheritance.lean`](../../Pphi2/OSProofs/OS3_RP_Inheritance.lean)
> **Generated**: 2026-03-20

## Overview
Shows that reflection positivity (OS3) is preserved under weak convergence of measures. This is a general topological fact: if $\mu_n \to \mu$ weakly and each $\mu_n$ is RP, then $\mu$ is RP. The key step is that $\phi \mapsto F(\phi) F(\Theta\phi)$ is bounded continuous when $F$ is, so weak convergence applies to each RP integrand.

## Status
**Main result**: Fully proven (0 sorry, 0 axioms)
**Length**: 143 lines, 1 definition + 2 theorems

---

### `IsRP`
```lean
def IsRP (mu : Measure X) (Theta : X -> X) (S : Set (X -> R)) : Prop :=
  forall F in S, integral x, F x * F (Theta x) d mu >= 0
```
Abstract reflection positivity: $\int F(x) F(\Theta x)\,d\mu \ge 0$ for all $F \in S$.

### `rp_closed_under_weak_limit`
If $\{\mu_n\}$ are RP measures converging weakly to $\mu$, then $\mu$ is RP. Proof: $x \mapsto F(x) F(\Theta x)$ is bounded continuous, so $\int F F \circ \Theta\,d\mu_n \to \int F F \circ \Theta\,d\mu$. Each term $\ge 0$, so the limit $\ge 0$ by `ge_of_tendsto`. Fully proved.

### `continuum_rp_from_lattice`
Specialization: RP transfers from lattice to continuum limit. Immediate from `rp_closed_under_weak_limit`. Fully proved.

---
*This file has **1** definition and **2** theorems (0 with sorry).*
