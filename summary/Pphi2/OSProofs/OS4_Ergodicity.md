# `OS4_Ergodicity.lean` -- Informal Summary

> **Source**: [`Pphi2/OSProofs/OS4_Ergodicity.lean`](../../Pphi2/OSProofs/OS4_Ergodicity.lean)
> **Generated**: 2026-03-20

## Overview
Shows that exponential clustering implies ergodicity of the measure with respect to time translations, and that the vacuum is unique. Ergodicity proof: for a $T_R$-invariant set $A$, $|\mu(A) - \mu(A)^2| \le C e^{-mR}$ for all $R > 0$; taking $R \to \infty$ forces $\mu(A) \in \{0,1\}$.

## Status
**Main result**: Fully proven (0 sorry, 0 axioms)
**Length**: 265 lines, 0 definitions + 5 theorems

---

### `clustering_implies_ergodicity`
If $\mu$ satisfies exponential clustering w.r.t. translations $T_R$, then $\mu$ is ergodic: $T_R$-invariant sets have measure $0$ or $1$. Proved by setting $F = G = \mathbf{1}_A$, computing $|\mu(A) - \mu(A)^2| \le C e^{-mR} \to 0$, then $\mu(A)(1-\mu(A)) = 0$. Fully proved.

### `unique_vacuum`
On the lattice: uniqueness of the ground state from `transferOperator_ground_simple_spectral`. Fully proved.

### `exponential_mixing`
$\exists m > 0$ with $m \le m_{\mathrm{phys}}$, the measure is exponentially mixing. Immediate from `massGap_pos`. Fully proved.

### `os4_lattice`
The lattice interacting measure satisfies OS4: $0 < m_{\mathrm{phys}}$. Delegates to `massGap_pos`. Fully proved.

### `os4_lattice_from_gap`
Same as `os4_lattice`, stated to make the connection to the OS axiom framework explicit.

---
*This file has **0** definitions and **5** theorems (0 with sorry).*
