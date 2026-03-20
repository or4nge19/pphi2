# `JentzschProof.lean` -- Informal Summary

> **Source**: [`Pphi2/TransferMatrix/JentzschProof.lean`](../../Pphi2/TransferMatrix/JentzschProof.lean)
> **Generated**: 2026-03-20

## Overview
Full proof of Jentzsch's theorem for compact self-adjoint positivity-improving operators on $L^2(\mathbb{R}^n)$ via the variational absolute value trick (Courant-Hilbert / Barry Simon approach), avoiding Krein-Rutman / Banach lattice cone machinery. The proof proceeds in 7 phases: absolute value inequality, inner product inequality, $|f|$ is a ground state, ground state strict positivity, constant sign, simplicity, and spectral gap.

## Status
**Main result**: Fully proven (0 sorry)
**Length**: 1082 lines, 3 definitions + 10 theorems

---

### `IsPositivityPreserving`
```lean
def IsPositivityPreserving {n : N} (T : Lp R 2 volume ->L[R] Lp R 2 volume) : Prop
```
$T$ maps nonneg functions to nonneg functions: $f \ge 0 \implies Tf \ge 0$.

### `IsPositivityImproving`
```lean
def IsPositivityImproving {n : N} (T : Lp R 2 volume ->L[R] Lp R 2 volume) : Prop
```
$T$ maps nonneg nonzero functions to a.e. strictly positive functions (ae-filter version).

### `IsPositivityImproving'`
```lean
def IsPositivityImproving' {n : N} (T : Lp R 2 volume ->L[R] Lp R 2 volume) : Prop
```
Same as `IsPositivityImproving` but using $L^p$ lattice order ($0 \le f$, $f \ne 0$).

### `abs_apply_le_apply_abs` (Phase 1)
$|Tf| \le T|f|$ a.e. for positivity-preserving $T$. From $f = f^+ - f^-$, $|Tf| \le Tf^+ + Tf^- = T|f|$.

### `abs_inner_le_inner_abs` (Phase 2)
$|\langle f, Tf\rangle| \le \langle |f|, T|f|\rangle$. Integral triangle inequality + Phase 1.

### `abs_eigenvector_of_top_eigenvector` (Phase 3)
If $Tf = \lambda_0 f$, then $T|f| = \lambda_0|f|$. Rayleigh quotient equality forces $|f|$ to be a ground state.

### `ground_state_strictly_positive` (Phase 4)
Nonneg nonzero eigenvector of $\lambda_0 > 0$ is strictly positive a.e. From positivity-improving applied to $|f|$.

### `eigenvector_constant_sign` (Phase 5)
Every $\lambda_0$-eigenvector is either $> 0$ a.e. or $< 0$ a.e. Set $g = |f| - f \ge 0$; if $g \ne 0$ then $g > 0$ a.e. by Phase 4.

### `top_eigenvalue_simple` (Phase 6)
$\lambda_0$ has multiplicity 1. If $u, v$ are orthogonal $\lambda_0$-eigenvectors, both have constant sign, so $\langle u, v\rangle > 0$, contradicting orthogonality.

### `spectral_gap` (Phase 7)
$|\mu| < \lambda_0$ for $\mu \ne \lambda_0$. Uses $|\mu| \le \lambda_0$ from Phase 2; equality forces $\mu = -\lambda_0$ leading to the $p = |g|+g$, $q = |g|-g$ argument and contradiction.

### `jentzsch_theorem_proved`
Assembly of all 7 phases. Given compact, self-adjoint, positivity-improving $T$ with eigenbasis $|\iota| \ge 2$: finds $i_0$ with $\lambda(i_0) > 0$ simple and $|\lambda(i)| < \lambda(i_0)$ for $i \ne i_0$.

---
*This file has **3** definitions and **10** theorems (0 with sorry).*
