# `Jentzsch.lean` -- Informal Summary

> **Source**: [`Pphi2/TransferMatrix/Jentzsch.lean`](../../Pphi2/TransferMatrix/Jentzsch.lean)
> **Generated**: 2026-03-20

## Overview
States Jentzsch's theorem (proved in `JentzschProof.lean`), proves the transfer operator is positivity-improving and strictly positive definite, shows $L^2(\mathbb{R}^{N_s})$ has nontrivial Hilbert bases, and derives all Perron-Frobenius properties: positive eigenvalues, ground-state simplicity, and spectral gap.

## Status
**Main result**: Fully proven (0 sorry, 0 axioms in this file)
**Length**: 515 lines, 0 definitions + 11 theorems

---

### `jentzsch_theorem`
For a compact, self-adjoint, positivity-improving operator $T$ on $L^2$ with $|\iota| \ge 2$: $\exists i_0$ with $\lambda(i_0) > 0$, $\lambda(i_0)$ simple, and $|\lambda(i)| < \lambda(i_0)$ for $i \ne i_0$. Delegates to `jentzsch_theorem_proved`.

### `transferOperator_positivityImproving`
$T$ is positivity-improving: if $f \ge 0$ a.e. and $f \not\equiv 0$, then $(Tf)(x) > 0$ a.e. Proved via the factorization $T = M_w \circ \mathrm{Conv}_G \circ M_w$ with $w > 0$, $G > 0$, and translation invariance of Lebesgue measure.

### `convolution_gaussian_strictly_positive_definite`
$\langle g, \mathrm{Conv}_G g\rangle > 0$ for $g \ne 0$. Delegates to `gaussian_conv_strictlyPD`.

### `transferOperator_strictly_positive_definite`
$\langle f, Tf\rangle > 0$ for $f \ne 0$. From $\langle f, Tf\rangle = \langle M_w f, \mathrm{Conv}_G(M_w f)\rangle$ (self-adjointness of $M_w$), injectivity of $M_w$ ($w > 0$), and Gaussian strict PD.

### `l2SpatialField_hilbertBasis_nontrivial`
Any Hilbert basis of $L^2(\mathbb{R}^{N_s})$ has $\ge 2$ elements. Proved by constructing orthogonal indicator functions on disjoint balls.

### `transferOperator_inner_nonneg`
$\langle f, Tf\rangle \ge 0$ for all $f$. Immediate from strict PD ($> 0$ for $f \ne 0$, $= 0$ for $f = 0$).

### `transferOperator_eigenvalues_pos`
All eigenvalues $\lambda_i > 0$. From $\langle b_i, Tb_i\rangle = \lambda_i \|b_i\|^2 = \lambda_i > 0$.

### `transferOperator_ground_simple`
$\exists i_0, i_1$ with $i_1 \ne i_0$ and $\lambda(i_1) < \lambda(i_0)$. Combines Jentzsch + nontriviality + eigenvalue positivity.

### `transferOperator_ground_simple_spectral`
Packaged spectral data with distinguished ground and first excited levels.

---
*This file has **0** definitions and **11** theorems (0 with sorry).*
