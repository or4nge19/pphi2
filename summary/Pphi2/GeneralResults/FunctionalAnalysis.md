# `FunctionalAnalysis.lean` -- Informal Summary

> **Source**: [`Pphi2/GeneralResults/FunctionalAnalysis.lean`](../../../Pphi2/GeneralResults/FunctionalAnalysis.lean)
>
> **Generated**: 2026-03-20

## Overview
Pure functional analysis results not specific to $P(\Phi)_2$: continuous Cesaro mean convergence, Schwartz function $L^p$ integrability, and a double-sum trigonometric identity for reflection positivity matrices. All candidates for upstreaming to Mathlib.

## Status
**Main result**: Fully proven (0 sorries)
**Length**: 219 lines, 0 definitions + 3 theorems

---

### `cesaro_set_integral_tendsto`
If $h : \mathbb{R} \to \mathbb{R}$ is measurable, bounded, and $h(t) \to L$ as $t \to +\infty$, then
$$\frac{1}{T}\int_0^T h(t)\,dt \to L \quad\text{as } T \to +\infty.$$
Proof splits $[0,T] = [0,R] \cup (R,T]$ where $|h(t) - L| < \varepsilon/2$ for $t \ge R$; the initial segment contributes $O(R/T) \to 0$.

### `schwartz_integrable_norm_rpow`
For any Schwartz function $f : \mathcal{S}(E, F)$ and $p > 0$: $\|f(\cdot)\|^p \in L^1$. Uses `SchwartzMap.eLpNorm_lt_top`.

### `rp_matrix_trig_identity`
For reals $a_i$, $b_j$ and coefficients $c_i$, $c_j$:
$$\sum_{ij} c_i c_j \cos(a_i - b_j) = \bigl(\sum_i c_i \cos a_i\bigr)\bigl(\sum_j c_j \cos b_j\bigr) + \bigl(\sum_i c_i \sin a_i\bigr)\bigl(\sum_j c_j \sin b_j\bigr)$$
Proved from $\cos(a-b) = \cos a \cos b + \sin a \sin b$ and bilinearity.

---
*This file has **0** definitions and **3** theorems/lemmas (0 with sorry).*
