# `RoughErrorBound.lean` -- Informal Summary

> **Source**: [`Pphi2/NelsonEstimate/RoughErrorBound.lean`](../../../Pphi2/NelsonEstimate/RoughErrorBound.lean)
> **Generated**: 2026-03-20

## Overview
Placeholder file for the hypercontractivity bound on the rough error. After covariance splitting, the rough error $E_R$ contains all cross-terms from the Wick binomial expansion. The intended results are: (1) $\mathbb{E}[E_R^2] \le C T^{1/2}$, (2) $\|E_R\|_p \le C p^2 T^{\delta/2}$ via hypercontractivity, and (3) the stretched-exponential tail bound $P(|E_R| > \lambda) \le e^{-c\lambda^{1/2}/T^{1/8}}$. All three theorems currently have `True` conclusions (placeholders).

## Status
**Main result**: Placeholder (all conclusions are `True`)
**Length**: 109 lines, 0 definitions + 3 theorems

---

### `rough_error_variance`
$\exists C > 0$ and ... (placeholder `True`). Intended: $\mathbb{E}[E_R^2] \le C \cdot T^{1/2}$.

### `rough_error_Lp_bound`
$\exists C > 0$ and ... (placeholder `True`). Intended: $\|E_R\|_p \le C p^2 T^{\delta/2}$ via Nelson's hypercontractivity.

### `rough_error_tail_bound`
$\exists c > 0$ and ... (placeholder `True`). Intended: $P(|E_R| > \lambda) \le e^{-c\lambda^{1/2}T^{-1/8}}$ from Chebyshev optimization.

---
*This file has **0** definitions and **3** theorems/lemmas (0 with sorry).*
