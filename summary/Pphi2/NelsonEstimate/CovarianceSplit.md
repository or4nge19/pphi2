# `CovarianceSplit.lean` -- Informal Summary

> **Source**: [`Pphi2/NelsonEstimate/CovarianceSplit.lean`](../../../Pphi2/NelsonEstimate/CovarianceSplit.lean)
> **Generated**: 2026-03-20

## Overview
Defines the heat-kernel (Schwinger parametrization) splitting of the lattice GFF covariance into smooth and rough parts at Fourier mode level: $C(k)^{-1} = C_S(T,k) + C_R(T,k)$ where $C_S = e^{-T\lambda_k}/\lambda_k$ (low frequency) and $C_R = (1 - e^{-T\lambda_k})/\lambda_k$ (high frequency). Proves the splitting identity, variance bounds ($c_S \le O(|\log T|)$, $\sum C_R^2 \le O(T)$), and positivity of both parts.

## Status
**Main result**: Fully proven (0 sorries)
**Length**: 202 lines, 4 definitions + 8 theorems

---

### `smoothCovEigenvalue`, `roughCovEigenvalue`
```lean
def smoothCovEigenvalue (T : ℝ) (m : ℕ) : ℝ
def roughCovEigenvalue (T : ℝ) (m : ℕ) : ℝ
```
$C_S(T,m) = e^{-T\lambda_m}/\lambda_m$ and $C_R(T,m) = (1 - e^{-T\lambda_m})/\lambda_m$.

### `covariance_split`
$\lambda_m^{-1} = C_S(T,m) + C_R(T,m)$.

### `smoothWickConstant`, `roughWickConstant`
Averages of $C_S$ and $C_R$ over Fourier modes.

### `wickConstant_split`
$c_a = c_S + c_R$.

### `smoothVariance_le_log`
$c_S \le C \cdot (1 + |\log T|)$ for $d = 2$, since each $C_S(k) \le 1/\lambda_k \le 1/m^2$.

### `roughCovEigenvalue_le_T`
$C_R(T, m) \le T$ from the elementary bound $(1 - e^{-x})/x \le 1$.

### `roughCovariance_sq_summable`
$\frac{1}{|\Lambda|}\sum C_R(m)^2 \le T \cdot c_a$, since $C_R^2 \le T \cdot C_R \le T/\lambda_m$.

### `smoothCovEigenvalue_pos`, `roughCovEigenvalue_pos`
Both parts are strictly positive for $T > 0$.

---
*This file has **4** definitions and **8** theorems/lemmas (0 with sorry).*
