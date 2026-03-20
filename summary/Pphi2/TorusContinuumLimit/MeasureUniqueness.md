# `MeasureUniqueness.lean` — Informal Summary

> **Source**: [`Pphi2/TorusContinuumLimit/MeasureUniqueness.lean`](../../Pphi2/TorusContinuumLimit/MeasureUniqueness.lean)
>
> **Generated**: 2026-03-20

## Overview
Proves that two centered Gaussian probability measures on Configuration($E$) with the same covariance must be equal. This is a general result for any `DyninMityaginSpace`. The proof combines MGF matching $\to$ 1D marginal equality (via complex MGF analytic continuation and `Measure.ext_of_complexMGF_eq`) $\to$ finite-dimensional marginals (Cramer-Wold via `ext_of_charFunDual`) $\to$ full measure equality (Kolmogorov uniqueness via `IsProjectiveLimit.unique`).

## Status
**Main result**: `gaussian_measure_unique_of_covariance` fully proved (0 axioms, 0 sorries)
**Length**: 370 lines, 0 definitions + 5 theorems

---

### `mgf_eq_of_covariance` (theorem, proved)
If two Gaussian measures have the same covariance, their moment generating functions agree on all test functions: $\int e^{\omega(f)}\, d\mu_1 = \int e^{\omega(f)}\, d\mu_2$.

### `mgf_at_scaled` (theorem, proved)
For a Gaussian measure, $\int e^{t \omega(f)}\, d\mu = \exp(t^2 \sigma^2(f)/2)$ where $\sigma^2(f) = \int (\omega f)^2\, d\mu$.

### `eval_map_eq_of_covariance` (theorem, proved)
Same covariance implies same 1D marginals for all test functions. **Proved** by matching real MGFs to `gaussianReal`, analytically continuing to complex MGFs via `eqOn_complexMGF_of_mgf`, and applying `Measure.ext_of_complexMGF_eq`.

### `pushforward_eq_of_eval_eq` (theorem, proved)
Equal 1D marginals for all $f : E$ imply equal pushforward measures on $\mathbb{R}^{\mathbb{N}}$ via `configBasisEval`. **Proved** by Cramer-Wold (`ext_of_charFunDual` for finite-dim marginals) + Kolmogorov uniqueness (`IsProjectiveLimit.unique`).

### `gaussian_measure_unique_of_covariance` (theorem, proved)
**Main theorem**: Two centered Gaussian probability measures on Configuration($E$) with the same covariance are equal. **Proved** by pulling back from $\mathbb{R}^{\mathbb{N}}$ using `instMeasurableSpaceConfiguration_eq_comap`.

---
*This file has **0** definitions and **5** theorems (0 with sorry).*
