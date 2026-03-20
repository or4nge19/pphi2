# `TorusGaussianLimit.lean` — Informal Summary

> **Source**: [`Pphi2/TorusContinuumLimit/TorusGaussianLimit.lean`](../../Pphi2/TorusContinuumLimit/TorusGaussianLimit.lean)
>
> **Generated**: 2026-03-20

## Overview
Identifies the weak limit from `torusGaussianLimit_exists` as a Gaussian measure with the correct covariance (the torus continuum Green's function $G_L$). Proves that weak limits of lattice Gaussians are Gaussian (via 1D pushforward matching + weak convergence of cos/sin integrals), defines the `IsTorusGaussianContinuumLimit` predicate, establishes covariance identification, proves $\mathbb{Z}_2$ symmetry of the limit, uniqueness of Gaussian measures from covariance, and the full convergence theorem `torusGaussianLimit_converges`. All results fully proved.

## Status
**Main result**: `torusGaussianLimit_converges` fully proved (0 axioms, 0 sorries)
**Length**: 1190 lines, 1 structure + 14 theorems

---

### `pushforward_eval_gaussianReal` (private theorem, proved)
Each 1D pushforward of the Gaussian limit is $N(0, \sigma^2)$ where $\sigma^2 = \int (\omega f)^2\, d\mu$. **Proved** via real MGF matching + complex MGF analytic continuation + `ext_of_complexMGF_eq`.

### `weakLimit_cos_conv` (private theorem, proved)
Weak convergence gives $\int \cos(\omega(f))\, d\mu_n \to \int \cos(\omega(f))\, d\mu$.

### `weakLimit_sin_zero` (private theorem, proved)
By $\mathbb{Z}_2$ symmetry, $\int \sin(\omega(f))\, d\mu = 0$.

### `weakLimit_centered_gaussianReal` (theorem, proved)
The 1D marginals of the weak limit equal $N(0, G_L(f,f))$ for each test function $f$.

### `torusGaussianLimit_isGaussian` (theorem, proved)
Weak limits of torus lattice Gaussians are Gaussian: $\int e^{\omega(f)}\, d\mu = \exp(\frac{1}{2}\int (\omega f)^2\, d\mu)$ for all $f$. **Proved** from the 1D Gaussian identification + MGF matching.

### `IsTorusGaussianContinuumLimit` (structure)
```lean
structure IsTorusGaussianContinuumLimit (μ : ...) (mass : ℝ) (hmass : 0 < mass) : Prop
```
Predicate: $\mu$ is a probability measure, Gaussian ($\int e^{\omega f}\, d\mu = \exp(\frac{1}{2}\int (\omega f)^2\, d\mu)$), has covariance $= G_L(f,f)$, and is $\mathbb{Z}_2$-symmetric.

### `torusGaussianMeasure_isGaussian` (theorem, proved)
Each lattice Gaussian measure satisfies the Gaussian MGF identity.

### `torusLimit_covariance_eq` (theorem, proved)
The covariance of the weak limit equals the continuum Green's function: $\int (\omega f)^2\, d\mu = G_L(f,f)$.

### `gaussian_measure_unique_of_covariance` (theorem, proved)
Two centered Gaussian probability measures with the same covariance are equal. Uses the uniqueness theorem from `MeasureUniqueness.lean`.

### `configuration_neg_apply` (theorem, proved)
Negation in configuration space: $(-\omega)(f) = -\omega(f)$.

### `torusGaussianMeasure_z2_symmetric` (theorem, proved)
Each lattice Gaussian measure is $\mathbb{Z}_2$-symmetric: $\mu \circ (-)^{-1} = \mu$.

### `z2_symmetric_of_weakLimit` (theorem, proved)
$\mathbb{Z}_2$ symmetry is inherited by the weak limit.

### `torusGaussianLimit_fullConvergence` (theorem, proved)
Full convergence: there exist a subsequence and a unique Gaussian limit measure satisfying `IsTorusGaussianContinuumLimit`.

### `torusGaussianLimit_converges` (theorem, proved)
Master convergence theorem: produces a subsequence, the limit measure, its `IsTorusGaussianContinuumLimit` predicate, and the weak convergence statement.

### `torusGaussianLimit_nontrivial` (theorem, proved)
$\int (\omega f)^2\, d\mu > 0$ for $f \ne 0$.

---
*This file has **1** structure and **14** theorems (0 with sorry).*
