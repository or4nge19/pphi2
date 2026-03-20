# `EmbeddedCovariance.lean` — Informal Summary

> **Source**: [`Pphi2/GaussianContinuumLimit/EmbeddedCovariance.lean`](../../Pphi2/GaussianContinuumLimit/EmbeddedCovariance.lean)
>
> **Generated**: 2026-03-20

## Overview
Defines the continuum-embedded Gaussian measure (pushforward of the lattice GFF under `latticeEmbedLift`), the embedded two-point function $\langle \Phi_a(f) \Phi_a(g) \rangle_{\text{GFF}}$, and the continuum Green's function bilinear form $G(f,g) = \int \hat{f}(k)\hat{g}(k)/(|k|^2 + m^2)\, dk/(2\pi)^d$. Provides algebraic identities connecting the two-point functions.

## Status
**Main result**: Fully proven (0 axioms, 0 sorries)
**Length**: 182 lines, 3 definitions + 3 theorems + 1 instance

---

### `gaussianContinuumMeasure`
```lean
def gaussianContinuumMeasure (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Measure (Configuration (ContinuumTestFunction d))
```
Pushforward $\nu_{\text{GFF},a} = (\tilde\iota_a)_* \mu_{\text{GFF},a}$.

### `gaussianContinuumMeasure_isProbability` (instance, proved)
$\nu_{\text{GFF},a}$ is a probability measure.

### `embeddedTwoPoint`
```lean
def embeddedTwoPoint (a mass : ℝ) ... (f g : ContinuumTestFunction d) : ℝ
```
Two-point function $\int \omega(f) \omega(g)\, d\nu_{\text{GFF},a}$.

### `continuumGreenBilinear`
```lean
def continuumGreenBilinear (mass : ℝ) (f g : ContinuumTestFunction d) : ℝ
```
Continuum Green's function $(2\pi)^{-d} \int \hat{f}(k)\hat{g}(k)/(|k|^2 + m^2)\, dk$.

### `embeddedTwoPoint_eq_covariance` (theorem, proved)
Rewrites the pushforward integral as a lattice Gaussian integral.

### `embeddedTwoPoint_eq_latticeSum` (theorem, proved)
$\langle\Phi_a(f),\Phi_a(g)\rangle = a^{2d} \sum_{x,y} C_a(x,y) f(ax) g(ay)$. **Proved** by expanding the product, swapping integral and sums, and applying the Gaussian cross-moment formula.

---
*This file has **3** definitions, **1** instance, and **3** theorems (0 with sorry).*
