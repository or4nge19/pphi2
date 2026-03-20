# `Osgood2.lean` -- Informal Summary

> **Source**: [`Pphi2/GeneralResults/Osgood/Osgood2.lean`](../../../../Pphi2/GeneralResults/Osgood/Osgood2.lean)
> **Generated**: 2026-03-20

## Overview
Adapted from Geoffrey Irving's `girving/ray`. Proves Osgood's lemma for two complex variables: a continuous, separately analytic function $f : \mathbb{C}^2 \to E$ is jointly analytic. The proof constructs the 2D Cauchy power series using iterated contour integrals, shows it converges geometrically within the bidisc, and sums to $f$ via iterated Cauchy integral formulas.

## Status
**Main result**: Fully proven (0 sorries)
**Length**: 619 lines, 3 definitions + 20 theorems (approx.)

---

### `Separate` (structure)
```lean
structure Separate (f : ℂ × ℂ → E) (c0 c1 : ℂ) (r b : ℝ) (s : Set (ℂ × ℂ)) : Prop
```
Bundled hypotheses: $f$ is continuous on $s$, separately analytic in each variable, bounded by $b$ on the product sphere, with $\overline{B}(c, r) \subseteq s$.

### `Separate.series2Coeff`
The $(n_0, n_1)$-th 2D Cauchy coefficient: iterated contour integrals $(2\pi i)^{-2} \oint\oint (z_0-c_0)^{-n_0-1}(z_1-c_1)^{-n_1-1} f\,dz_0\,dz_1$.

### `series2`
The formal 2D power series: $N$-th coefficient is the antidiagonal sum $\sum_{n_0+n_1=N} \text{termCmmap}(\text{coeff}_{n_0,n_1})$.

### `osgood_h`
$f$ has a power series on the ball of radius $r$: `HasFPowerSeriesOnBall f (series2 h) (c0,c1) r`. Core result.

### `osgood`
If $f : \mathbb{C}^2 \to E$ is continuous on open $s$ and separately analytic, then $f$ is jointly analytic on $s$. Applies `osgood_h` locally.

### `osgood_at`
Pointwise version: separate analyticity near a point implies joint analyticity at that point.

---
*This file has **3** definitions and approximately **20** theorems/lemmas (0 with sorry).*
