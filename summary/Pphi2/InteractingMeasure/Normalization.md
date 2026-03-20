# `Normalization.lean` -- Informal Summary

> **Source**: [`Pphi2/InteractingMeasure/Normalization.lean`](../../../Pphi2/InteractingMeasure/Normalization.lean)
>
> **Generated**: 2026-03-20

## Overview
Further properties of the interacting lattice measure: integrability of observables, all polynomial moments of field evaluations, the FKG inequality for monotone observables, and boundedness of the generating functional. The FKG proof is the centerpiece, reducing to `fkg_perturbed` from `gaussian-field` via the single-site decomposition of $V_a$.

## Status
**Main result**: Fully proven (0 sorries)
**Length**: 406 lines, 0 definitions + 5 theorems

---

### `bounded_integrable_interacting`
Bounded measurable functions are integrable under $\mu_a$ (since $\mu_a$ is a probability measure).

### `field_second_moment_finite`
$\int |\omega(\delta_x)|^2\,d\mu_a < \infty$. Proved by dominating $|\omega(\delta_x)|^2 e^{-V}$ by $|\omega(\delta_x)|^2 e^B$ and using Gaussian integrability from `pairing_product_integrable`.

### `field_all_moments_finite`
$\int |\omega(\delta_x)|^p\,d\mu_a < \infty$ for all $p \in \mathbb{N}$. Uses `pairing_is_gaussian` + `integrable_pow_of_mem_interior_integrableExpSet` for Gaussian moment finiteness.

### `fkg_interacting`
For monotone functions $F, G$: $\mathbb{E}_{\mu_a}[FG] \ge \mathbb{E}_{\mu_a}[F] \cdot \mathbb{E}_{\mu_a}[G]$. Proved by converting integrability from $\mu_a$ to Gaussian + weight, applying `fkg_perturbed` (unnormalized FKG), then dividing by $Z^2$.

### `generating_functional_bounded`
$\left|\int \cos(\omega(f))\,d\mu_a\right| \le 1$ since $|\cos| \le 1$ and $\mu_a$ is a probability measure.

---
*This file has **0** definitions and **5** theorems/lemmas (0 with sorry).*
