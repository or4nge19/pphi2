# `Tightness.lean` — Informal Summary

> **Source**: [`Pphi2/ContinuumLimit/Tightness.lean`](../../Pphi2/ContinuumLimit/Tightness.lean)
>
> **Generated**: 2026-04-12

## Overview
Proves the tightness of the family of continuum-embedded interacting measures $\{\nu_a\}_{a \in (0,1]}$ on $\mathcal{S}'(\mathbb{R}^d)$. The file now contains the full local route: first a uniform interacting second-moment bound, then integrability of squared evaluations under the pushed-forward interacting measures, and finally Mitoma-Chebyshev tightness via `configuration_tight_of_uniform_second_moments`.

## Status
**Main result**: `continuumMeasures_tight` proved
**Length**: 233 lines, 0 definitions + 3 theorems

---

### `continuum_second_moment_uniform` (theorem, proved)
For each test function $f$, there is a constant $C(f)$ such that
\[
\int (\omega f)^2\, d\nu_a \le C(f)
\]
uniformly for all spacings $a \in (0,1]$.

Proof outline:
1. Specialize the proved `interacting_moment_bound` at the quadratic moment.
2. Rewrite the Gaussian side as the embedded Gaussian continuum measure.
3. Bound that Gaussian second moment uniformly by `gaussian_second_moment_uniform`.

### `continuumMeasure_sq_integrable` (theorem, proved)
For every test function $f$, the observable $\omega \mapsto (\omega f)^2$ is integrable under each continuum-embedded interacting measure.

Proof outline:
1. Pull the integral back through `continuumMeasure = map latticeEmbedLift`.
2. Reduce to integrability of $(\omega g_f)^2$ under the interacting lattice measure.
3. Use the Gaussian pairing law plus the bounded-below interaction weight to transfer Gaussian integrability through the density.

### `continuumMeasures_tight` (theorem, proved)
For every $\varepsilon > 0$, there exists a compact set $K \subset \mathcal{S}'(\mathbb{R}^d)$ such that $\nu_a(K) \ge 1 - \varepsilon$ for all $a \in (0, 1]$.

Proof outline:
1. Supply the Dynin-Mityagin instance for `ContinuumTestFunction d` when `d > 0`.
2. Use `continuumMeasure_sq_integrable` to meet the integrability hypothesis in Mitoma-Chebyshev.
3. Feed `continuum_second_moment_uniform` into `configuration_tight_of_uniform_second_moments`.

**Dependencies**: `Hypercontractivity.lean`, `GaussianTightness.lean`, `GaussianField.Tightness`, Mitoma (1983).

---
*This file has **0** definitions and **3** theorems (all proved).*
