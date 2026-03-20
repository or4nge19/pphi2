# `GaussianTightness.lean` — Informal Summary

> **Source**: [`Pphi2/GaussianContinuumLimit/GaussianTightness.lean`](../../Pphi2/GaussianContinuumLimit/GaussianTightness.lean)
> **Generated**: 2026-03-20

## Overview
Shows that the family of continuum-embedded Gaussian measures $\{\nu_{\text{GFF},a}\}_{a \in (0,1]}$ is tight on $\mathcal{S}'(\mathbb{R}^d)$. The uniform second moment bound is proved; tightness via the Mitoma criterion is axiomatized.

## Status
**Main result**: Uniform second moment proved; tightness axiom
**Length**: 110 lines, 0 definitions + 1 theorem + 1 axiom

---

### `gaussian_second_moment_uniform` (theorem, proved)
$\int (\omega f)^2\, d\nu_{\text{GFF},a} \le C(f,m)$ uniformly in $a \in (0,1]$ and $N$. **Proved** from `embeddedTwoPoint_uniform_bound`.

### `gaussianContinuumMeasures_tight` (axiom)
The family $\{\nu_{\text{GFF},a}\}_{a \in (0,1]}$ is tight on $\mathcal{S}'(\mathbb{R}^d)$. Proof outline: uniform second moments $\to$ Chebyshev $\to$ 1D tightness $\to$ Mitoma criterion.

---
*This file has **0** definitions and **1** theorem (0 with sorry) + **1** axiom.*
