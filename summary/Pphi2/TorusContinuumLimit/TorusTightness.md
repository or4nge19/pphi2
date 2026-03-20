# `TorusTightness.lean` — Informal Summary

> **Source**: [`Pphi2/TorusContinuumLimit/TorusTightness.lean`](../../Pphi2/TorusContinuumLimit/TorusTightness.lean)
> **Generated**: 2026-03-20

## Overview
Shows that the family of torus-embedded Gaussian measures $\{\nu_{\text{GFF},N}\}_{N \ge 1}$ is tight on Configuration(TorusTestFunction $L$). The uniform second moment bound is proved, and tightness is derived from the Mitoma-Chebyshev criterion (`configuration_tight_of_uniform_second_moments` from gaussian-field).

## Status
**Main result**: `torusContinuumMeasures_tight` fully proved (0 axioms, 0 sorries)
**Length**: 126 lines, 0 definitions + 2 theorems

---

### `torus_second_moment_uniform` (theorem, proved)
$\int (\omega f)^2\, d\nu_{\text{GFF},N} \le C(f,L,m)$ uniformly in $N$. **Proved** from `torusEmbeddedTwoPoint_uniform_bound`.

### `torusContinuumMeasures_tight` (theorem, proved)
The family $\{\nu_{\text{GFF},N}\}_{N \ge 1}$ is tight. **Proved** by applying `configuration_tight_of_uniform_second_moments` with the uniform second moment bounds, nuclearity of `TorusTestFunction L`, and lattice Gaussian integrability.

---
*This file has **0** definitions and **2** theorems (0 with sorry).*
