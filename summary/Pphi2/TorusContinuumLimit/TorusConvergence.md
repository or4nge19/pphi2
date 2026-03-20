# `TorusConvergence.lean` — Informal Summary

> **Source**: [`Pphi2/TorusContinuumLimit/TorusConvergence.lean`](../../Pphi2/TorusContinuumLimit/TorusConvergence.lean)
>
> **Generated**: 2026-03-20

## Overview
Applies Prokhorov's theorem to extract a weakly convergent subsequence from the tight family of torus Gaussian measures. Unlike the $\mathcal{S}'(\mathbb{R}^d)$ case (which needs topological axioms), here the **proved** `prokhorov_sequential` is used directly because Configuration(TorusTestFunction $L$) is Polish.

## Status
**Main result**: `torusGaussianLimit_exists` fully proved (0 axioms, 0 sorries)
**Length**: 85 lines, 0 definitions + 1 theorem

---

### `torusGaussianLimit_exists` (theorem, proved)
For $N \to \infty$, the torus-embedded Gaussian measures $\nu_{\text{GFF},N}$ have a weakly convergent subsequence. The limit is a probability measure on Configuration(TorusTestFunction $L$).

**Proved** from:
1. `torusContinuumMeasures_tight` (tightness)
2. `configuration_torus_polish` (Polish space)
3. `prokhorov_configuration` (proved Prokhorov extraction)

---
*This file has **0** definitions and **1** theorem (0 with sorry).*
