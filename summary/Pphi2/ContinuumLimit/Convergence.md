# `Convergence.lean` — Informal Summary

> **Source**: [`Pphi2/ContinuumLimit/Convergence.lean`](../../Pphi2/ContinuumLimit/Convergence.lean)
>
> **Generated**: 2026-04-12

## Overview
Applies Prokhorov's theorem to extract a weakly convergent subsequence from the tight family of continuum-embedded measures. The file now uses the proved theorem `continuumMeasures_tight` from `Tightness.lean`, contains a fully proved sequential Prokhorov theorem for Polish spaces, a proved configuration-space extraction theorem, the fixed-`N` continuum extraction theorem `continuumLimit`, and two remaining substantive axioms for non-Gaussianity and the full `IsPphi2Limit` package.

## Status
**Main result**: `continuumLimit` proved; 2 axioms total
**Length**: 295 lines, 0 definitions + 3 theorems + 2 axioms

---

### `prokhorov_sequential` (theorem, proved)
On a Polish space $X$, if a sequence of probability measures $\{\mu_n\}$ is tight, then it has a weakly convergent subsequence. **Fully proved** from Mathlib.

### `prokhorov_configuration_sequential` (theorem, proved)
Sequential Prokhorov extraction on configuration space, derived from `prokhorov_sequential` and the proved tightness input specialized to the configuration space.

### `continuumLimit` (theorem, proved)
For any sequence of lattice spacings $a_n \to 0$, there exists a subsequence $a_{n_k}$ and a probability measure $\mu$ on $\mathcal{S}'(\mathbb{R}^d)$ such that $\nu_{a_{n_k}} \rightharpoonup \mu$ weakly.

### `continuumLimit_nonGaussian` (axiom)
The continuum limit is non-Gaussian for nontrivial $P$: there exists $f$ with $S_4(f,f,f,f) - 3 S_2(f,f)^2 \ne 0$ (nonzero connected four-point function).

### `pphi2_limit_exists` (axiom)
There exists a probability measure $\mu$ on $\mathcal{S}'(\mathbb{R}^2)$ satisfying `IsPphi2Limit`. This is the substantive plane-limit existence package needed downstream; the weaker fixed-`N` extraction theorem is `continuumLimit`.

---
*This file has **0** definitions and **3** theorems (all proved) + **2** axioms.*
