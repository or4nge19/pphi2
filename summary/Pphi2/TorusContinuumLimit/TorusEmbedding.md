# `TorusEmbedding.lean` — Informal Summary

> **Source**: [`Pphi2/TorusContinuumLimit/TorusEmbedding.lean`](../../Pphi2/TorusContinuumLimit/TorusEmbedding.lean)
> **Generated**: 2026-03-20

## Overview
Defines the torus-specific lattice-to-continuum embedding: lattice fields on $(\mathbb{Z}/N\mathbb{Z})^2$ with spacing $a = L/N$ are embedded into Configuration(TorusTestFunction $L$) via `torusEmbedCLM` (from gaussian-field). Also defines the pushforward Gaussian measure, the embedded two-point function, and the continuum Green's function on $T^2_L$.

## Status
**Main result**: Fully proven (0 axioms, 0 sorries)
**Length**: 131 lines, 5 definitions + 1 theorem + 1 instance

---

### `torusEmbedLift (N : ℕ) [NeZero N]`
```lean
def torusEmbedLift (N : ℕ) [NeZero N] :
    Configuration (FinLatticeField 2 N) → Configuration (TorusTestFunction L)
```
Lifts lattice configurations to torus configurations by extracting $\omega(\delta_x)$ and embedding via `torusEmbedCLM`.

### `torusEmbedLift_measurable` (theorem, proved)
The torus embedding lift is measurable. **Proved** by showing each evaluation is a finite sum of measurable functions.

### `torusContinuumMeasure`
```lean
def torusContinuumMeasure (N : ℕ) [NeZero N] (mass : ℝ) (hmass : 0 < mass) :
    Measure (Configuration (TorusTestFunction L))
```
Pushforward $\nu_{\text{GFF},N} = (\tilde\iota_N)_* \mu_{\text{GFF},N}$.

### `torusContinuumMeasure_isProbability` (instance, proved)

### `torusEmbeddedTwoPoint`
```lean
def torusEmbeddedTwoPoint (N : ℕ) [NeZero N] (mass : ℝ) (hmass : 0 < mass)
    (f g : TorusTestFunction L) : ℝ
```
Two-point function $\int \omega(f) \omega(g)\, d\nu_{\text{GFF},N}$.

### `torusContinuumGreen`
```lean
def torusContinuumGreen (mass : ℝ) (hmass : 0 < mass) (f g : TorusTestFunction L) : ℝ
```
Continuum Green's function on $T^2_L$: spectral sum $G_L(f,g) = \sum_n \hat{f}(n)\hat{g}(n)/((2\pi n/L)^2 + m^2)$.

---
*This file has **5** definitions, **1** instance, and **1** theorem (0 with sorry).*
