# `TorusNuclearBridge.lean` — Informal Summary

> **Source**: [`Pphi2/TorusContinuumLimit/TorusNuclearBridge.lean`](../../Pphi2/TorusContinuumLimit/TorusNuclearBridge.lean)
>
> **Generated**: 2026-03-20

## Overview
Proves that `TorusTestFunction L` is Hilbert-nuclear (`IsHilbertNuclear`), separable, and nonempty. These are the topological prerequisites for the Bochner-Minlos theorem and the Prokhorov extraction on Configuration(TorusTestFunction $L$). The proof chains: DyninMityaginSpace $\to$ NuclearSpace $\to$ IsNuclear $\to$ IsHilbertNuclear.

## Status
**Main result**: Fully proven (0 axioms, 0 sorries)
**Length**: 84 lines, 0 definitions + 3 instances + 2 private theorems

---

### `nuclearSpace_to_isNuclear` (private theorem, proved)
Converts gaussian-field's `NuclearSpace` to bochner's `IsNuclear`. For $\mathbb{R}$-valued CLFs, $\|f(x)\| = |f(x)|$.

### `WithSeminorms.equiv` (private theorem, proved)
Reindexing a seminorm family by an equivalence preserves `WithSeminorms`.

### `torusTestFunction_isHilbertNuclear` (instance, proved)
`TorusTestFunction L` is Hilbert-nuclear. **Proved** via the chain: DyninMityaginSpace $\to$ NuclearSpace (gaussian-field) $\to$ IsNuclear (bridge) $\to$ IsHilbertNuclear (Pietsch bridge) with RapidDecaySeq's $\mathbb{N}$-indexed seminorms.

### `torusTestFunction_separableSpace` (instance, proved)
`TorusTestFunction L` is separable, via the countable Schauder basis.

### `Nonempty (TorusTestFunction L)` (instance)
Witnessed by $0$.

---
*This file has **0** definitions and **3** instances + **2** private theorems (0 with sorry).*
