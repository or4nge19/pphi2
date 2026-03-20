# `Tightness.lean` — Informal Summary

> **Source**: [`Pphi2/ContinuumLimit/Tightness.lean`](../../Pphi2/ContinuumLimit/Tightness.lean)
>
> **Generated**: 2026-03-20

## Overview
States the tightness of the family of continuum-embedded interacting measures $\{\nu_a\}_{a \in (0,1]}$ on $\mathcal{S}'(\mathbb{R}^d)$. This is the key prerequisite for Prokhorov extraction. The proof is axiomatized, relying on Mitoma's criterion (tightness of 1D projections from uniform second moment bounds) fed by hypercontractive estimates.

## Status
**Main result**: 1 axiom (tightness)
**Length**: 88 lines, 0 definitions + 1 axiom

---

### `continuumMeasures_tight` (axiom)
For every $\varepsilon > 0$, there exists a compact set $K \subset \mathcal{S}'(\mathbb{R}^d)$ such that $\nu_a(K) \ge 1 - \varepsilon$ for all $a \in (0, 1]$.

Proof outline:
1. By Mitoma's criterion, tightness of measures on $\mathcal{S}'$ reduces to tightness of 1D projections.
2. Chebyshev's inequality reduces 1D tightness to uniform second moment bounds $\sup_a \int |\Phi_a(f)|^2 \, d\nu_a < \infty$.
3. The uniform bound is provided by the hypercontractive estimate (from `Hypercontractivity.lean`).

**Dependencies**: `Hypercontractivity.lean`, Mitoma (1983).

---
*This file has **0** definitions and **1** axiom (1 unproved).*
