# `SmoothLowerBound.lean` -- Informal Summary

> **Source**: [`Pphi2/NelsonEstimate/SmoothLowerBound.lean`](../../../Pphi2/NelsonEstimate/SmoothLowerBound.lean)
> **Generated**: 2026-03-20

## Overview
Shows that the smooth part of the Wick-ordered interaction (after covariance splitting) is bounded below by a constant depending on $\log(1/T)$ but NOT on the lattice size $N$. Uses the pointwise bound $:x^4:_c \ge -6c^2$ and the volume identity $a^d \cdot |\Lambda| = L^d$ to get the $N$-independent bound $V_S \ge -6L^d c_S^2 \ge -C(1 + |\log T|)^2$.

## Status
**Main result**: Fully proven (0 sorries)
**Length**: 153 lines, 0 definitions + 4 theorems

---

### `site_interaction_lower_bound`
$a^d \cdot :(\varphi(x))^4:_c \ge -6 a^d c^2$ at a single lattice site.

### `smooth_interaction_lower_bound`
Summed over all sites: $V_S = a^d \sum_x :(\varphi_S(x))^4:_{c_S} \ge -6 a^d |\Lambda| c_S^2$.

### `smooth_interaction_lower_bound_volume`
Volume-independent version: with $a = L/N$, we have $a^d |\Lambda| = L^d$, so $V_S \ge -6L^d c_S^2$.

### `smooth_interaction_lower_bound_log`
Combined with `smoothVariance_le_log`: $V_S \ge -C(1 + |\log T|)^2$ where $C$ depends on $L$ and $m$ but NOT on $N$.

Depends on: `wickMonomial_four_lower_bound`, `smoothVariance_le_log`, `smoothCovEigenvalue_pos`.

---
*This file has **0** definitions and **4** theorems/lemmas (0 with sorry).*
