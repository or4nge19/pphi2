# `NelsonEstimate.lean` -- Informal Summary

> **Source**: [`Pphi2/NelsonEstimate/NelsonEstimate.lean`](../../../Pphi2/NelsonEstimate/NelsonEstimate.lean)
> **Generated**: 2026-03-20

## Overview
States and proves Nelson's exponential estimate on the lattice: $\int e^{-2V}\,d\mu_{\text{GFF}} \le K$ uniformly in the lattice size $N$. The proof uses the key identity $a^d \cdot |\Lambda| = L^d$ (physical volume is constant as $a \to 0$) combined with the uniform-in-$c$ lower bound on the Wick polynomial from `wickPolynomial_uniform_bounded_below`.

## Status
**Main result**: Fully proven (0 sorries)
**Length**: 144 lines, 0 definitions + 1 theorem

---

### `nelson_exponential_estimate_lattice`
For the $P(\varphi)_2$ lattice theory on the 2D torus of size $L$ with spacing $a = L/N$ and mass $m > 0$:
$$\int \left(e^{-V_a(\omega)}\right)^2\,d\mu_{\text{GFF}} \le K$$
where $K = e^{2L^2 A}$ depends on $P$, $L$, $m$ but NOT on $N$. The proof exploits $a^2 \cdot N^2 = L^2$, so the pointwise bound $V(\omega) \ge -L^2 A$ is uniform in $N$.

Depends on: `wickPolynomial_uniform_bounded_below`, `wickConstant_le_inv_mass_sq`, `wickConstant_pos`, `circleSpacing_pos`.

---
*This file has **0** definitions and **1** theorem (0 with sorry).*
