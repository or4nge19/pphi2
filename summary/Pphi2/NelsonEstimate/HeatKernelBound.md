# `HeatKernelBound.lean` -- Informal Summary

> **Source**: [`Pphi2/NelsonEstimate/HeatKernelBound.lean`](../../../Pphi2/NelsonEstimate/HeatKernelBound.lean)
>
> **Generated**: 2026-03-20

## Overview
The core analytic lemmas for Nelson's estimate. Proves Schwinger parametrization identities ($e^{-T\lambda}/\lambda = \int_T^\infty e^{-t\lambda}\,dt$ and $(1 - e^{-T\lambda})/\lambda = \int_0^T e^{-t\lambda}\,dt$), Jordan's inequality $\sin^2 x \ge (2/\pi)^2 x^2$, Gaussian sum bounds $\sum_k e^{-\alpha k^2} \le 1 + \sqrt{\pi/\alpha}$, and the heat kernel trace bound $H(t) = \sum_k e^{-t\lambda_k} \le C/t$ uniform in $N$. Then derives the eigenvalue sum bounds from the heat kernel bound.

## Status
**Main result**: Fully proven (0 sorries)
**Length**: 396 lines, 0 definitions + 11 theorems

---

### `schwinger_smooth`, `schwinger_rough`
Schwinger parametrization: $e^{-T\lambda}/\lambda = \int_T^\infty e^{-t\lambda}\,dt$ and $(1 - e^{-T\lambda})/\lambda = \int_0^T e^{-t\lambda}\,dt$. Proved via FTC with the antiderivative $-e^{-t\lambda}/\lambda$.

### `sin_sq_lower_bound`
$(2/\pi)^2 x^2 \le \sin^2 x$ for $|x| \le \pi/2$, from Mathlib's Jordan inequality.

### `gaussian_sum_bound`
$\sum_{k=-M}^M e^{-\alpha k^2} \le 1 + \sqrt{\pi/\alpha}$. Proved by splitting into $k=0$, positive, and negative parts, using the Gaussian integral $\int_0^\infty e^{-\alpha x^2}\,dx = \sqrt{\pi/\alpha}/2$.

### `heat_kernel_1d_bound`, `heat_kernel_trace_bound`
1D: $\sum_k e^{-t \cdot 4\sin^2(\pi k/N)/a^2} \le C(1 + 1/\sqrt{t})$. Full: $\sum_m e^{-t\lambda_m} \le C/t$ with $C = |\Lambda|/m^2$.

### `smoothVariance_from_heat_kernel`, `roughVariance_from_heat_kernel`
$\sum C_S(m) \le C(1 + |\log T|)$ and $\sum C_R(m)^2 \le CT$ derived from the heat kernel bound.

---
*This file has **0** definitions and **11** theorems/lemmas (0 with sorry).*
