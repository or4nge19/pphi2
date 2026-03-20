# `PropagatorConvergence.lean` — Informal Summary

> **Source**: [`Pphi2/GaussianContinuumLimit/PropagatorConvergence.lean`](../../Pphi2/GaussianContinuumLimit/PropagatorConvergence.lean)
> **Generated**: 2026-03-20

## Overview
The main analytical content of the Gaussian continuum limit: proves the lattice propagator converges to the continuum Green's function, provides a uniform bound on $E[\Phi_a(f)^2]$, and establishes positivity $G(f,f) > 0$ for $f \ne 0$. The uniform bound is fully proved via a spectral eigenvalue argument and a Schwartz Riemann sum bound with explicit telescoping estimates.

## Status
**Main result**: `embeddedTwoPoint_uniform_bound` fully proved; 1 axiom
**Length**: 569 lines, 0 definitions + 4 theorems + 1 axiom + many private helpers

---

### `propagator_convergence` (axiom)
For $a_n \to 0$ with $N_n a_n \to \infty$: $\text{embeddedTwoPoint}(f,g) \to G(f,g)$. The lattice Riemann sum converges to the Fourier integral.

### `covariance_le_mass_inv_sq_norm` (private theorem, proved)
$\text{Cov}(h, h) \le m^{-2} \sum_x h(x)^2$, since all eigenvalues of $-\Delta + m^2$ satisfy $\lambda_k \ge m^2$. **Proved** by spectral decomposition + Parseval.

### `schwartz_riemann_sum_bound` (private theorem, proved)
$a^d \sum_x |f(ax)|^2 \le C$ uniformly in $a \in (0,1]$ and $N$, for Schwartz $f$. **Proved** via Schwartz decay $(1+\|y\|)^d |f(y)| \le S_f$, product factorization over coordinates, and 1D telescoping $\sum_n a/(1+an)^2 \le 2$.

### `embeddedTwoPoint_uniform_bound` (theorem, proved)
$E[\Phi_a(f)^2] \le m^{-2} C_f$ uniformly in $a$. **Proved** by combining `covariance_le_mass_inv_sq_norm` with `schwartz_riemann_sum_bound`.

### `continuumGreenBilinear_pos` (theorem, proved)
$G(f,f) > 0$ for $f \ne 0$. **Proved** since the integrand $|f(k)|^2/(|k|^2+m^2)$ is nonneg, and strictly positive on a set of positive measure (injectivity of Fourier transform on $\mathcal{S}$).

---
*This file has **0** definitions and **4** theorems (0 with sorry) + **1** axiom.*
