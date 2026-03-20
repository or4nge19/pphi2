# `TorusPropagatorConvergence.lean` — Informal Summary

> **Source**: [`Pphi2/TorusContinuumLimit/TorusPropagatorConvergence.lean`](../../Pphi2/TorusContinuumLimit/TorusPropagatorConvergence.lean)
> **Generated**: 2026-03-20

## Overview
The main analytical content of the torus Gaussian continuum limit. Proves the lattice Green's function on $T^2_L$ converges to the continuum Green's function as $N \to \infty$ (pure UV limit, $L$ fixed). Also proves the uniform bound $E[\Phi_N(f)^2] \le C$, positivity $G_L(f,f) > 0$, the eigenvalue lower bound $\lambda_k \ge m^2$, and the Riemann sum bound for torus test functions. All results are fully proved.

## Status
**Main result**: All proved (0 axioms, 0 sorries)
**Length**: 586 lines, 1 definition + 13 theorems + many private helpers

---

### `latticeTestFn (N : ℕ) (f : TorusTestFunction L)`
```lean
def latticeTestFn (N : ℕ) [NeZero N] (f : TorusTestFunction L) : FinLatticeField 2 N
```
The lattice field induced by evaluating a torus test function at lattice sites.

### `torusEmbedLift_eval_eq` (theorem, proved)
$(\tilde\iota_N \omega)(f) = \omega(\iota^* f)$ where $\iota^* f$ is the pullback lattice test function.

### `torusEmbeddedTwoPoint_eq_spectral_sum` (theorem, proved)
$\langle\Phi_N(f), \Phi_N(g)\rangle = \sum_k \lambda_k^{-1} c_k(\iota^* f) c_k(\iota^* g)$.

### `torus_propagator_convergence` (theorem, proved)
$\text{torusEmbeddedTwoPoint}(f,g) \to G_L(f,g)$ as $N \to \infty$. **Proved** via `lattice_green_tendsto_continuum` (mode-by-mode convergence + dominated convergence).

### `massEigenvalues_ge_mass_sq` (theorem, proved)
$\lambda_k \ge m^2$ for all $k$. **Proved** by spectral decomposition: $\langle e_k, (-\Delta+m^2)e_k\rangle \ge m^2$ since $-\Delta \ge 0$.

### `covariance_inner_le_mass_inv_sq_norm_sq` (theorem, proved)
$\langle Tg, Tg\rangle \le m^{-2} \sum_x g(x)^2$. **Proved** from eigenvalue bound + Parseval.

### `latticeTestFn_norm_sq_bounded` (theorem, proved)
$\sum_x (\iota^* f)(x)^2 \le C$ uniformly in $N$. **Proved** via DyninMityaginSpace expansion, Fourier basis bounds, and cancellation of $N$.

### `torusEmbeddedTwoPoint_uniform_bound` (theorem, proved)
$E[\Phi_N(f)^2] \le m^{-2} C_f$ uniformly in $N$.

### `torusContinuumGreen_pos` / `torusContinuumGreen_nonneg` (theorems, proved)
$G_L(f,f) > 0$ for $f \ne 0$; $G_L(f,f) \ge 0$ for all $f$.

---
*This file has **1** definition and **13** theorems (0 with sorry).*
