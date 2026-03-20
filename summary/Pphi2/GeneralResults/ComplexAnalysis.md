# `ComplexAnalysis.lean` -- Informal Summary

> **Source**: [`Pphi2/GeneralResults/ComplexAnalysis.lean`](../../../Pphi2/GeneralResults/ComplexAnalysis.lean)
> **Generated**: 2026-03-20

## Overview
Proves analyticity of parameter-dependent integrals: if $z \mapsto F(z, \omega)$ is entire for each $\omega$ and dominated by a locally uniform integrable bound, then $z \mapsto \int F(z,\omega)\,d\mu$ is entire on $\mathbb{C}^n$. The proof combines one-variable differentiability under the integral sign (Cauchy estimates + `hasDerivAt_integral_of_dominated_loc_of_deriv_le`), continuity via dominated convergence, and Osgood's lemma (separate analyticity + continuity = joint analyticity).

## Status
**Main result**: Fully proven (0 sorries)
**Length**: 282 lines, 0 definitions + 5 theorems

---

### `ComplexAnalysis.osgood_separately_analytic`
A continuous function $f : \mathbb{C}^n \to \mathbb{C}$ that is separately analytic in each coordinate is jointly analytic. Wrapper for `OsgoodN.lean`.

### `analyticAt_update`
The map $t \mapsto \texttt{update}\; z_0\; j\; t$ is analytic $\mathbb{C} \to (\texttt{Fin}\;n \to \mathbb{C})$ (affine embedding of a coordinate line).

### `differentiable_one_var_integral`
If $G(\cdot, \omega)$ is entire for each $\omega$ with compact domination, then $z \mapsto \int G(z,\omega)\,d\mu$ is differentiable on $\mathbb{C}$. Uses Cauchy estimates for the derivative bound, countable dense subset for ae swapping, and `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

### `continuous_integral_of_compact_dom`
$z \mapsto \int F(z,\omega)\,d\mu$ is continuous under pointwise continuity + locally uniform domination (dominated convergence).

### `analyticOnNhd_integral`
The main theorem: $z \mapsto \int F(z,\omega)\,d\mu$ is entire analytic on $\mathbb{C}^n$. Combines separate analyticity (from one-variable result) + continuity (from dominated convergence) via Osgood's lemma.

---
*This file has **0** definitions and **5** theorems/lemmas (0 with sorry).*
