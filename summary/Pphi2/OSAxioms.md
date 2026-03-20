# `OSAxioms.lean` -- Informal Summary

> **Source**: [`Pphi2/OSAxioms.lean`](../../Pphi2/OSAxioms.lean)
>
> **Generated**: 2026-03-20

## Overview
Defines the five Osterwalder-Schrader axioms for probability measures on $\mathcal{S}'(\mathbb{R}^2)$. Sets up the spacetime ($\mathbb{R}^2$), test functions ($\mathcal{S}(\mathbb{R}^2)$), the generating functional $Z[f] = \int e^{i\langle\omega,f\rangle}\,d\mu$, the Euclidean group $E(2) = \mathbb{R}^2 \rtimes O(2)$ and its action on test functions, time reflection $\Theta$, and positive-time test functions. Bundles all five axioms into `SatisfiesFullOS`.

## Status
**Main result**: Definitions only (no proofs needed)
**Length**: 384 lines, 19 definitions + 3 theorems

---

### Type setup
- `SpaceTime2 := EuclideanSpace ℝ (Fin 2)`, `TestFunction2 := SchwartzMap SpaceTime2 ℝ`
- `FieldConfig2 := WeakDual ℝ (TestFunction2)` (tempered distributions)
- `TestFunction2ℂ := SchwartzMap SpaceTime2 ℂ` (complex test functions)

### `generatingFunctional`, `generatingFunctionalℂ`
$Z[f] = \int e^{i\omega(f)}\,d\mu$ (real) and $Z[J] = \int e^{i\langle\omega,J\rangle_\mathbb{C}}\,d\mu$ (complex).

### `schwartzRe`, `schwartzIm`
Extract real/imaginary parts of complex Schwartz functions as real Schwartz functions.

### `E2`, `euclideanAction2`, `euclideanAction2ℂ`
Euclidean motion $(R, t)$ with action $g \cdot x = R(x) + t$; pullback on test functions via `compCLMOfAntilipschitz`.

### `timeReflection2`, `compTimeReflection2`
Time reflection $(t, x) \mapsto (-t, x)$ and its pullback on Schwartz space.

### `SchwartzMap.translate`
Translation $f \mapsto f(\cdot - a)$.

### OS Axiom Definitions
- **`OS0_Analyticity`**: $Z[\sum z_i f_i]$ entire analytic in $z \in \mathbb{C}^n$.
- **`OS1_Regularity`**: $\|Z[J]\| \le e^{c(\|J\|_1 + \|J\|_p^p)}$.
- **`OS2_EuclideanInvariance`**: $Z[g \cdot f] = Z[f]$ for $g \in E(2)$.
- **`OS3_ReflectionPositivity`**: $\sum_{ij} c_i c_j \operatorname{Re}(Z[f_i - \Theta f_j]) \ge 0$.
- **`OS4_Clustering`**: $Z[f + T_a g] \to Z[f] \cdot Z[g]$ as $\|a\| \to \infty$.
- **`OS4_Ergodicity`**: Cesaro-averaged generating functional factors.

### `SatisfiesFullOS`
Structure bundling all five axioms.

---
*This file has **19** definitions and **3** theorems/lemmas (0 with sorry).*
