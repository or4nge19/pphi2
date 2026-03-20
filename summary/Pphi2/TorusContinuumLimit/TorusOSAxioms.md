# `TorusOSAxioms.lean` — Informal Summary

> **Source**: [`Pphi2/TorusContinuumLimit/TorusOSAxioms.lean`](../../Pphi2/TorusContinuumLimit/TorusOSAxioms.lean)
>
> **Generated**: 2026-03-20

## Overview
Defines and proves the Osterwalder-Schrader axioms OS0-OS2 for the torus Gaussian continuum limit measure. Contains the generating functional definitions, the characteristic functional formula $E[e^{i\omega(f)}] = \exp(-\frac{1}{2}G_L(f,f))$ proved via complex MGF analytic continuation, the multi-variable identity theorem for entire functions, OS0 analyticity via `analyticOnNhd_integral`, OS1 regularity, OS2 translation/D4 invariance, and the bundled `SatisfiesTorusOS` structure. All Gaussian results fully proved.

## Status
**Main result**: `torusGaussianLimit_satisfies_OS` fully proved; 0 axioms, 0 sorries
**Length**: 935 lines, 7 definitions + ~20 theorems/lemmas + 1 structure

---

### `torusGeneratingFunctional`
```lean
def torusGeneratingFunctional (μ : ...) [IsProbabilityMeasure μ]
    (f : TorusTestFunction L) : ℂ
```
$Z_\mu(f) = \int e^{i\omega(f)}\, d\mu(\omega)$.

### `torusGeneratingFunctionalℂ`
```lean
def torusGeneratingFunctionalℂ (μ : ...) [IsProbabilityMeasure μ]
    (f_{\text{re}}\ f_{\text{im}} : TorusTestFunction L) : ℂ
```
Complex generating functional $Z[J] = \int e^{i\omega(f_{\text{re}}) - \omega(f_{\text{im}})}\, d\mu$.

### `TorusOS0_Analyticity`, `TorusOS1_Regularity`, `TorusOS2_TranslationInvariance`, `TorusOS2_D4Invariance`
Prop definitions for each OS axiom on the torus.

### `torusGaussianLimit_characteristic_functional` (theorem, proved)
$E[e^{i\omega(f)}] = \exp(-\frac{1}{2}G_L(f,f))$. **Proved** by matching the real MGF to $N(0, G_L(f,f))$ via `mgf_id_gaussianReal`, then analytically continuing to $z = i$ using `eqOn_complexMGF_of_mgf`.

### `analyticOnNhd_eq_of_eqOn_reals` (private theorem, proved)
Multi-variable identity theorem: two entire functions $(\text{Fin}\ n \to \mathbb{C}) \to \mathbb{C}$ agreeing on $\mathbb{R}^n$ are equal. **Proved** by induction using `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`.

### `torusGeneratingFunctionalℂ_analyticOnNhd` (theorem, proved)
$z \mapsto Z_{\mathbb{C}}[\sum \text{Re}(z_i) J_i, \sum \text{Im}(z_i) J_i]$ is entire analytic. **Proved** via `analyticOnNhd_integral` with Gaussian exponential moment domination.

### `torusGaussianLimit_complex_cf_quadratic` (theorem, proved)
$Z_{\mathbb{C}}[z] = \exp(-\frac{1}{2}\sum_{i,j} z_i z_j G_L(J_i, J_j))$. **Proved** by the identity theorem: both sides are entire and agree on $\mathbb{R}^n$.

### `torusGaussianLimit_os0`, `torusGaussianLimit_os1`, `torusGaussianLimit_os2_translation`, `torusGaussianLimit_os2_D4` (theorems, proved)
Each OS axiom for the Gaussian limit.

### `SatisfiesTorusOS` (structure)
Bundled torus OS axioms: OS0 + OS1 + OS2 (translation + D4).

### `torusGaussianLimit_satisfies_OS` (theorem, proved)
The torus Gaussian continuum limit satisfies all torus OS axioms.

### `torusGaussianOS_exists` (theorem, proved)
Existence: for any $L > 0$, $m > 0$, there exists a probability measure satisfying `SatisfiesTorusOS`.

---
*This file has **7** definitions, **1** structure, and **~20** theorems/lemmas (0 with sorry).*
