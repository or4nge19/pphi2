# `General.lean` -- Informal Summary

> **Source**: [`Pphi2/InteractingMeasure/General.lean`](../../../Pphi2/InteractingMeasure/General.lean)
> **Generated**: 2026-03-20

## Overview
General interacting measure theory, independent of spacetime structure. Given a probability measure $\mu_{\text{free}}$ and an interaction functional $V$ that is measurable and bounded below, constructs: the Boltzmann weight $e^{-V}$, partition function $Z = \int e^{-V}\,d\mu_{\text{free}}$, interacting measure $d\mu_V = \frac{1}{Z}e^{-V}\,d\mu_{\text{free}}$, and $n$-point Schwinger functions $S_n(f_1,\ldots,f_n) = \int \omega(f_1)\cdots\omega(f_n)\,d\mu_V$.

## Status
**Main result**: Fully proven (0 sorries)
**Length**: 343 lines, 8 definitions + 12 theorems

---

### `interactingBoltzmannWeight`
```lean
def interactingBoltzmannWeight (V : Configuration E → ℝ) : Configuration E → ℝ
```
$\omega \mapsto e^{-V(\omega)}$.

### `interactingBoltzmannWeight_pos`
$e^{-V(\omega)} > 0$ for all $\omega$.

### `interactingBoltzmannWeight_integrable`
$e^{-V}$ is integrable w.r.t. any probability measure when $V$ is measurable and bounded below.

### `interactingPartitionFunction`
```lean
def interactingPartitionFunction (V : Configuration E → ℝ) (μ : Measure (Configuration E)) : ℝ
```
$Z = \int e^{-V(\omega)}\,d\mu(\omega)$.

### `interactingPartitionFunction_pos`
$Z > 0$ since $e^{-V} > 0$ everywhere and $\mu$ is a probability measure.

### `interactingMeasure`
```lean
def interactingMeasure (V : Configuration E → ℝ) (μ : Measure (Configuration E)) : Measure (Configuration E)
```
$d\mu_V = \frac{1}{Z} e^{-V}\,d\mu$.

### `interactingMeasure_isProbabilityMeasure`
$\mu_V$ is a probability measure: $\mu_V(\text{univ}) = \frac{1}{Z} \cdot Z = 1$.

### `schwinger2`, `schwinger1`, `schwingerN`
Two-point, one-point, and $n$-point Schwinger functions under the interacting measure.

### `schwinger2_nonneg`
$S_2(f,f) = \int \omega(f)^2\,d\mu_V \ge 0$.

### `schwingerN_perm`
$n$-point functions are invariant under permutation of test functions.

### `interactingBoltzmannWeight_antitone`
If $V_1 \le V_2$ pointwise then $e^{-V_2} \le e^{-V_1}$ pointwise.

---
*This file has **8** definitions and **12** theorems/lemmas (0 with sorry).*
