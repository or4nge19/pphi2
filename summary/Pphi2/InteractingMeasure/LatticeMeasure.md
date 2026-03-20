# `LatticeMeasure.lean` -- Informal Summary

> **Source**: [`Pphi2/InteractingMeasure/LatticeMeasure.lean`](../../../Pphi2/InteractingMeasure/LatticeMeasure.lean)
> **Generated**: 2026-03-20

## Overview
Defines the $P(\Phi)_2$ interacting measure on the finite lattice as a perturbation of the lattice Gaussian measure: $d\mu_a = \frac{1}{Z_a} e^{-V_a(\omega)}\,d\mu_{\text{GFF},a}(\omega)$. Lifts the interaction from field configurations to distributions via delta-function evaluations $\omega(\delta_x)$, defines the partition function and Boltzmann weight, and proves the interacting measure is a probability measure.

## Status
**Main result**: Fully proven (0 sorries)
**Length**: 262 lines, 5 definitions + 6 theorems

---

### `Pphi2.fieldAtSite`
```lean
def fieldAtSite (x : FinLatticeSites d N) : Configuration (FinLatticeField d N) → ℝ
```
Evaluates the field at lattice site $x$: $\omega(\delta_x)$.

### `Pphi2.interactionFunctional`
```lean
def interactionFunctional (P : InteractionPolynomial) (a mass : ℝ) : Configuration (FinLatticeField d N) → ℝ
```
$V_a(\omega) = a^d \sum_x :P(\omega(\delta_x)):_{c_a}$.

### `interactionFunctional_measurable`
$V_a$ is measurable (each $\omega \mapsto \omega(\delta_x)$ is measurable by the cylindrical $\sigma$-algebra).

### `Pphi2.boltzmannWeight`, `Pphi2.partitionFunction`
$e^{-V_a(\omega)}$ and $Z_a = \int e^{-V_a}\,d\mu_{\text{GFF},a}$.

### `partitionFunction_pos`
$Z_a > 0$ since $e^{-V_a} > 0$ everywhere.

### `Pphi2.interactingLatticeMeasure`
```lean
def interactingLatticeMeasure (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) : Measure ...
```
$d\mu_a = \frac{1}{Z_a} e^{-V_a}\,d\mu_{\text{GFF},a}$.

### `interactingLatticeMeasure_isProbability`
$\mu_a$ is a probability measure.

### `Pphi2.latticeSchwinger2`
Two-point Schwinger function: $S_2(x,y) = \frac{1}{Z} \int \omega(\delta_x)\omega(\delta_y) e^{-V_a}\,d\mu_{\text{GFF}}$.

---
*This file has **5** definitions and **6** theorems/lemmas (0 with sorry).*
