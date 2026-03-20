# `ComplexTestFunction.lean` -- Informal Summary

> **Source**: [`Pphi2/OSforGFF/ComplexTestFunction.lean`](../../../Pphi2/OSforGFF/ComplexTestFunction.lean)
> **Generated**: 2026-03-20

## Overview
Utility file for embedding real Schwartz functions into complex Schwartz functions and relating real/complex generating functionals. Defines `schwartzOfReal` ($f \mapsto f + 0i$) and proves simp lemmas: `schwartzRe` and `schwartzIm` extract components correctly, `euclideanAction2ℂ` commutes with `schwartzOfReal`, and the complex generating functional at real test functions equals the real generating functional.

## Status
**Main result**: Fully proven (0 sorries)
**Length**: 86 lines, 1 definition + 8 theorems

---

### `schwartzOfReal`
```lean
def schwartzOfReal (f : TestFunction2) : TestFunction2ℂ
```
Embeds a real Schwartz function as a complex-valued one via $\text{Complex.ofReal}$. Smoothness from `Complex.ofRealCLM.contDiff.comp`; decay from composing with a bounded linear map.

### `schwartzOfReal_apply`
$(schwartzOfReal\; f)(x) = (f(x) : \mathbb{C})$.

### `schwartzRe_schwartzOfReal`, `schwartzIm_schwartzOfReal`
$\text{Re}(\text{ofReal}(f)) = f$ and $\text{Im}(\text{ofReal}(f)) = 0$.

### `euclideanAction2ℂ_schwartzOfReal`
$E(2)$ action commutes with real embedding: $g \cdot \text{ofReal}(f) = \text{ofReal}(g \cdot f)$.

### `schwartzRe_euclideanAction2ℂ`, `schwartzIm_euclideanAction2ℂ`
Real/imaginary parts commute with $E(2)$ action.

### `generatingFunctionalℂ_ofReal_add_real_smul`
$Z_\mathbb{C}[\text{ofReal}(f) + r \cdot \text{ofReal}(h)] = Z[f + rh]$ (complex generating functional at real arguments equals real one).

### `schwartz_decompose`
$J = \text{ofReal}(\text{Re}\;J) + i \cdot \text{ofReal}(\text{Im}\;J)$ for any complex Schwartz function $J$.

---
*This file has **1** definition and **8** theorems/lemmas (0 with sorry).*
