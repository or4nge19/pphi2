# `Multilinear.lean` -- Informal Summary

> **Source**: [`Pphi2/GeneralResults/Osgood/Multilinear.lean`](../../../../Pphi2/GeneralResults/Osgood/Multilinear.lean)
>
> **Generated**: 2026-03-20

## Overview
Adapted from Geoffrey Irving's `girving/ray`. Defines continuous multilinear map constructors needed for the Osgood lemma proof: `fstCmmap` and `sndCmmap` (projections), `smulCmmap` (cons-ing two multilinear maps via scalar multiplication), `termCmmap` (monomials $x^a y^b$ as multilinear maps on $\mathbb{C} \times \mathbb{C}$), and `cmmapApplyCmap` (evaluation at a point as a CLM). Proves norm bounds and evaluation formulas.

## Status
**Main result**: Fully proven (0 sorries)
**Length**: 273 lines, 5 definitions + 14 theorems

---

### `fstCmmap`, `sndCmmap`
```lean
def fstCmmap (R A B : Type) ... : ContinuousMultilinearMap R (fun _ : Fin 1 ↦ A × B) A
def sndCmmap (R A B : Type) ... : ContinuousMultilinearMap R (fun _ : Fin 1 ↦ A × B) B
```
`fst` and `snd` projections as 1-linear continuous multilinear maps. Both have norm 1.

### `smulCmmap`
```lean
def smulCmmap ... (x : ContinuousMultilinearMap ...) (xs : ContinuousMultilinearMap ...) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin (n + 1) ↦ A) B
```
Cons two multilinear maps: extract scalar from first input via $x$, apply $xs$ to remaining inputs, combine via $\cdot$. Norm bound: $\|x \cdot xs\| \le \|x\| \cdot \|xs\|$.

### `termCmmap`
```lean
noncomputable def termCmmap (𝕜 : Type) ... : ∀ n : ℕ, ℕ → E → ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ 𝕜 × 𝕜) E
```
Monomial $x^{\min(k,n)} y^{n-k}$ as an $n$-linear map on $\mathbb{C} \times \mathbb{C}$. Norm bound: $\|\text{termCmmap}\; n\; k\; x\| \le \|x\|$.

### `cmmapApplyCmap`
```lean
def cmmapApplyCmap (𝕜 : Type) ... (x : ∀ i, A i) : ContinuousMultilinearMap 𝕜 A B →L[𝕜] B
```
Evaluation of a continuous multilinear map at a fixed point, as a CLM.

---
*This file has **5** definitions and **14** theorems/lemmas (0 with sorry).*
