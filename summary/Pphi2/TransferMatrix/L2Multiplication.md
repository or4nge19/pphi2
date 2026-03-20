# `L2Multiplication.lean` -- Informal Summary

> **Source**: [`Pphi2/TransferMatrix/L2Multiplication.lean`](../../Pphi2/TransferMatrix/L2Multiplication.lean)
> **Generated**: 2026-03-20

## Overview
Constructs the multiplication operator $M_w : L^2 \to L^2$ for a bounded measurable function $w$ with $\|w\|_\infty \le C$. Shows $M_w$ is a continuous linear map with $\|M_w f\|_2 \le C\|f\|_2$ (Holder with exponents $\infty$ and $2$), and that $M_w$ is self-adjoint when $w$ is real-valued. This is a building block for the transfer operator factorization $T = M_w \circ \mathrm{Conv}_G \circ M_w$.

## Status
**Main result**: Fully proven (0 sorry)
**Length**: 163 lines, 1 definition + 4 theorems/lemmas

---

### `mul_L2_bound`
```lean
lemma mul_L2_bound {mu : Measure alpha} (w : alpha -> R) ... (f : Lp R 2 mu) :
    eLpNorm (w * f) 2 mu <= ENNReal.ofReal C * eLpNorm f 2 mu
```
Norm bound $\|w \cdot f\|_2 \le C \|f\|_2$ when $\|w\|_\infty \le C$, via `eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm`. Fully proved.

### `mulCLM`
```lean
noncomputable def mulCLM {mu : Measure alpha} (w : alpha -> R) (hw_meas : Measurable w)
    (C : R) (hC : 0 < C) (hw_bound : forall^ae x, norm (w x) <= C) :
    Lp R 2 mu ->L[R] Lp R 2 mu
```
Given $w$ essentially bounded by $C$, multiplication by $w$ as a bounded linear operator on $L^2(\mu, \mathbb{R})$.

### `mulCLM_spec`
$(M_w f)(x) = w(x) \cdot f(x)$ a.e. Fully proved.

### `mulCLM_norm_bound`
$\|M_w f\| \le C \|f\|$ (operator norm bound). Fully proved.

### `mulCLM_isSelfAdjoint`
$M_w$ is self-adjoint: $\langle f, M_w g\rangle = \langle M_w f, g\rangle$, since $w$ is real-valued and $\int f(x)(w(x)g(x))\,d\mu = \int (w(x)f(x))g(x)\,d\mu$. Fully proved.

---
*This file has **1** definition and **4** theorems/lemmas (0 with sorry).*
