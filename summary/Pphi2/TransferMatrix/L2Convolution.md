# `L2Convolution.lean` -- Informal Summary

> **Source**: [`Pphi2/TransferMatrix/L2Convolution.lean`](../../Pphi2/TransferMatrix/L2Convolution.lean)
>
> **Generated**: 2026-03-20

## Overview
Proves Young's inequality for exponents $(1,2,2)$: if $g \in L^1$ and $f \in L^2$ then $g * f \in L^2$ with $\|g*f\|_2 \le \|g\|_1 \|f\|_2$. Constructs the convolution CLM `convCLM` on $L^2$ and proves self-adjointness for even kernels via the Fubini identity $\int h \cdot (g*f) = \int (g*h) \cdot f$.

## Status
**Main result**: Fully proven (0 sorry)
**Length**: 621 lines, 2 definitions + 6 theorems

---

### `realConv`
```lean
def realConv (mu : Measure G) (g f : G -> R) : G -> R
```
Real-valued convolution: $(g * f)(x) = \int g(t) f(x-t)\,d\mu(t)$.

### `young_convolution_memLp`
$g \in L^1, f \in L^2 \implies g*f \in L^2$. Proved via Cauchy-Schwarz, Tonelli, and Haar translation invariance. Fully proved.

### `young_convolution_bound`
$\|g*f\|_2 \le \|g\|_1 \|f\|_2$ (Young's inequality). Fully proved.

### `young_convolution_ae_add`
$g * (f_1+f_2) =_{\text{a.e.}} g*f_1 + g*f_2$. Proved via `ConvolutionExistsAt.distrib_add` and Fubini. Fully proved.

### `convCLM`
```lean
noncomputable def convCLM {mu : Measure G} [mu.IsAddHaarMeasure]
    (g : G -> R) (hg : MemLp g 1 mu) : Lp R 2 mu ->L[R] Lp R 2 mu
```
Convolution with $g \in L^1$ as a continuous linear map on $L^2$.

### `convCLM_spec`
$(\mathrm{Conv}_g f)(x) = \int g(t) f(x-t)\,dt$ a.e. Fully proved.

### `integral_mul_conv_eq`
Fubini adjoint identity: $\int h \cdot (g*f) = \int (g*h) \cdot f$ for even $g$. Uses AM-GM for product integrability and translation invariance of Haar measure. Fully proved.

### `convCLM_isSelfAdjoint_of_even`
Convolution by an even kernel is self-adjoint on $L^2$: $\langle f, \mathrm{Conv}_g h\rangle = \langle \mathrm{Conv}_g f, h\rangle$. Fully proved.

---
*This file has **2** definitions and **6** theorems/lemmas (0 with sorry).*
