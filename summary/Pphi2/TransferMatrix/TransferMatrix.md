# `TransferMatrix.lean` -- Informal Summary

> **Source**: [`Pphi2/TransferMatrix/TransferMatrix.lean`](../../Pphi2/TransferMatrix/TransferMatrix.lean)
>
> **Generated**: 2026-03-20

## Overview
Defines the transfer matrix kernel $T(\psi, \psi')$ for the lattice $P(\Phi)_2$ field theory by decomposing the lattice action across time slices. On a 2D lattice $\{0,\dots,N_t-1\} \times \{0,\dots,N_s-1\}$, the Boltzmann weight factorizes as a product of transfer matrix kernels $T(\psi,\psi') = \exp\bigl(-K(\psi,\psi') - \tfrac{a}{2}h_a(\psi) - \tfrac{a}{2}h_a(\psi')\bigr)$.

## Status
**Main result**: Fully proven (0 sorry)
**Length**: 194 lines, 6 definitions + 4 theorems

---

### `SpatialField (Ns : N) := Fin Ns -> R`
```lean
abbrev SpatialField (Ns : N) := Fin Ns -> R
```
Field on a single spatial time slice: $\psi : \{0,\dots,N_s-1\} \to \mathbb{R}$.

### `spatialKinetic`
```lean
def spatialKinetic (a : R) (psi : SpatialField Ns) : R
```
Spatial kinetic energy: $\frac{1}{2}\sum_x a^{-2}(\psi(x+1)-\psi(x))^2$.

### `spatialPotential`
```lean
def spatialPotential (P : InteractionPolynomial) (_a mass : R) (c : R) (psi : SpatialField Ns) : R
```
Spatial potential energy: $\sum_x \bigl(\frac{1}{2}m^2\psi(x)^2 + {:}P(\psi(x)){:}_c\bigr)$.

### `spatialAction`
```lean
def spatialAction (P : InteractionPolynomial) (a mass : R) (c : R) (psi : SpatialField Ns) : R
```
Full spatial action $h_a(\psi) = \text{spatialKinetic} + \text{spatialPotential}$.

### `timeCoupling`
```lean
def timeCoupling (psi psi' : SpatialField Ns) : R
```
Time coupling between adjacent slices: $K(\psi,\psi') = \frac{1}{2}\sum_x (\psi(x)-\psi'(x))^2$.

### `transferKernel`
```lean
def transferKernel (P : InteractionPolynomial) (a mass : R) : SpatialField Ns -> SpatialField Ns -> R
```
Transfer matrix kernel: $T(\psi,\psi') = \exp\bigl(-K(\psi,\psi') - \frac{a}{2}h_a(\psi) - \frac{a}{2}h_a(\psi')\bigr)$.

### `timeCoupling_nonneg`
$K(\psi,\psi') \ge 0$ (sum of squares).
*Proof*: Direct from `mul_nonneg` and `sq_nonneg`. Fully proved.

### `timeCoupling_eq_zero_iff`
$K(\psi,\psi') = 0 \iff \psi = \psi'$.
*Proof*: From `Finset.sum_eq_zero_iff_of_nonneg` and `sq_eq_zero_iff`. Fully proved.

### `transferKernel_pos`
$T(\psi,\psi') > 0$ for all $\psi,\psi'$.
*Proof*: Immediate from `Real.exp_pos`. Fully proved.

### `transferKernel_symmetric`
$T(\psi,\psi') = T(\psi',\psi)$.
*Proof*: From $(a-b)^2 = (b-a)^2$ and commutativity of addition. Fully proved.

---
*This file has **6** definitions and **4** theorems/lemmas (0 with sorry).*
