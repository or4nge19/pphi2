# `Positivity.lean` -- Informal Summary

> **Source**: [`Pphi2/TransferMatrix/Positivity.lean`](../../Pphi2/TransferMatrix/Positivity.lean)
>
> **Generated**: 2026-03-20

## Overview
Defines the lattice Hamiltonian $H = -\frac{1}{a}\log T$ and its spectral properties. Introduces energy levels $E_0 = -\frac{1}{a}\log\lambda_0$, $E_1 = -\frac{1}{a}\log\lambda_1$, the mass gap $m_{\mathrm{phys}} = E_1 - E_0$, and proves the mass gap is strictly positive from the Perron-Frobenius spectral gap $\lambda_1 < \lambda_0$.

## Status
**Main result**: Fully proven (0 sorry)
**Length**: 145 lines, 6 definitions + 3 theorems

---

### `TransferGroundExcitedData`
```lean
structure TransferGroundExcitedData (P : InteractionPolynomial) (a mass : R) (ha : 0 < a) (hmass : 0 < mass)
```
Packaged spectral decomposition with distinguished ground ($i_0$) and first-excited ($i_1$) indices.

### `transferGroundExcitedData`
Noncomputable choice of `TransferGroundExcitedData` from `transferOperator_ground_simple_spectral`.

### `transferGroundEigenvalue` / `transferFirstExcitedEigenvalue`
$\lambda_0$ and $\lambda_1$ extracted from spectral data.

### `groundEnergyLevel` / `firstExcitedEnergyLevel`
$E_0 = -\frac{1}{a}\log\lambda_0$ and $E_1 = -\frac{1}{a}\log\lambda_1$.

### `massGap`
```lean
def massGap (P : InteractionPolynomial) (a mass : R) (ha : 0 < a) (hmass : 0 < mass) : R
```
Physical mass gap: $m_{\mathrm{phys}} = E_1 - E_0$.

### `energyLevel_gap`
$E_0 < E_1$. From $\lambda_0 > \lambda_1 > 0$ and $-\frac{1}{a} < 0$ reversing the log inequality. Fully proved.

### `massGap_pos`
$m_{\mathrm{phys}} > 0$. Immediate from `energyLevel_gap`. Fully proved.

---
*This file has **6** definitions and **3** theorems (0 with sorry).*
