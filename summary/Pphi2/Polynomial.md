# `Polynomial.lean` -- Informal Summary

> **Source**: [`Pphi2/Polynomial.lean`](../../Pphi2/Polynomial.lean)
> **Generated**: 2026-03-20

## Overview
Defines the interaction polynomial $P(\tau)$ for the $P(\Phi)_2$ model: an even polynomial of degree $n \ge 4$ with positive leading coefficient $1/n$. Provides evaluation, Wick-ordered evaluation (placeholder), derivative (placeholder), and a quadratic-shift operation used for mass reparametrization.

## Status
**Main result**: Fully proven (0 sorries)
**Length**: 102 lines, 5 definitions + 2 theorems

---

### `InteractionPolynomial` (structure)
```lean
structure InteractionPolynomial where
  n : ℕ
  hn_ge : 4 ≤ n
  hn_even : Even n
  coeff : Fin n → ℝ
  coeff_odd_eq_zero : ∀ m : Fin n, Odd (m : ℕ) → coeff m = 0
  coeff_zero_nonpos : coeff ⟨0, by omega⟩ ≤ 0
```
Data for a $P(\Phi)_2$ model: an even polynomial $P(\tau) = \frac{1}{n}\tau^n + \sum_{m<n} a_m \tau^m$ of even degree $n \ge 4$ with $\mathbb{Z}_2$ symmetry ($P(-\tau) = P(\tau)$).

### `InteractionPolynomial.eval`
```lean
def InteractionPolynomial.eval (P : InteractionPolynomial) (τ : ℝ) : ℝ
```
Evaluates $P(\tau) = \frac{1}{n}\tau^n + \sum_{m<n} a_m \tau^m$.

### `InteractionPolynomial.eval_neg`
$P(-\tau) = P(\tau)$ for all $\tau$. Proved by case-splitting on parity of each coefficient index.

### `InteractionPolynomial.shiftQuadratic`
```lean
def InteractionPolynomial.shiftQuadratic (P : InteractionPolynomial) (δ : ℝ) : InteractionPolynomial
```
Shifts the $\tau^2$ coefficient of $P$ by $\delta$, used for mass reparametrization: $P \mapsto P'$ where $a_2' = a_2 + \delta$, leaving the total lattice action unchanged when the Gaussian mass is adjusted correspondingly.

### `InteractionPolynomial.evalWick`
```lean
def InteractionPolynomial.evalWick (P : InteractionPolynomial) (τ _c : ℝ) : ℝ
```
Placeholder for the Wick-ordered polynomial $:P(\tau):_c$ (actual implementation is in `WickPolynomial.lean`).

### `InteractionPolynomial.evalWick'`
```lean
def InteractionPolynomial.evalWick' (P : InteractionPolynomial) (τ _c : ℝ) : ℝ
```
Placeholder derivative $\partial_\tau P(\tau, c)$.

---
*This file has **5** definitions and **2** theorems/lemmas (0 with sorry).*
