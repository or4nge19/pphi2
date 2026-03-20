# `WickPolynomial.lean` -- Informal Summary

> **Source**: [`Pphi2/WickOrdering/WickPolynomial.lean`](../../../Pphi2/WickOrdering/WickPolynomial.lean)
> **Generated**: 2026-03-20

## Overview
Defines Wick-ordered monomials $:x^n:_c$ and the Wick-ordered interaction polynomial $:P(x):_c$ on the lattice. Proves the connection to probabilist's Hermite polynomials, that Wick ordering at $c=0$ recovers the ordinary polynomial, and that the Wick polynomial is bounded below -- a crucial fact for the well-definedness of $e^{-V}$. The bounded-below proof uses formal `Polynomial` machinery to verify degree and leading coefficient, then applies a general result about even-degree polynomials with positive leading coefficient.

## Status
**Main result**: Fully proven (0 sorries)
**Length**: 594 lines, 6 definitions + 18 theorems

---

### `Pphi2.wickMonomial`
```lean
def wickMonomial : ℕ → ℝ → ℝ → ℝ
```
The Wick-ordered monomial $:x^n:_c$ via the recursion $:x^0: = 1$, $:x^1: = x$, $:x^{n+2}: = x \cdot :x^{n+1}: - (n+1)c \cdot :x^n:$.

### `wickMonomial_zero`, `wickMonomial_one`, `wickMonomial_succ_succ`
Simp lemmas for the recursive cases.

### `wickMonomial_zero_variance`
$:x^n:_0 = x^n$ for all $n$. Proved by induction.

### `wickMonomial_two`, `wickMonomial_three`, `wickMonomial_four`
Explicit formulas: $:x^2:_c = x^2 - c$, $:x^3:_c = x^3 - 3cx$, $:x^4:_c = x^4 - 6cx^2 + 3c^2$. Proved by `simp` + `ring`.

### `wickMonomial_eq_hermite`
For $c > 0$: $:x^n:_c = c^{n/2} \cdot He_n(x/\sqrt{c})$ where $He_n$ is the probabilist's Hermite polynomial. Proved via the bridge to `gaussian-field`'s `wick_eq_hermiteR_rpow`.

### `Pphi2.wickPolynomial`
```lean
def wickPolynomial (P : InteractionPolynomial) (c x : ℝ) : ℝ
```
The Wick-ordered interaction polynomial $:P(x):_c = \frac{1}{n}:x^n:_c + \sum_{m<n} a_m :x^m:_c$.

### `wickPolynomial_zero_variance`
$:P(x):_0 = P(x)$ (Wick ordering at zero variance recovers the original polynomial).

### `poly_even_degree_bounded_below`
A real polynomial with even degree $\ge 2$ and positive leading coefficient is bounded below: $\exists A > 0,\; \forall x,\; p(x) \ge -A$. Proved via `tendsto_norm_atTop` + continuity minimum.

### `wickPolynomial_bounded_below`
$\exists A > 0$ such that $:P(x):_c \ge -A$ for all $x \in \mathbb{R}$. Proved by converting to a formal `Polynomial` and verifying even degree $\ge 4$ with positive leading coefficient $1/n$.

### `wickMonomial_continuous₂`, `wickPolynomial_continuous₂`
Joint continuity of $(c, x) \mapsto :x^n:_c$ and $(c, x) \mapsto :P(x):_c$. Proved by induction on the recursion.

### `wickPolynomial_uniform_bounded_below`
For $c \in [0, C]$, the bound $:P(x):_c \ge -A$ holds uniformly: the constant $A$ depends on $P$ and $C$ but not on $c$ individually. Proved by coefficient continuity + compactness of $[0,C] \times [-R, R]$.

---
*This file has **6** definitions and **18** theorems/lemmas (0 with sorry).*
