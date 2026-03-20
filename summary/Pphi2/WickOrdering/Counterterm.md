# `Counterterm.lean` -- Informal Summary

> **Source**: [`Pphi2/WickOrdering/Counterterm.lean`](../../../Pphi2/WickOrdering/Counterterm.lean)
>
> **Generated**: 2026-03-20

## Overview
Defines the Wick ordering constant $c_a = G_a(0,0)$, the diagonal of the lattice Green's function, which is the ONLY UV counterterm needed for $P(\Phi)_2$ (super-renormalizability). Proves positivity, an upper bound $c_a \le 1/m^2$, and monotonicity in the mass parameter.

## Status
**Main result**: Fully proven (0 sorries)
**Length**: 134 lines, 1 definition + 3 theorems

---

### `Pphi2.wickConstant`
```lean
def wickConstant (a mass : ℝ) : ℝ
```
The self-contraction $c_a = \frac{1}{|\Lambda|}\sum_{m=0}^{|\Lambda|-1} \frac{1}{\lambda_m}$ where $\lambda_m$ are eigenvalues of $-\Delta_a + m^2$. Equals $G_a(x,x)$ (translation-invariant). Diverges as $c_a \sim \frac{1}{2\pi}\log(1/a) + O(1)$ when $a \to 0$.

### `wickConstant_pos`
$c_a > 0$ when $a > 0$ and $\text{mass} > 0$. Each eigenvalue $\lambda_m > 0$, so each inverse is positive, and the average of positive terms is positive.

### `wickConstant_le_inv_mass_sq`
$c_a \le m^{-2}$ since each $\lambda_m \ge m^2$, so each $1/\lambda_m \le 1/m^2$.

### `wickConstant_antitone_mass`
$c_a$ is monotone decreasing in mass: $m_1 \le m_2 \implies c_a(m_2) \le c_a(m_1)$, since larger mass increases eigenvalues.

---
*This file has **1** definition and **3** theorems/lemmas (0 with sorry).*
