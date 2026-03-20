# `WickBinomial.lean` -- Informal Summary

> **Source**: [`Pphi2/NelsonEstimate/WickBinomial.lean`](../../../Pphi2/NelsonEstimate/WickBinomial.lean)
>
> **Generated**: 2026-03-20

## Overview
Proves the Wick binomial theorem: $:(x+y)^n:_{c_1+c_2} = \sum_{k=0}^n \binom{n}{k} :x^k:_{c_1} \cdot :y^{n-k}:_{c_2}$, the key algebraic identity for the Nelson estimate's covariance splitting. Also proves the lower bound $:x^4:_c \ge -6c^2$ (by completing the square: $x^4 - 6cx^2 + 3c^2 = (x^2 - 3c)^2 - 6c^2$).

## Status
**Main result**: Fully proven (0 sorries)
**Length**: 319 lines, 0 definitions + 7 theorems

---

### `wickMonomial_add_binomial`
For all $n$, $c_1$, $c_2$, $x$, $y$:
$$:({x+y})^n:_{c_1+c_2} = \sum_{k=0}^n \binom{n}{k} :x^k:_{c_1} \cdot :y^{n-k}:_{c_2}$$
Proved by strong induction on $n$, applying the Wick recurrence to both $x$ and $y$ factors, using binomial coefficient identities $(k+1)\binom{n+1}{k+1} = (n+1)\binom{n}{k}$ and $(n+1-k)\binom{n+1}{k} = (n+1)\binom{n}{k}$, and Pascal's rule via `sum_antidiagonal_choose_succ_nsmul`.

### `wickMonomial_two_add`
$n=2$: $:(x+y)^2:_{c_1+c_2} = :x^2:_{c_1} + 2xy + :y^2:_{c_2}$.

### `wickMonomial_four_add`
$n=4$: explicit 5-term expansion for the $\varphi^4$ case.

### `wickMonomial_four_lower_bound`
$:x^4:_c \ge -6c^2$ for all $x$ and $c \ge 0$. Proof: $x^4 - 6cx^2 + 3c^2 = (x^2 - 3c)^2 - 6c^2 \ge -6c^2$.

---
*This file has **0** definitions and **7** theorems/lemmas (0 with sorry).*
