# `LatticeAction.lean` -- Informal Summary

> **Source**: [`Pphi2/InteractingMeasure/LatticeAction.lean`](../../../Pphi2/InteractingMeasure/LatticeAction.lean)
> **Generated**: 2026-03-20

## Overview
Defines the Wick-ordered lattice interaction $V_a(\varphi) = a^d \sum_x :P(\varphi(x)):_{c_a}$ for the $P(\Phi)_2$ field theory on the finite lattice. Proves that $V_a$ is bounded below (crucial for well-definedness of $e^{-V_a}$), continuous, and decomposes as a sum of single-site functions (key for FKG).

## Status
**Main result**: Fully proven (0 sorries)
**Length**: 125 lines, 1 definition + 4 theorems

---

### `Pphi2.latticeInteraction`
```lean
def latticeInteraction (P : InteractionPolynomial) (a mass : ℝ) : FinLatticeField d N → ℝ
```
$V_a(\varphi) = a^d \sum_{x \in \Lambda} :P(\varphi(x)):_{c_a}$ where $c_a = \texttt{wickConstant}$.

### `latticeInteraction_bounded_below`
$\exists B,\;\forall \varphi,\; V_a(\varphi) \ge -B$. Since $:P(\varphi(x)):_{c_a} \ge -A$ for each site, the sum of $|\Lambda|$ terms gives $V_a \ge -a^d |\Lambda| A$. Depends on `wickPolynomial_bounded_below`.

### `latticeInteraction_continuous`
$V_a$ is continuous in $\varphi$, since each $:P(\varphi(x)):$ is continuous in $\varphi(x)$ and the sum is finite.

### `latticeInteraction_single_site`
$V_a(\varphi) = a^d \sum_x v_x(\varphi(x))$ where $v_x(\tau) = :P(\tau):_{c_a}$ depends on $\varphi$ only through the single-site value $\varphi(x)$. This single-site decomposition enables the FKG inequality.

---
*This file has **1** definition and **4** theorems/lemmas (0 with sorry).*
