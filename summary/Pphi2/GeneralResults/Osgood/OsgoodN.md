# `OsgoodN.lean` -- Informal Summary

> **Source**: [`Pphi2/GeneralResults/Osgood/OsgoodN.lean`](../../../../Pphi2/GeneralResults/Osgood/OsgoodN.lean)
> **Generated**: 2026-03-20

## Overview
Generalizes Osgood's lemma from $\mathbb{C}^2$ to $\mathbb{C}^n$: a continuous, separately analytic function of $n$ complex variables is jointly analytic. The proof is by induction on $n$, using the two-variable `osgood` from `Osgood2.lean` for the base case and a "block Osgood" lemma for the inductive step. The block Osgood lemma constructs the joint power series via antidiagonal sums of `jointTerm` multilinear maps (prepending fst-extractions to snd-composed coefficients).

## Status
**Main result**: 1 axiom (`block_osgood_ax` for the inductive step)
**Length**: ~570 lines, 10 definitions + 15 theorems + 1 axiom

---

### Base cases
- `osgood_n0`: Any function $f : (\text{Fin}\;0 \to \mathbb{C}) \to \mathbb{C}$ is analytic (domain is a point).
- `osgood_n1`: Separately analytic on $\mathbb{C}^1$ implies analytic (reduce to 1D via `funUnique`).

### Inductive step helpers
- `sep_analytic_tail`, `sep_analytic_head`: Separate analyticity of $f \circ \text{Fin.cons}$ in tail/head variables.
- `continuous_fin_cons_tail`: Continuity of partial application.

### `block_osgood_1`
For $g : \mathbb{C} \times (\text{Fin}\;1 \to \mathbb{C}) \to \mathbb{C}$: analytic in $\mathbb{C}$ for each fixed $\text{Fin}\;1 \to \mathbb{C}$ and vice versa $\implies$ jointly analytic. Transfer to $\mathbb{C}^2$ via `osgood`.

### Joint series construction
- `prependFst k q`: Prepend $k$ fst-extractions to a multilinear map $q$.
- `sndComp q`: Compose $q$ with snd projections on all inputs.
- `jointTerm q k`: $= \text{prependFst}\;k\;(\text{sndComp}\;q)$; evaluates to $u^k \cdot q(s,\ldots,s)$ at constant $(u,s)$.
- `jointEntry'`, `jointSeries`: Antidiagonal assembly of joint terms into a `FormalMultilinearSeries`.

### `block_osgood_series`
Given 1D Cauchy coefficients $c_k(v)$ with power series $q_k$ in $v$ and geometric bounds, constructs `HasFPowerSeriesOnBall` for the joint function $g(w,v)$. Fully proved.

### `osgood_separately_analytic`
The main $n$-variable Osgood theorem. The inductive step uses `block_osgood_ax` (axiom) for the block Osgood lemma at general $m$.

---
*This file has **10** definitions, **15** theorems, and **1** axiom.*
