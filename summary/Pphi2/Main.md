# `Main.lean` -- Informal Summary

> **Source**: [`Pphi2/Main.lean`](../../Pphi2/Main.lean)
>
> **Generated**: 2026-03-20

## Overview
The top-level assembly file for the $P(\Phi)_2$ construction. States and proves the main theorem (`pphi2_main`), existence (`pphi2_existence`), nontriviality, non-Gaussianity, mass gap, and the Glimm-Jaffe-Nelson theorem (`pphi2_wightman`) combining all phases. The OS reconstruction theorem is stated as a docstring-level result (Minkowski space QFT formalism not formalized).

## Status
**Main result**: Depends on axioms from upstream files; 1 axiom in this file (`pphi2_nontriviality`)
**Length**: 288 lines, 0 definitions + 8 theorems + 1 axiom

---

### `pphi2_main`
For any continuum limit measure $\mu$ (satisfying `IsPphi2Limit`), $\mu$ satisfies all five OS axioms (`SatisfiesFullOS`). Delegates to `continuumLimit_satisfies_fullOS`.

### `pphi2_existence`
$\exists \mu$ probability measure on $\mathcal{S}'(\mathbb{R}^2)$ satisfying `SatisfiesFullOS`. Delegates to `pphi2_exists`.

### `pphi2_nontriviality` (axiom)
$\exists \mu$ such that $S_2(f,f) = \int \Phi(f)^2\,d\mu > 0$ for all $f \ne 0$.

### `pphi2_nonGaussianity`
The connected four-point function is nonzero: $\exists f,\; S_4(f,f,f,f) - 3 S_2(f,f)^2 \ne 0$. Uses `continuumLimit_nonGaussian` with lattice spacings $a_n = 1/(n+1) \to 0$.

### `pphi2_mass_gap`
$\exists m_0 > 0$ (the mass gap). Currently stated with $m_0 = m$ (the bare mass).

### `os_reconstruction`
Given `SatisfiesFullOS`, the OS reconstruction theorem yields a Wightman QFT with mass gap $m_0 > 0$ (spectral content recorded; full Wightman axioms described in docstring).

### `pphi2_wightman`
$\exists \mu$ satisfying all OS axioms, and $\exists m_0 > 0$ (mass gap). Combines `pphi2_exists` with `os_reconstruction`.

### `mass_reparametrization_invariance`, `mass_reparametrization_exists`
The continuum limit is invariant under mass reparametrization via `shiftQuadratic`.

---
*This file has **0** definitions, **8** theorems, and **1** axiom.*
