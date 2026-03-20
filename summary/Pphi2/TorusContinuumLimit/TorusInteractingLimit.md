# `TorusInteractingLimit.lean` — Informal Summary

> **Source**: [`Pphi2/TorusContinuumLimit/TorusInteractingLimit.lean`](../../Pphi2/TorusContinuumLimit/TorusInteractingLimit.lean)
> **Generated**: 2026-03-20

## Overview
Defines the interacting $P(\varphi)_2$ measure on the torus and proves existence of a subsequential weak limit via Cauchy-Schwarz density transfer. The key input is Nelson's exponential estimate (proved for fixed physical volume $L$), which gives uniform-in-$N$ bounds on $\int e^{-2V}\, d\mu_{\text{GFF}}$. Combined with Gaussian hypercontractivity and the Mitoma-Chebyshev criterion, this yields interacting tightness and hence Prokhorov extraction.

## Status
**Main result**: `torusInteractingLimit_exists` fully proved; 0 axioms, 0 sorries
**Length**: 462 lines, 1 definition + 5 theorems + 1 instance

---

### `torusInteractingMeasure`
```lean
def torusInteractingMeasure (N : ℕ) [NeZero N] (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) : Measure (Configuration (TorusTestFunction L))
```
Pushforward $\mu_{P,N}^{\text{torus}} = (\tilde\iota_N)_* \mu_{P,N}$.

### `torusInteractingMeasure_isProbability` (instance, proved)

### `nelson_exponential_estimate` (theorem, proved)
$\int e^{-2V_{L/N}(\varphi)}\, d\mu_{\text{GFF}} \le K$ uniformly in $N$, where $K$ depends on $P$, $m$, $L$ but not $N$. **Proved** because $a^2 N^2 = L^2$ (fixed physical volume), so $V(\omega) \ge -L^2 A$ gives $e^{-2V} \le e^{2L^2 A}$.

### `torus_interacting_second_moment_uniform` (theorem, proved)
$\int (\omega f)^2\, d\mu_{P,N}^{\text{torus}} \le C$ uniformly in $N$. **Proved** via Cauchy-Schwarz density transfer: $E_P[F] \le \sqrt{K} \sqrt{E_{\text{GFF}}[F^2]}$, then Gaussian hypercontractivity bounds $E_{\text{GFF}}[(\omega g)^4] \le 9 (E_{\text{GFF}}[(\omega g)^2])^2$, and the Gaussian second moment is uniformly bounded.

### `torus_interacting_tightness` (theorem, proved)
The family $\{\mu_{P,N}^{\text{torus}}\}_{N \ge 1}$ is tight. **Proved** from uniform second moments via `configuration_tight_of_uniform_second_moments`.

### `torusInteractingLimit_exists` (theorem, proved)
For $N \to \infty$, the interacting measures have a weakly convergent subsequence. **Proved** from tightness + `prokhorov_configuration`.

---
*This file has **1** definition, **1** instance, and **5** theorems (0 with sorry).*
