# `TorusInteractingOS.lean` — Informal Summary

> **Source**: [`Pphi2/TorusContinuumLimit/TorusInteractingOS.lean`](../../Pphi2/TorusContinuumLimit/TorusInteractingOS.lean)
>
> **Generated**: 2026-03-20

## Overview
States and proves (modulo general infrastructure) the Osterwalder-Schrader axioms OS0-OS2 for the torus interacting continuum limit measure. Contains the lattice symmetry invariance theorem (translation, swap, time reflection for the interacting measure), the Cauchy-Schwarz based OS1 regularity bound, exponential moment bounds for the interacting measure, and the full OS0 analyticity via `analyticOnNhd_integral`. The translation invariance proof transfers lattice symmetry through the weak limit using a uniform Green's function seminorm bound.

## Status
**Main result**: `torusInteracting_satisfies_OS` bundling OS0-OS2; 0 axioms, 0 sorries
**Length**: 2955 lines, 3 definitions + ~35 theorems/lemmas (all proved)

---

### `interactingLatticeMeasure_symmetry_invariant` (theorem, proved)
For a bijective site permutation $\sigma$ preserving the Gaussian density, $\int F(\omega \circ \sigma)\, d\mu_{\text{int}} = \int F(\omega)\, d\mu_{\text{int}}$. **Proved** via MeasurePreserving decomposition: evalME $\to$ piCongrLeft $\to$ evalME$^{-1}$.

### `torusInteractingMeasure_gf_latticeTranslation_invariant` (theorem, proved)
The generating functional of the interacting measure is invariant under lattice translations.

### `torus_interacting_second_moment_continuous` (theorem, proved)
$E_P[(\omega f)^2] \le C \cdot G_N(f,f)$ with $C = 3\sqrt{K}$ universal.

### `torusEmbeddedTwoPoint_le_seminorm` (theorem, proved)
$G_N(f,f) \le p(f)^2$ for a continuous seminorm $p$, uniformly in $N$.

### `torusGF_latticeApproximation_error_vanishes` (theorem, proved)
The cutoff GF approximation error $|Z_N[T_v f] - Z_N[T_{w_n} f]| \to 0$ along the subsequence, where $w_n$ are nearest lattice vectors to $v$.

### `torusInteractingLimit_translation_invariant` (theorem, proved)
The generating functional of the interacting continuum limit is translation invariant.

### `gaussian_exp_abs_moment` (theorem, proved)
For the interacting measure, $\int e^{c|\omega(f)|}\, d\mu_P \le$ explicit Gaussian bound.

### `torusInteractingMeasure_exponentialMomentBound_cutoff` (theorem, proved)
Cutoff-level exponential moment bound: $\|Z_{\mathbb{C},N}[f_{\text{re}}, f_{\text{im}}]\| \le \exp(c \cdot (p(f_{\text{re}}) + p(f_{\text{im}})))$.

### `torusInteracting_exponentialMomentBound` (theorem, proved)
The exponential moment bound passes to the continuum limit.

### `torusInteracting_os0` (theorem, proved)
OS0 analyticity for the interacting continuum limit: $z \mapsto Z_{\mathbb{C}}[\sum z_i J_i]$ is entire.

### `torusInteracting_os1` (theorem, proved)
OS1 regularity: $\|Z_{\mathbb{C}}[f_{\text{re}}, f_{\text{im}}]\| \le \exp(c(q(f_{\text{re}}) + q(f_{\text{im}})))$.

### `torusInteracting_os2_translation` (theorem, proved)
OS2 translation invariance for the interacting limit.

### `torusInteracting_os2_D4` (theorem, proved)
OS2 D4 point group invariance (swap + time reflection) for the interacting limit.

### `torusInteracting_satisfies_OS` (theorem, proved)
Bundled: the interacting continuum limit satisfies `SatisfiesTorusOS` (OS0 + OS1 + OS2).

---
*This file has **3** definitions and **~35** theorems/lemmas (0 with sorry).*
