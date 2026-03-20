# `SpectralGap.lean` -- Informal Summary

> **Source**: [`Pphi2/TransferMatrix/SpectralGap.lean`](../../Pphi2/TransferMatrix/SpectralGap.lean)
>
> **Generated**: 2026-03-20

## Overview
Restates the strict positivity of the mass gap and introduces two axioms for the uniform lower bound on the spectral gap: one giving a uniform bound $m_0 > 0$ for all $a \le a_0$, and one giving an explicit bound $m_{\mathrm{phys}} \ge c \cdot m_{\mathrm{bare}}$. These are crucial for transferring OS4 (clustering) to the continuum limit.

## Status
**Main result**: 2 axioms
**Length**: 107 lines, 0 definitions + 1 theorem + 2 axioms

---

### `spectral_gap_pos`
$E_1 - E_0 > 0$. Delegates to `massGap_pos`. Fully proved.

### `spectral_gap_uniform` (axiom)
$\exists m_0 > 0,\, \exists a_0 > 0,\, \forall a \in (0,a_0]:\; m_{\mathrm{phys}} \ge m_0$. The mass gap is bounded below uniformly in the lattice spacing. Proof requires cluster expansion (Glimm-Jaffe-Spencer).

### `spectral_gap_lower_bound` (axiom)
$\exists c > 0,\, \forall a \le 1:\; m_{\mathrm{phys}} \ge c \cdot m_{\mathrm{bare}}$. Explicit lower bound in terms of the bare mass.

---
*This file has **0** definitions and **1** theorem (0 with sorry) + **2** axioms.*
