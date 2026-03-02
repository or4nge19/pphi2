/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tightness of Torus Gaussian Measures

Shows that the family of continuum-embedded Gaussian measures
`{ν_{GFF,N}}_{N ≥ 1}` is tight on Configuration(TorusTestFunction L).

## Main results

- `torus_second_moment_uniform` — `∫ (ω f)² dν_{GFF,N} ≤ C` uniformly in N
- `torusContinuumMeasures_tight` — (axiom) tightness via Mitoma criterion on torus

## Mathematical background

### Tightness on the torus vs S'(ℝ^d)

The torus approach makes tightness significantly easier than on S'(ℝ^d):
- **Finite volume**: The torus T²_L is compact, so there is no IR contribution
  to the Riemann sum bounds.
- **Mitoma criterion on compact spaces**: For measures on the dual of a nuclear
  Fréchet space over a compact base, tightness of 1D marginals suffices.
- **1D marginals are Gaussian**: Each `(ev_f)_* ν_{GFF,N}` is N(0, σ²_N) with
  σ²_N ≤ C uniformly (from `torusEmbeddedTwoPoint_uniform_bound`).

## References

- Mitoma (1983), "Tightness of probabilities on C([0,1]; S') and D([0,1]; S')"
- Simon, *The P(φ)₂ Euclidean QFT*, §V.1
-/

import Pphi2.TorusContinuumLimit.TorusPropagatorConvergence

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Uniform second moment bounds -/

/-- **Uniform bound on torus Gaussian second moments.**

  `∫ (ω f)² dν_{GFF,N} ≤ C(f, L, m)` uniformly in N ≥ 1

This is a direct consequence of `torusEmbeddedTwoPoint_uniform_bound`. -/
theorem torus_second_moment_uniform (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (TorusTestFunction L),
      (ω f) ^ 2 ∂(torusContinuumMeasure L N mass hmass) ≤ C := by
  obtain ⟨C, hC_pos, hC_bound⟩ := torusEmbeddedTwoPoint_uniform_bound L mass hmass f
  refine ⟨C, hC_pos, fun N _ => ?_⟩
  have : ∫ ω : Configuration (TorusTestFunction L),
      (ω f) ^ 2 ∂(torusContinuumMeasure L N mass hmass) =
    torusEmbeddedTwoPoint L N mass hmass f f := by
    congr 1; ext ω; ring
  rw [this]
  exact hC_bound N

/-! ## Tightness of torus Gaussian measures -/

/-- **Tightness of the torus-embedded Gaussian measures.**

The family `{ν_{GFF,N}}_{N ≥ 1}` is tight on Configuration(TorusTestFunction L).

Proof outline:
1. **1D marginals**: For each f ∈ C∞(T²_L), the pushforward `(ev_f)_* ν_{GFF,N}`
   is N(0, σ²_N) on ℝ. By `torus_second_moment_uniform`, σ²_N ≤ C uniformly.
   Chebyshev gives `P(|Φ_N(f)| > R) ≤ C/R²` for all N.

2. **Equicontinuity**: For f, g ∈ C∞(T²_L), `E[|Φ_N(f) - Φ_N(g)|²]` is
   controlled by seminorms of f - g, uniformly in N. This is cleaner than
   on S'(ℝ^d) because the torus has finite volume.

3. **Mitoma criterion**: 1D tightness + equicontinuity ⟹ tightness on the
   dual of the nuclear Fréchet space C∞(T²_L).

Reference: Mitoma (1983), Simon §V.1. -/
axiom torusContinuumMeasures_tight
    (mass : ℝ) (hmass : 0 < mass) :
    ∀ ε : ℝ, 0 < ε →
    ∃ (K : Set (Configuration (TorusTestFunction L))),
      IsCompact K ∧
      ∀ (N : ℕ) [NeZero N],
      1 - ε ≤ (torusContinuumMeasure L N mass hmass K).toReal

end Pphi2

end
