/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Existence of the Torus Gaussian Continuum Limit

Applies the **proved** Prokhorov theorem on Polish spaces to extract a weakly
convergent subsequence from the tight family of torus Gaussian measures.

## Main results

- `torusGaussianLimit_exists` — **PROVED** (no new axiom!) existence of subsequential limit

## Mathematical background

This is the key payoff of the torus approach:

1. `torusContinuumMeasures_tight` gives tightness of {ν_{GFF,N}}.
2. `configuration_torus_polish` gives that Configuration(TorusTestFunction L) is Polish.
3. `prokhorov_sequential` (already proved in `Convergence.lean`) extracts a
   weakly convergent subsequence.

Unlike the S'(ℝ^d) case, where we needed the axiom `prokhorov_configuration_sequential`
because S'(ℝ^d) is not obviously Polish, here we use the **proved** theorem directly.

## References

- Prokhorov (1956)
- Billingsley, *Convergence of Probability Measures*
-/

import Pphi2.TorusContinuumLimit.TorusTightness
import Pphi2.ContinuumLimit.Convergence

noncomputable section

open GaussianField MeasureTheory Filter

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Prokhorov extraction on the torus

The key theorem: existence of a subsequential weak limit.

This uses `prokhorov_sequential` (proved!) rather than the axiomatized
`prokhorov_configuration_sequential`. The crucial ingredient is that
`Configuration(TorusTestFunction L)` is Polish (from `configuration_torus_polish`). -/

/-- **Existence of the torus Gaussian free field continuum limit.**

For N → ∞, the torus-embedded Gaussian measures `ν_{GFF,N}` have a
weakly convergent subsequence. The limit is a probability measure on
Configuration(TorusTestFunction L).

**This theorem is PROVED**, not axiomatized. The proof uses:
1. Tightness (`torusContinuumMeasures_tight`)
2. Polish space (`configuration_torus_polish`)
3. Prokhorov's theorem (`prokhorov_sequential` — already proved) -/
theorem torusGaussianLimit_exists
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (φ : ℕ → ℕ) (μ : Measure (Configuration (TorusTestFunction L))),
      StrictMono φ ∧
      IsProbabilityMeasure μ ∧
      ∀ (f : Configuration (TorusTestFunction L) → ℝ),
        Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ ω, f ω ∂(torusContinuumMeasure L (φ n + 1) mass hmass))
          atTop (nhds (∫ ω, f ω ∂μ)) := by
  -- Define the sequence of measures indexed by ℕ
  -- We use N = n + 1 to ensure NeZero
  let ν : ℕ → Measure (Configuration (TorusTestFunction L)) :=
    fun n => torusContinuumMeasure L (n + 1) mass hmass
  -- Apply Prokhorov on Configuration spaces (no PolishSpace needed)
  exact prokhorov_configuration ν
    (fun n => torusContinuumMeasure_isProbability L (n + 1) mass hmass)
    (fun ε hε => by
      obtain ⟨K, hK_compact, hK_bound⟩ :=
        torusContinuumMeasures_tight L mass hmass ε hε
      exact ⟨K, hK_compact, fun n => hK_bound (n + 1)⟩)

end Pphi2

end
