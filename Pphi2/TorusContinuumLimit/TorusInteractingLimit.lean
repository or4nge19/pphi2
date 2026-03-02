/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Interacting P(φ)₂ Continuum Limit on the Torus

Defines the interacting P(φ)₂ measure on the torus and proves existence
of a subsequential weak limit via the Cauchy-Schwarz density transfer.

## Main results

- `torusInteractingMeasure` — pushforward of lattice interacting measure to torus
- `torus_interacting_tightness` — (axiom) tightness via Cauchy-Schwarz transfer
- `torusInteractingLimit_exists` — existence of subsequential limit (proved!)

## Mathematical background

### Cauchy-Schwarz density transfer

The interacting measure `dμ_P = (1/Z) e^{-V} dμ_{GFF}` has second moments
controlled by the Gaussian second moments via Cauchy-Schwarz:

  `E_P[|ω(f)|²] ≤ (1/Z) · E_{GFF}[|ω(f)|⁴]^{1/2} · E_{GFF}[e^{-2V}]^{1/2}`

The Gaussian fourth moment is controlled by the second moment (Gaussian
hypercontractivity), and `E_{GFF}[e^{-2V}]` is bounded by Nelson's exponential
estimate. Combined with the **uniform Gaussian tightness** on the torus, this
gives interacting tightness.

### Advantage of the torus

The finite volume makes both Nelson's estimate and the Riemann sum bounds
significantly cleaner. The infinite-volume limit (L → ∞) can be done
separately as a second step.

## References

- Glimm-Jaffe, *Quantum Physics*, §19.3-19.4
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. V-VI
-/

import Pphi2.TorusContinuumLimit.TorusGaussianLimit

noncomputable section

open GaussianField MeasureTheory Filter

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Interacting measure on the torus -/

/-- The torus-embedded interacting P(φ)₂ measure.

Pushforward of the lattice interacting measure `μ_{P,N}` under the torus
embedding, where the lattice spacing is a = L/N.

  `μ_{P,N}^{torus} = (ι̃_N)_* μ_{P,N}` -/
def torusInteractingMeasure (N : ℕ) [NeZero N] (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) :
    Measure (Configuration (TorusTestFunction L)) :=
  Measure.map (torusEmbedLift L N)
    (interactingLatticeMeasure 2 N P (circleSpacing L N) mass (circleSpacing_pos L N) hmass)

/-- The torus interacting measure is a probability measure. -/
instance torusInteractingMeasure_isProbability (N : ℕ) [NeZero N]
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    IsProbabilityMeasure (torusInteractingMeasure L N P mass hmass) := by
  unfold torusInteractingMeasure
  haveI := interactingLatticeMeasure_isProbability 2 N P
    (circleSpacing L N) mass (circleSpacing_pos L N) hmass
  exact Measure.isProbabilityMeasure_map
    (torusEmbedLift_measurable L N).aemeasurable

/-! ## Tightness of interacting measures -/

/-- **Tightness of the torus interacting measures.**

The family `{μ_{P,N}^{torus}}_{N ≥ 1}` is tight on Configuration(TorusTestFunction L).

This is the key analytical result that transfers Gaussian tightness to the
interacting case via the Cauchy-Schwarz density transfer:

  `E_P[|ω(f)|²] ≤ (1/Z_N) · E_{GFF}[|ω(f)|⁴]^{1/2} · E_{GFF}[e^{-2V_N}]^{1/2}`

where:
- `E_{GFF}[|ω(f)|⁴]^{1/2} ≤ C · E_{GFF}[|ω(f)|²]` by Gaussian hypercontractivity
- `E_{GFF}[|ω(f)|²] ≤ C` uniformly by `torusEmbeddedTwoPoint_uniform_bound`
- `(1/Z_N) · E_{GFF}[e^{-2V_N}]^{1/2}` is bounded by Nelson's estimate

Combined with the Mitoma criterion on the torus, this gives tightness.

Reference: Glimm-Jaffe §19.3, Simon Ch. V. -/
axiom torus_interacting_tightness
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∀ ε : ℝ, 0 < ε →
    ∃ (K : Set (Configuration (TorusTestFunction L))),
      IsCompact K ∧
      ∀ (N : ℕ) [NeZero N],
      1 - ε ≤ (torusInteractingMeasure L N P mass hmass K).toReal

/-! ## Existence of the interacting continuum limit -/

/-- **Existence of the torus P(φ)₂ continuum limit.**

For N → ∞, the torus-embedded interacting measures have a weakly
convergent subsequence. The limit is a probability measure on
Configuration(TorusTestFunction L).

**This theorem is PROVED**, not axiomatized. The proof uses:
1. Interacting tightness (`torus_interacting_tightness`)
2. Polish space (`configuration_torus_polish`)
3. Prokhorov's theorem (`prokhorov_sequential` — already proved) -/
theorem torusInteractingLimit_exists
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (φ : ℕ → ℕ) (μ : Measure (Configuration (TorusTestFunction L))),
      StrictMono φ ∧
      IsProbabilityMeasure μ ∧
      ∀ (f : Configuration (TorusTestFunction L) → ℝ),
        Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ ω, f ω ∂(torusInteractingMeasure L (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, f ω ∂μ)) := by
  let ν : ℕ → Measure (Configuration (TorusTestFunction L)) :=
    fun n => torusInteractingMeasure L (n + 1) P mass hmass
  haveI : PolishSpace (Configuration (TorusTestFunction L)) :=
    configuration_torus_polish L
  haveI : BorelSpace (Configuration (TorusTestFunction L)) :=
    configuration_torus_borelSpace L
  exact prokhorov_sequential ν
    (fun n => torusInteractingMeasure_isProbability L (n + 1) P mass hmass)
    (fun ε hε => by
      obtain ⟨K, hK_compact, hK_bound⟩ :=
        torus_interacting_tightness L P mass hmass ε hε
      exact ⟨K, hK_compact, fun n => hK_bound (n + 1)⟩)

end Pphi2

end
