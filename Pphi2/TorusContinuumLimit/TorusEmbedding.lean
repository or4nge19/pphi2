/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Torus Embedding: Lattice GFF on the Torus

Defines the continuum-embedded Gaussian measure on the 2D torus T²_L,
the two-point functions, and the continuum Green's function on the torus.

## Main definitions

- `torusEmbedLift` — lifts lattice configurations to torus configurations
- `torusContinuumMeasure` — pushforward of lattice GFF to Configuration(TorusTestFunction L)
- `torusEmbeddedTwoPoint` — two-point function `∫ ω(f)·ω(g) dν_{GFF,N}`
- `torusContinuumGreen` — continuum Green's function on T²_L

## Mathematical background

The torus approach fixes the physical volume L = Na, so only N → ∞ (a = L/N → 0).
The lattice (ℤ/Nℤ)² with spacing a = L/N is embedded into the configuration
space of the torus T²_L = (ℝ/Lℤ)² via sampling at lattice points:

  `(ι_N φ)(f) = Σ_{x ∈ (ℤ/Nℤ)²} φ(x) · eval_x(f)`

where `eval_x(f)` evaluates the torus test function at lattice site x using
the circle restriction with √(L/N) normalization.

The continuum Green's function on the torus has discrete Fourier modes:

  `G_L(f,g) = (1/L²) Σ_{n ∈ ℤ²} f̂(n) ĝ(n) / ((2πn/L)² + m²)`

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
-/

import Pphi2.InteractingMeasure.LatticeMeasure
import Torus.Evaluation

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Torus embedding of lattice fields

We embed lattice fields φ : (ℤ/Nℤ)² → ℝ into distributions on the torus
T²_L via the `torusEmbedCLM` from gaussian-field, which constructs the CLM
`f ↦ Σ_x φ(x) · eval_x(f)` using `NuclearTensorProduct.evalCLM`. -/

/-- The torus embedding lift: maps lattice configurations to torus configurations.

Given a lattice configuration ω (a linear functional on `FinLatticeField 2 N`),
constructs a torus configuration by extracting field values `ω(δ_x)` at each
site and embedding via `torusEmbedCLM`. -/
def torusEmbedLift (N : ℕ) [NeZero N] :
    Configuration (FinLatticeField 2 N) → Configuration (TorusTestFunction L) :=
  fun ω => torusEmbedCLM L N (fun x => ω (Pi.single x 1))

/-- The torus embedding lift is measurable.

Each evaluation `ω ↦ (torusEmbedLift ω)(f)` is a finite sum of measurable
functions `ω ↦ ω(Pi.single x 1)` multiplied by constants, hence measurable. -/
theorem torusEmbedLift_measurable (N : ℕ) [NeZero N] :
    @Measurable _ _ instMeasurableSpaceConfiguration instMeasurableSpaceConfiguration
      (torusEmbedLift L N) := by
  apply configuration_measurable_of_eval_measurable
  intro f
  show Measurable (fun (ω : Configuration (FinLatticeField 2 N)) =>
    torusEmbedLift L N ω f)
  simp only [torusEmbedLift, torusEmbedCLM_apply]
  exact Finset.measurable_sum _ fun x _ =>
    (configuration_eval_measurable (Pi.single x 1)).mul measurable_const

/-! ## Gaussian continuum measure on torus -/

/-- The continuum-embedded Gaussian free field measure on the torus.

Pushforward of the lattice GFF `μ_{GFF,N}` under the torus embedding.
Here a = L/N is determined by L and N.

  `ν_{GFF,N} = (ι̃_N)_* μ_{GFF,N}` -/
def torusContinuumMeasure (N : ℕ) [NeZero N] (mass : ℝ)
    (hmass : 0 < mass) :
    Measure (Configuration (TorusTestFunction L)) :=
  Measure.map (torusEmbedLift L N)
    (latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass)

/-- The torus Gaussian continuum measure is a probability measure. -/
instance torusContinuumMeasure_isProbability (N : ℕ) [NeZero N]
    (mass : ℝ) (hmass : 0 < mass) :
    IsProbabilityMeasure (torusContinuumMeasure L N mass hmass) := by
  unfold torusContinuumMeasure
  exact Measure.isProbabilityMeasure_map
    (torusEmbedLift_measurable L N).aemeasurable

/-! ## Two-point functions -/

/-- The embedded two-point function on the torus.

  `⟨Φ_N(f) · Φ_N(g)⟩_{GFF} = ∫ ω(f) · ω(g) dν_{GFF,N}` -/
def torusEmbeddedTwoPoint (N : ℕ) [NeZero N] (mass : ℝ) (hmass : 0 < mass)
    (f g : TorusTestFunction L) : ℝ :=
  ∫ ω : Configuration (TorusTestFunction L),
    ω f * ω g ∂(torusContinuumMeasure L N mass hmass)

/-- The continuum Green's function on the 2D torus.

  `G_L(f,g) = Σ_m coeff_m(f) · coeff_m(g) / (μ_m + mass²)`

where `μ_m` are the Laplacian eigenvalues on T²_L (via Cantor pairing:
`μ_{pair(n₁,n₂)} = (2πn₁/L)² + (2πn₂/L)²`) and `coeff_m` are the
Schauder coefficients from `DyninMityaginSpace`.

This is the spectral sum representation of the Green's function `(-Δ + m²)⁻¹`
on the torus, which equals the Laplace transform of the heat kernel:
`G_mass(f,g) = ∫₀^∞ e^{-t·mass²} K_t(f,g) dt`.

When `HeatKernel/Bilinear.lean` is implemented in gaussian-field, this will
be replaced by `greenFunctionBilinear mass hmass f g`. -/
def torusContinuumGreen (mass : ℝ) (hmass : 0 < mass)
    (f g : TorusTestFunction L) : ℝ :=
  sorry -- Will be greenFunctionBilinear from gaussian-field HeatKernel/Bilinear.lean

end Pphi2

end
