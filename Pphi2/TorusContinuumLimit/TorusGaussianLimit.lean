/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gaussian Identification of the Torus Continuum Limit

Identifies the weak limit from `torusGaussianLimit_exists` as a Gaussian
measure with the correct covariance (the torus continuum Green's function).

## Main results

- `torusGaussianLimit_isGaussian` — (axiom) weak limits of Gaussians are Gaussian
- `IsTorusGaussianContinuumLimit` — predicate for the Gaussian continuum limit on torus

## Mathematical background

### Gaussianity of the limit

The characteristic functional of ν_{GFF,N} is:

  `E[e^{iω(f)}] = exp(-½ · torusEmbeddedTwoPoint_N(f, f))`

By `torus_propagator_convergence`, the exponent converges to `-½ G_L(f, f)`.
Weak convergence implies pointwise convergence of characteristic functionals.
Hence the limit has Gaussian characteristic functional, and by Bochner-Minlos
on the torus it is a Gaussian measure.

This is the same mathematical content as `gaussianLimit_isGaussian` from
the S'(ℝ^d) approach, but on the torus configuration space.

## References

- Fernique (1975), §III.4
- Simon, *The P(φ)₂ Euclidean QFT* Ch. I
-/

import Pphi2.TorusContinuumLimit.TorusConvergence

noncomputable section

open GaussianField MeasureTheory Filter

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Gaussianity of the torus limit -/

/-- **Weak limits of Gaussian measures on the torus are Gaussian.**

If {μ_n} is a sequence of centered Gaussian measures on Configuration(TorusTestFunction L)
that converges weakly to μ, then μ is also a centered Gaussian measure.

The characteristic functional of μ_n is `exp(-½ σ²_n(f))` where σ²_n(f)
is the variance. Weak convergence implies pointwise convergence of
characteristic functionals to `exp(-½ σ²(f))`, which is Gaussian by
the Bochner-Minlos theorem on the nuclear Fréchet space C∞(T²_L).

Reference: Fernique (1975), §III.4; Simon, *The P(φ)₂ Euclidean QFT* Ch. I. -/
axiom torusGaussianLimit_isGaussian
    (μ_seq : ℕ → Measure (Configuration (TorusTestFunction L)))
    (hμ_prob : ∀ n, IsProbabilityMeasure (μ_seq n))
    -- Each μ_n is Gaussian
    (hμ_gauss : ∀ n (f : TorusTestFunction L),
      ∫ ω : Configuration (TorusTestFunction L),
        Real.exp (ω f) ∂(μ_seq n) =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂(μ_seq n)))
    -- Weak convergence to μ
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hconv : ∀ (g : Configuration (TorusTestFunction L) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun n => ∫ ω, g ω ∂(μ_seq n)) atTop (nhds (∫ ω, g ω ∂μ))) :
    -- The limit is Gaussian
    ∀ (f : TorusTestFunction L),
      ∫ ω : Configuration (TorusTestFunction L),
        Real.exp (ω f) ∂μ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ)

/-! ## Gaussian continuum limit predicate -/

/-- **Predicate for the torus Gaussian continuum limit measure.**

A probability measure μ on Configuration(TorusTestFunction L) is a
Gaussian continuum limit if:
1. It is a probability measure.
2. It is Gaussian (characteristic functional has exp(-½σ²) form).
3. Its covariance equals the torus continuum Green's function.
4. It is Z₂-symmetric: `μ ∘ (-) = μ`. -/
structure IsTorusGaussianContinuumLimit
    (μ : Measure (Configuration (TorusTestFunction L)))
    (mass : ℝ) (hmass : 0 < mass) : Prop where
  /-- μ is a probability measure -/
  isProbability : IsProbabilityMeasure μ
  /-- Gaussian: characteristic functional has exp(-½σ²) form -/
  isGaussian : ∀ (f : TorusTestFunction L),
    ∫ ω : Configuration (TorusTestFunction L),
      Real.exp (ω f) ∂μ =
    Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ)
  /-- Covariance = torus continuum Green's function -/
  covariance_eq : ∀ (f : TorusTestFunction L),
    ∫ ω : Configuration (TorusTestFunction L), (ω f) ^ 2 ∂μ =
    torusContinuumGreen L mass hmass f f
  /-- Z₂ symmetry: μ is invariant under field negation -/
  z2_symmetric : Measure.map
    (Neg.neg : Configuration (TorusTestFunction L) →
      Configuration (TorusTestFunction L)) μ = μ

/-! ## Nontriviality -/

/-- **Nontriviality of the torus Gaussian continuum limit.**

For any nonzero test function f, the two-point function is strictly positive. -/
theorem torusGaussianLimit_nontrivial
    (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) (hf : f ≠ 0)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (h2pt : ∫ ω : Configuration (TorusTestFunction L),
        (ω f) ^ 2 ∂μ = torusContinuumGreen L mass hmass f f) :
    0 < ∫ ω : Configuration (TorusTestFunction L), (ω f) ^ 2 ∂μ := by
  rw [h2pt]
  exact torusContinuumGreen_pos L mass hmass f hf

end Pphi2

end
