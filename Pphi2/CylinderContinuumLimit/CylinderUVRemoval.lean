/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cylinder UV Removal: Λ → ∞

Removes the UV cutoff Λ from the cylinder interacting measure,
constructing the UV limit measure μ_T for each fixed temporal extent T.

## Main results

- `cylinderUVLimitMeasure` — the limit measure as Λ → ∞
- `cylinderUVLimitMeasure_isProbability` — it is a probability measure
- `cylinderUVLimit_weakLimit` — it is the weak limit of μ_{Λ,T}

## Mathematical background

The UV limit exists because Wick ordering removes the logarithmic
divergence of the bare interaction. Concretely:

1. V_{Λ,T} converges in L²(μ_free) as Λ → ∞ because the Wick-ordered
   integrand :P(φ_Λ):_{c_Λ} has controlled differences: the variance
   of V_{Λ',T} - V_{Λ,T} involves only spatial modes |k| ∈ (Λ, Λ'],
   which are independent under μ_free and whose Wick-ordered contribution
   vanishes by the renormalization cancellation.

2. L² convergence of V implies L¹ convergence of exp(-V) (by dominated
   convergence + uniform lower bound), hence weak convergence of measures.

This is the cylinder analogue of the lattice continuum limit (a → 0),
but simpler: the UV cutoff Λ is a Fourier mode truncation, not a
lattice spacing, so no embedding map is needed.

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII (UV cutoff removal)
- Glimm-Jaffe, *Quantum Physics*, §19.2
-/

import Pphi2.CylinderContinuumLimit.CylinderHypercontractivity

open GaussianField MeasureTheory

noncomputable section

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## UV limit measure

The UV limit measure μ_T is the weak limit of the cutoff measures μ_{Λ,T}
as Λ → ∞. Its existence follows from:
- Uniform second moment bounds (from `cylinderInteracting_second_moment_bound`)
- Tightness via Mitoma criterion (nuclear test function space)
- Prokhorov's theorem on the Polish configuration space -/

/-- **UV limit measure** on the cylinder for fixed temporal extent T.

This is the P(φ)₂ interacting measure with UV cutoff removed:
  `μ_T = lim_{Λ→ ∞} (1/Z_{Λ,T}) exp(-V_{Λ,T}) dμ_free`

The limit exists because:
1. Uniform moment bounds (from hypercontractivity + density transfer)
   give tightness of {μ_{Λ,T}}_Λ
2. Prokhorov on the Polish configuration space extracts a convergent
   subsequence
3. The limit is independent of subsequence (by L² convergence of V_{Λ,T}) -/
axiom cylinderUVLimitMeasure
    (P : InteractionPolynomial) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    @Measure (Configuration (CylinderTestFunction L)) instMeasurableSpaceConfiguration

/-- The UV limit measure is a probability measure. -/
axiom cylinderUVLimitMeasure_isProbability
    (P : InteractionPolynomial) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    @IsProbabilityMeasure (Configuration (CylinderTestFunction L))
      instMeasurableSpaceConfiguration
      (cylinderUVLimitMeasure L P T mass hT hmass)

/-- The UV limit measure is the weak limit of the cutoff measures.

For all bounded continuous functions g on Configuration(CylinderTestFunction L):
  `∫ g dμ_{Λ,T} → ∫ g dμ_T` as Λ → ∞ -/
axiom cylinderUVLimit_weakLimit
    (P : InteractionPolynomial) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (g : Configuration (CylinderTestFunction L) → ℝ)
    (hg_cont : Continuous g) (hg_bound : ∃ M, ∀ ω, |g ω| ≤ M) :
    Filter.Tendsto (fun Λ =>
      ∫ ω, g ω ∂(cylinderInteractingMeasure L P Λ T mass hT hmass))
    Filter.atTop
    (nhds (∫ ω, g ω ∂(cylinderUVLimitMeasure L P T mass hT hmass)))

/-! ## Properties of the UV limit -/

/-- **Absolute continuity of the UV limit measure** w.r.t. the free measure.

Each cutoff measure μ_{Λ,T} = (1/Z_{Λ,T}) exp(-V_{Λ,T}) dμ_free is absolutely
continuous w.r.t. μ_free by construction. However, absolute continuity is NOT
preserved under weak limits in general (counterexample: point masses weakly
converging to a point mass at a different location).

For P(φ)₂, the limit μ_T is absolutely continuous because:
1. The Wick-ordered densities exp(-V_{Λ,T})/Z_{Λ,T} converge in L²(μ_free)
   (by hypercontractivity + Wick renormalization cancellation)
2. L² convergence implies the limit has an L² density w.r.t. μ_free
3. Having an L² density implies absolute continuity

This is a deep analytical fact requiring L² convergence of densities
(not just weak convergence of measures), so we take it as an axiom.

**References:**
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII, Theorem VIII.5
- Glimm-Jaffe, *Quantum Physics*, §19.2, density convergence -/
axiom cylinderUVLimitMeasure_absolutelyContinuous
    (P : InteractionPolynomial) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    cylinderUVLimitMeasure L P T mass hT hmass ≪
    cylinderFreeMeasure L mass hmass

/-- **Finite second moments** under the UV limit measure.

The proof uses weak convergence + truncation + monotone convergence:
1. For each M > 0, let g_M(ω) = min((ω f)², M). This is bounded and continuous.
2. By `cylinderUVLimit_weakLimit`: ∫ g_M dμ_T = lim_Λ ∫ g_M dμ_{Λ,T}
3. Since g_M ≤ (ω f)², we have ∫ g_M dμ_{Λ,T} ≤ ∫ (ω f)² dμ_{Λ,T} ≤ C
   by `cylinderInteracting_second_moment_bound`
4. Therefore ∫ g_M dμ_T ≤ C for all M
5. By monotone convergence (g_M ↑ (ω f)²), we get ∫ (ω f)² dμ_T ≤ C

This argument is mathematically straightforward but requires significant Lean
infrastructure (min continuity, monotone convergence for Bochner integrals,
connecting Filter.Tendsto bounds to pointwise bounds). We take it as an axiom.

**Key inputs:** `cylinderInteracting_second_moment_bound`, `cylinderUVLimit_weakLimit`
**References:** Simon, *P(φ)₂*, Ch. VIII; see also Billingsley, *Convergence of
Probability Measures*, Theorem 5.4 (Fatou for weak convergence) -/
axiom cylinderUVLimit_second_moment_finite
    (P : InteractionPolynomial) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (f : CylinderTestFunction L) :
    ∃ C : ℝ, ∫ ω, (ω f) ^ 2
      ∂(cylinderUVLimitMeasure L P T mass hT hmass) ≤ C

/-- **Convergence of two-point Schwinger functions** as Λ → ∞.

Since `cylinderSchwinger2 L P Λ T mass hT hmass f g = ∫ ω f * ω g dμ_{Λ,T}` and
ω ↦ ω(f) · ω(g) is continuous but NOT bounded, the weak convergence axiom
`cylinderUVLimit_weakLimit` does not apply directly.

The proof requires **uniform integrability** of {ω ↦ ω(f)·ω(g)} under {μ_{Λ,T}}:
1. By Cauchy-Schwarz: |∫ ω f · ω g dμ| ≤ (∫ (ω f)² dμ)^{1/2} · (∫ (ω g)² dμ)^{1/2}
2. `cylinderInteracting_second_moment_bound` gives ∫ (ω f)² dμ_{Λ,T} ≤ C uniformly
3. Actually need: for all ε > 0, there exists M s.t. ∫_{|ω f · ω g| > M} |ω f · ω g| dμ_{Λ,T} < ε
   uniformly in Λ. This follows from uniform L² bounds via Markov/truncation.
4. Uniform integrability + weak convergence of measures implies convergence of integrals
   (Vitali convergence theorem for weak limits)

This is standard but requires Vitali's convergence theorem infrastructure.

**Key inputs:** `cylinderInteracting_second_moment_bound`, `cylinderUVLimit_weakLimit`
**References:** Billingsley, *Convergence of Probability Measures*, Theorem 5.4;
Simon, *P(φ)₂*, Ch. VIII -/
axiom cylinderUVLimit_schwinger2
    (P : InteractionPolynomial) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) :
    Filter.Tendsto (fun Λ =>
      cylinderSchwinger2 L P Λ T mass hT hmass f g)
    Filter.atTop
    (nhds (∫ ω, ω f * ω g
      ∂(cylinderUVLimitMeasure L P T mass hT hmass)))

end Pphi2

end
