/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nelson's Exponential Estimate

Combines covariance splitting, the smooth classical lower bound, and
hypercontractivity on the rough error to prove Nelson's exponential estimate:

  `∫ exp(-2V) dμ_GFF ≤ K`  (uniform in lattice size N)

## Main results

- `nelson_exponential_estimate_lattice` — the full estimate on the lattice

## Proof outline

1. Split covariance: C = C_S(T) + C_R(T) (CovarianceSplit.lean)
2. Wick binomial: V(φ) = V_S(φ_S) + E_R(φ_S, φ_R) (WickBinomial.lean)
3. Classical lower bound: V_S ≥ -C₁·(1+|log T|)² (SmoothLowerBound.lean)
4. Hypercontractivity: P(|E_R| > λ) ≤ exp(-c·λ^{1/2}/T^{1/8}) (RoughErrorBound.lean)
5. Dynamic cutoff: choose T = exp(-c₃·√M), integrate (this file)

## References

- Simon, *P(φ)₂ Euclidean QFT*, Chapter V, Theorem V.14
- Glimm-Jaffe, *Quantum Physics*, Section 8.6
-/

import Pphi2.NelsonEstimate.SmoothLowerBound
import Pphi2.NelsonEstimate.RoughErrorBound
import Pphi2.InteractingMeasure.LatticeMeasure
import Pphi2.TorusContinuumLimit.TorusEmbedding

noncomputable section

open GaussianField MeasureTheory Real
open scoped BigOperators

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Nelson's dynamic cutoff argument

Given:
- V(φ) = V_S(φ_S) + E_R(φ_S, φ_R)
- V_S(φ_S) ≥ -C₁·(log T)² (smooth lower bound)
- P(|E_R| > λ) ≤ exp(-c₂·λ^{1/2}/T^{1/8}) (rough tail bound)

If V(φ) ≤ -M, then E_R ≤ -M - V_S ≤ -M + C₁(log T)².

Choose T = T(M) such that C₁(log T)² = M/2:
  T = exp(-√(M/(2C₁)))

Then |E_R| ≥ M/2, so:
  P(V ≤ -M) ≤ P(|E_R| ≥ M/2) ≤ exp(-c₂·(M/2)^{1/2} · exp(c₃·M^{1/2}))

This is DOUBLE EXPONENTIAL decay, so:
  ∫₀^∞ exp(2M) · P(V ≤ -M) dM < ∞ -/

/-- **Nelson's exponential estimate on the lattice** (the main theorem).

For the P(φ)₂ lattice theory on the 2D torus of size L with lattice
spacing a = L/N and mass m > 0:

  `∫ exp(-2V) dμ_GFF ≤ K`

where K depends on P (the interaction polynomial), L, and m,
but NOT on N (the lattice size).

Proof: Dynamic cutoff combining Steps 1-4. -/
theorem nelson_exponential_estimate_lattice
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (K : ℝ), 0 < K ∧
    ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (FinLatticeField 2 N),
        (exp (-interactionFunctional 2 N P (circleSpacing L N) mass ω)) ^ 2
        ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass
          (circleSpacing_pos L N) hmass) ≤ K := by
  -- The key insight: the interaction V(ω) = a^d · Σ_x :P(ω(x)):_c has a^d prefactor.
  -- With a = L/N, we have a^d · |Λ| = (L/N)^d · N^d = L^d, which is CONSTANT in N.
  -- So the pointwise bound V(ω) ≥ -a^d · |Λ| · A = -L^d · A gives a uniform-in-N bound
  -- exp(-2V) ≤ exp(2 · L^d · A).
  -- For d = 2: K = exp(2 · L² · A) works.
  --
  -- Step 1: Get uniform lower bound on wickPolynomial for c ∈ [0, mass⁻²]
  obtain ⟨A, hA_pos, hA_bound⟩ :=
    Pphi2.wickPolynomial_uniform_bounded_below P (mass⁻¹ ^ 2) (by positivity)
  -- Step 2: K = exp(2 · L² · A) works uniformly in N
  refine ⟨Real.exp (2 * L ^ 2 * A), Real.exp_pos _, fun N _ => ?_⟩
  set a := circleSpacing L N
  set ha := circleSpacing_pos L N
  set μ := latticeGaussianMeasure 2 N a mass ha hmass
  haveI : IsProbabilityMeasure μ := latticeGaussianMeasure_isProbability 2 N a mass ha hmass
  -- Step 3: V(ω) ≥ -(a² · |Λ| · A) = -(L² · A) for all ω
  have hc_nn : 0 ≤ wickConstant 2 N a mass :=
    le_of_lt (wickConstant_pos 2 N a mass ha hmass)
  have hc_le : wickConstant 2 N a mass ≤ mass⁻¹ ^ 2 :=
    wickConstant_le_inv_mass_sq 2 N a mass ha hmass
  set Λ := Fintype.card (FinLatticeSites 2 N)
  -- Key identity: a² · Λ = L² (since a = L/N and Λ = N²)
  have hΛ_eq : (Λ : ℝ) = (N : ℝ) ^ 2 := by
    change (Fintype.card (Fin 2 → ZMod N) : ℝ) = (N : ℝ) ^ 2
    simp [ZMod.card]
  have ha_eq : a = L / (N : ℝ) := rfl
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have ha_sq_Λ : a ^ 2 * (Λ : ℝ) = L ^ 2 := by
    rw [hΛ_eq, ha_eq]
    field_simp
  have h_wp_bound : ∀ (ω : Configuration (FinLatticeField 2 N)),
      interactionFunctional 2 N P a mass ω ≥ -(L ^ 2 * A) := by
    intro ω
    unfold interactionFunctional
    have ha_pow : (0 : ℝ) ≤ a ^ 2 := sq_nonneg a
    calc a ^ 2 * ∑ x : FinLatticeSites 2 N,
          wickPolynomial P (wickConstant 2 N a mass) (ω (finLatticeDelta 2 N x))
        ≥ a ^ 2 * ∑ _x : FinLatticeSites 2 N, (-A) := by
          apply mul_le_mul_of_nonneg_left _ ha_pow
          exact Finset.sum_le_sum fun x _ => hA_bound _ hc_nn hc_le _
      _ = a ^ 2 * (-(↑Λ * A)) := by
          congr 1; rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
      _ = -(a ^ 2 * ↑Λ * A) := by ring
      _ = -(L ^ 2 * A) := by rw [ha_sq_Λ]
  -- Step 4: exp(-2V) ≤ exp(2 · L² · A) pointwise
  have h_exp_bound : ∀ ω, (Real.exp (-interactionFunctional 2 N P a mass ω)) ^ 2 ≤
      Real.exp (2 * L ^ 2 * A) := by
    intro ω
    rw [sq, ← Real.exp_add, show -interactionFunctional 2 N P a mass ω +
        (-interactionFunctional 2 N P a mass ω) =
        -2 * interactionFunctional 2 N P a mass ω from by ring]
    exact Real.exp_le_exp_of_le (by linarith [h_wp_bound ω])
  -- Step 5: Integrate the pointwise bound over the probability measure
  calc ∫ ω, (Real.exp (-interactionFunctional 2 N P a mass ω)) ^ 2 ∂μ
      ≤ ∫ _ω, Real.exp (2 * L ^ 2 * A) ∂μ := by
        apply integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
          (integrable_const _) (ae_of_all _ h_exp_bound)
    _ = Real.exp (2 * L ^ 2 * A) := by
        simp [integral_const]

end Pphi2

end
