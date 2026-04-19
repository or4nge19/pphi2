/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tightness of the Continuum-Embedded Measures

Shows that the family of continuum-embedded measures `{ν_a}_{a>0}` is tight
in S'(ℝ²). This is the key technical step enabling extraction of a
convergent subsequence via Prokhorov's theorem.

## Main results

- `second_moment_uniform` — uniform bound on `∫ |Φ_a(f)|² dν_a`
- `moment_equicontinuity` — equicontinuity of moments in f
- `continuumMeasures_tight` — tightness of {ν_a} in S'(ℝ²)

## Mathematical background

### Tightness criterion (Mitoma)

A family of probability measures {ν_α} on S'(ℝ^d) is tight iff for each
f ∈ S(ℝ^d), the real-valued random variables {Φ_α(f)} are tight on ℝ.

By Chebyshev, tightness of {Φ_α(f)} on ℝ follows from uniform second
moment bounds: `sup_α ∫ |Φ_α(f)|² dν_α < ∞`.

### Uniform moment bounds

The key input is Nelson's hypercontractive estimate, which gives:

  `∫ |Φ_a(f)|² dμ_a ≤ C · ‖f‖²_{H^{-1}}`

uniformly in a, where `‖f‖_{H^{-1}}` is the Sobolev H^{-1} norm.

For the interacting measure, the bound follows from:
1. The Gaussian two-point function: `∫ Φ_a(f)² dμ_{GFF} = ⟨f, G_a f⟩`
2. The interaction only improves decay: `∫ Φ_a(f)² dμ_a ≤ e^C · ∫ Φ_a(f)² dμ_{GFF}`
3. The lattice propagator converges: `⟨f, G_a f⟩ → ⟨f, G f⟩`

## References

- Mitoma (1983), "Tightness of probabilities on C([0,1]; S') and D([0,1]; S')"
- Simon, *The P(φ)₂ Euclidean QFT*, §V.1
- Glimm-Jaffe, *Quantum Physics*, §19.4
-/

import Pphi2.ContinuumLimit.Hypercontractivity
import Pphi2.GaussianContinuumLimit.GaussianTightness

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (d N : ℕ) [NeZero N] [Fact (0 < d)]

-- NOTE: second_moment_uniform and moment_equicontinuity were removed as dead
-- axioms (never referenced by any actual Lean code outside this file).
-- We retain only the live tightness theorem needed by Prokhorov extraction.

/-! ## Uniform second moment bounds -/

/-- **Uniform interacting second-moment bound.**

The continuum-embedded interacting measures inherit a uniform `L²` bound from
the proved moment estimate `interacting_moment_bound` together with the Gaussian
uniform second-moment bound `gaussian_second_moment_uniform`. -/
theorem continuum_second_moment_uniform (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) (f : ContinuumTestFunction d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
      ∫ ω : Configuration (ContinuumTestFunction d),
        (ω f) ^ 2 ∂(continuumMeasure d N P a mass ha hmass) ≤ C := by
  obtain ⟨Cint, hCint_pos, hCint⟩ := interacting_moment_bound d N P mass hmass
  obtain ⟨Cg, hCg_pos, hCg⟩ := gaussian_second_moment_uniform d N mass hmass f
  refine ⟨3 * Cint * Cg, mul_pos (mul_pos (by norm_num) hCint_pos) hCg_pos, ?_⟩
  intro a ha ha_le
  have h_int := hCint 1 2 1 (by norm_num) (by norm_num) f a ha ha_le
  have h_gauss := hCg a ha ha_le
  have h_lhs_eq :
      ∫ ω : Configuration (ContinuumTestFunction d),
          |ω f| ^ ((2 : ℝ) * ↑(1 : ℕ)) ∂(continuumMeasure d N P a mass ha hmass) =
      ∫ ω : Configuration (ContinuumTestFunction d),
          (ω f) ^ 2 ∂(continuumMeasure d N P a mass ha hmass) := by
    congr 1
    ext ω
    rw [show ((2 : ℝ) * ↑(1 : ℕ)) = (2 : ℝ) by norm_num]
    simp [sq_abs]
  have h_rhs_eq :
      (∫ ω : Configuration (ContinuumTestFunction d),
          |ω f| ^ (2 * ↑(1 : ℕ)) ∂(Measure.map (latticeEmbedLift d N a ha)
            (latticeGaussianMeasure d N a mass ha hmass))) ^ ((2 : ℝ) / 2) =
      ∫ ω : Configuration (ContinuumTestFunction d),
          (ω f) ^ 2 ∂(gaussianContinuumMeasure d N a mass ha hmass) := by
    rw [show ((2 : ℝ) / 2) = (1 : ℝ) by norm_num, Real.rpow_one]
    simp [gaussianContinuumMeasure, sq_abs]
  rw [h_lhs_eq] at h_int
  calc
    ∫ ω : Configuration (ContinuumTestFunction d),
        (ω f) ^ 2 ∂(continuumMeasure d N P a mass ha hmass)
      ≤ Cint * (2 * (2 : ℝ) - 1) ^ ((2 : ℝ) * ↑(1 : ℕ) / 2) *
          (∫ ω : Configuration (ContinuumTestFunction d),
            |ω f| ^ (2 * ↑(1 : ℕ)) ∂(Measure.map (latticeEmbedLift d N a ha)
              (latticeGaussianMeasure d N a mass ha hmass))) ^ ((2 : ℝ) / 2) := h_int
    _ = Cint * 3 *
          ∫ ω : Configuration (ContinuumTestFunction d),
            (ω f) ^ 2 ∂(gaussianContinuumMeasure d N a mass ha hmass) := by
          rw [h_rhs_eq, show ((2 : ℝ) * ↑(1 : ℕ) / 2) = (1 : ℝ) by norm_num, Real.rpow_one]
          ring
    _ ≤ Cint * 3 * Cg := by
          apply mul_le_mul_of_nonneg_left h_gauss
          positivity
    _ = 3 * Cint * Cg := by ring

omit [Fact (0 < d)] in
/-- Integrability of evaluation-squared through the continuum embedding. -/
theorem continuumMeasure_sq_integrable
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : ContinuumTestFunction d) :
    Integrable (fun ω : Configuration (ContinuumTestFunction d) =>
      (ω f) ^ 2) (continuumMeasure d N P a mass ha hmass) := by
  unfold continuumMeasure
  rw [integrable_map_measure
    ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable
    (latticeEmbedLift_measurable d N a ha).aemeasurable]
  set g := latticeTestField d N a f
  have h_eq :
      ((fun ω : Configuration (ContinuumTestFunction d) => (ω f) ^ 2) ∘
          latticeEmbedLift d N a ha) =
      fun ω : Configuration (FinLatticeField d N) => (ω g) ^ 2 := by
    ext ω
    simp [Function.comp, g, latticeEmbedLift_eval_eq d N a ha f ω]
  rw [h_eq]
  obtain ⟨B, hB⟩ := interactionFunctional_bounded_below d N P a mass ha hmass
  have hZ := partitionFunction_pos d N P a mass ha hmass
  set μ_GFF := latticeGaussianMeasure d N a mass ha hmass
  set bw := boltzmannWeight d N P a mass
  suffices h :
      Integrable (fun ω : Configuration (FinLatticeField d N) => (ω g) ^ 2)
        (μ_GFF.withDensity (fun ω => ENNReal.ofReal (bw ω))) by
    unfold interactingLatticeMeasure
    exact h.smul_measure (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr hZ).ne'))
  have hf_meas : Measurable (fun ω : Configuration (FinLatticeField d N) =>
      ENNReal.ofReal (bw ω)) :=
    ENNReal.measurable_ofReal.comp ((interactionFunctional_measurable d N P a mass).neg.exp)
  apply (integrable_withDensity_iff hf_meas
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  have hbw_simp : ∀ ω : Configuration (FinLatticeField d N),
      (ENNReal.ofReal (bw ω)).toReal = bw ω :=
    fun ω => ENNReal.toReal_ofReal (le_of_lt (boltzmannWeight_pos d N P a mass ω))
  simp_rw [hbw_simp]
  have h_sq_int : Integrable (fun ω : Configuration (FinLatticeField d N) =>
      (ω g) ^ 2) μ_GFF := by
    set T := latticeCovariance d N a mass ha hmass
    have h_gauss := pairing_is_gaussian T g
    have h_int_gauss : Integrable (fun x : ℝ => x ^ 2)
        (ProbabilityTheory.gaussianReal 0 (@inner ℝ _ _ (T g) (T g) : ℝ).toNNReal) :=
      ProbabilityTheory.integrable_pow_of_mem_interior_integrableExpSet (by simp) 2
    rw [← h_gauss] at h_int_gauss
    rwa [integrable_map_measure h_int_gauss.aestronglyMeasurable
      (configuration_eval_measurable g).aemeasurable] at h_int_gauss
  apply (h_sq_int.mul_const (Real.exp B)).mono
  · exact ((configuration_eval_measurable g).pow_const 2).aestronglyMeasurable.mul
      ((interactionFunctional_measurable d N P a mass).neg.exp.aestronglyMeasurable)
  · exact Filter.Eventually.of_forall fun ω => by
      simp only [Real.norm_eq_abs]
      have h1 : 0 ≤ (ω g) ^ 2 := sq_nonneg _
      have h2 : 0 < bw ω := boltzmannWeight_pos d N P a mass ω
      have h3 : bw ω ≤ Real.exp B := by
        change Real.exp (-interactionFunctional d N P a mass ω) ≤ Real.exp B
        exact Real.exp_le_exp_of_le (by linarith [hB ω])
      rw [abs_of_nonneg (mul_nonneg h1 (le_of_lt h2)),
          abs_of_nonneg (mul_nonneg h1 (le_of_lt (Real.exp_pos B)))]
      exact mul_le_mul_of_nonneg_left h3 h1

/-! ## Tightness -/

/-- **Tightness of the continuum-embedded measures.**

The family `{ν_a = (ι_a)_* μ_a}_{a ∈ (0, 1]}` is tight in the space of
probability measures on `S'(ℝ^d) = Configuration (ContinuumTestFunction d)`.

Proof:
1. By Mitoma's criterion, it suffices to show that for each f ∈ S(ℝ^d),
   the real-valued measures `(ev_f)_* ν_a` are tight on ℝ.
2. By Chebyshev's inequality, tightness on ℝ follows from the uniform
   second moment bound `∫ |Φ_a(f)|² dν_a ≤ C(f)`.
3. The uniform bound is provided by `continuum_second_moment_uniform`. -/
theorem continuumMeasures_tight (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) :
    -- The family {ν_a}_{a ∈ (0,1]} is tight on Configuration (ContinuumTestFunction d)
    -- Stated as: for every ε > 0, there exists a compact K such that
    -- ν_a(K) ≥ 1 - ε for all a ∈ (0, 1].
    ∀ ε : ℝ, 0 < ε →
    ∃ (K : Set (Configuration (ContinuumTestFunction d))),
      IsCompact K ∧
      ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
      1 - ε ≤ (continuumMeasure d N P a mass ha hmass K).toReal := by
  intro ε hε
  have hd : 0 < d := Fact.out
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) := inferInstance
  haveI : DyninMityaginSpace (ContinuumTestFunction d) :=
    schwartz_dyninMityaginSpace
  set ι := { a : ℝ // 0 < a ∧ a ≤ 1 }
  set μ : ι → Measure (Configuration (ContinuumTestFunction d)) :=
    fun i => continuumMeasure d N P i.val mass i.prop.1 hmass
  have hprob : ∀ i : ι, IsProbabilityMeasure (μ i) := by
    intro i
    dsimp [μ]
    exact continuumMeasure_isProbability d N P i.val mass i.prop.1 hmass
  have h_int :
      ∀ (f : ContinuumTestFunction d) (i : ι),
      Integrable (fun ω : Configuration (ContinuumTestFunction d) =>
        (ω f) ^ 2) (μ i) := by
    intro f i
    simpa [μ] using continuumMeasure_sq_integrable d N P i.val mass i.prop.1 hmass f
  have h_moments :
      ∀ f : ContinuumTestFunction d, ∃ C : ℝ, ∀ i : ι,
      ∫ ω : Configuration (ContinuumTestFunction d),
        (ω f) ^ 2 ∂(μ i) ≤ C := by
    intro f
    obtain ⟨C, _, hC⟩ := continuum_second_moment_uniform d N P mass hmass f
    exact ⟨C, fun i => by simpa [μ] using hC i.val i.prop.1 i.prop.2⟩
  obtain ⟨K, hK_compact, hK_mass⟩ :=
    configuration_tight_of_uniform_second_moments
      μ hprob h_int h_moments ε hε
  exact ⟨K, hK_compact, fun a ha ha_le => hK_mass ⟨a, ha, ha_le⟩⟩

end Pphi2

end
