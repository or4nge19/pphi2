/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# General Interacting Measure Theory

Given a probability measure μ_free on a configuration space and an interaction
functional V that is measurable and bounded below, constructs:
- Boltzmann weight exp(-V)
- Partition function Z = ∫ exp(-V) dμ_free
- Interacting measure μ_V = (1/Z) exp(-V) dμ_free
- Schwinger functions and generating functional

These results are spacetime-independent: they apply to any QFT
(lattice, cylinder, torus, plane) once the interaction is specified.

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. II, VIII
- Glimm-Jaffe, *Quantum Physics*, §19.1
-/

import GaussianField.Construction

open GaussianField MeasureTheory

noncomputable section

namespace Pphi2

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-! ## Boltzmann weight -/

/-- **Boltzmann weight** `exp(-V(ω))` for a general interaction functional V. -/
def interactingBoltzmannWeight
    (V : Configuration E → ℝ) : Configuration E → ℝ :=
  fun ω => Real.exp (-(V ω))

/-- The Boltzmann weight is strictly positive everywhere. -/
theorem interactingBoltzmannWeight_pos
    (V : Configuration E → ℝ) (ω : Configuration E) :
    0 < interactingBoltzmannWeight V ω :=
  Real.exp_pos _

/-- **Integrability of the Boltzmann weight** with respect to any probability measure,
given that V is measurable and bounded below.

Follows from V bounded below (so exp(-V) ≤ exp(B)) and finite total mass. -/
theorem interactingBoltzmannWeight_integrable
    (V : Configuration E → ℝ)
    (μ : Measure (Configuration E))
    [IsProbabilityMeasure μ]
    (hV_meas : Measurable V)
    (hV_below : ∃ B : ℝ, ∀ ω, V ω ≥ -B) :
    Integrable (interactingBoltzmannWeight V) μ := by
  obtain ⟨B, hB⟩ := hV_below
  have hmeas : Measurable (interactingBoltzmannWeight V) := hV_meas.neg.exp
  apply (memLp_of_bounded (a := 0) (b := Real.exp B)
    (ae_of_all _ (fun ω => ?_)) hmeas.aestronglyMeasurable (p := 1)).integrable le_rfl
  exact ⟨le_of_lt (interactingBoltzmannWeight_pos V ω),
    Real.exp_le_exp_of_le (by linarith [hB ω])⟩

/-- The Boltzmann weight is measurable as an ENNReal-valued function. -/
theorem interactingBoltzmannWeight_ennreal_measurable
    (V : Configuration E → ℝ)
    (hV_meas : Measurable V) :
    Measurable (fun ω : Configuration E =>
      ENNReal.ofReal (interactingBoltzmannWeight V ω)) :=
  hV_meas.neg.exp.ennreal_ofReal

/-! ## Partition function -/

/-- **Partition function** `Z = ∫ exp(-V(ω)) dμ_free(ω)`. -/
def interactingPartitionFunction
    (V : Configuration E → ℝ)
    (μ : Measure (Configuration E)) : ℝ :=
  ∫ ω, interactingBoltzmannWeight V ω ∂μ

/-- The partition function is strictly positive.

Proof: `exp(-V) > 0` everywhere and the probability measure has full support. -/
theorem interactingPartitionFunction_pos
    (V : Configuration E → ℝ)
    (μ : Measure (Configuration E))
    [IsProbabilityMeasure μ]
    (hV_meas : Measurable V)
    (hV_below : ∃ B : ℝ, ∀ ω, V ω ≥ -B) :
    0 < interactingPartitionFunction V μ := by
  unfold interactingPartitionFunction
  rw [integral_pos_iff_support_of_nonneg
    (fun ω => le_of_lt (interactingBoltzmannWeight_pos V ω))
    (interactingBoltzmannWeight_integrable V μ hV_meas hV_below)]
  have h_support : Function.support (interactingBoltzmannWeight V) = Set.univ := by
    ext ω
    simp [Function.mem_support, ne_of_gt (interactingBoltzmannWeight_pos V ω)]
  rw [h_support, measure_univ]
  norm_num

/-! ## Interacting measure -/

/-- **Interacting measure** `dμ_V = (1/Z) · exp(-V) · dμ_free`. -/
def interactingMeasure
    (V : Configuration E → ℝ)
    (μ : Measure (Configuration E)) :
    Measure (Configuration E) :=
  (ENNReal.ofReal (interactingPartitionFunction V μ))⁻¹ •
    μ.withDensity (fun ω => ENNReal.ofReal (interactingBoltzmannWeight V ω))

/-- The withDensity measure has total mass equal to the partition function. -/
theorem interactingWithDensity_mass
    (V : Configuration E → ℝ)
    (μ : Measure (Configuration E))
    [IsProbabilityMeasure μ]
    (hV_meas : Measurable V)
    (hV_below : ∃ B : ℝ, ∀ ω, V ω ≥ -B) :
    μ.withDensity (fun ω => ENNReal.ofReal (interactingBoltzmannWeight V ω))
      Set.univ =
    ENNReal.ofReal (interactingPartitionFunction V μ) := by
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ, MeasureTheory.setLIntegral_univ]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (interactingBoltzmannWeight_integrable V μ hV_meas hV_below)
    (ae_of_all _ fun ω =>
      le_of_lt (interactingBoltzmannWeight_pos V ω))).symm

/-- **The interacting measure is a probability measure.** `μ_V(univ) = (1/Z) · Z = 1`. -/
theorem interactingMeasure_isProbabilityMeasure
    (V : Configuration E → ℝ)
    (μ : Measure (Configuration E))
    [IsProbabilityMeasure μ]
    (hV_meas : Measurable V)
    (hV_below : ∃ B : ℝ, ∀ ω, V ω ≥ -B) :
    IsProbabilityMeasure (interactingMeasure V μ) := by
  constructor
  show (interactingMeasure V μ) Set.univ = 1
  simp only [interactingMeasure, Measure.smul_apply, smul_eq_mul]
  rw [interactingWithDensity_mass V μ hV_meas hV_below]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr (interactingPartitionFunction_pos V μ hV_meas hV_below))
    ENNReal.ofReal_ne_top

/-! ## Schwinger functions -/

/-- **Two-point Schwinger function** `S₂(f, g) = ∫ ω(f) · ω(g) dμ_V(ω)`. -/
def schwinger2
    (V : Configuration E → ℝ)
    (μ : Measure (Configuration E))
    (f g : E) : ℝ :=
  ∫ ω : Configuration E,
    ω f * ω g ∂(interactingMeasure V μ)

/-- The two-point Schwinger function is symmetric. -/
theorem schwinger2_symm
    (V : Configuration E → ℝ)
    (μ : Measure (Configuration E))
    (f g : E) :
    schwinger2 V μ f g = schwinger2 V μ g f := by
  simp only [schwinger2]; congr 1 with ω; ring

/-- **One-point Schwinger function** (expectation value of the field). -/
def schwinger1
    (V : Configuration E → ℝ)
    (μ : Measure (Configuration E))
    (f : E) : ℝ :=
  ∫ ω : Configuration E,
    ω f ∂(interactingMeasure V μ)

/-- **Interacting generating functional** `Z_V(f) = ∫ exp(ω(f)) dμ_V(ω)`. -/
def interactingGeneratingFunctional
    (V : Configuration E → ℝ)
    (μ : Measure (Configuration E))
    (f : E) : ℝ :=
  ∫ ω : Configuration E,
    Real.exp (ω f) ∂(interactingMeasure V μ)

/-- **Schwinger function formula via the free measure.**

  `S₂(f, g) = (1/Z) ∫ ω(f) · ω(g) · exp(-V(ω)) dμ_free(ω)` -/
theorem schwinger2_eq_free_expectation
    (V : Configuration E → ℝ)
    (μ : Measure (Configuration E))
    [IsProbabilityMeasure μ]
    (hV_meas : Measurable V)
    (hV_below : ∃ B : ℝ, ∀ ω, V ω ≥ -B)
    (f g : E) :
    schwinger2 V μ f g =
    (interactingPartitionFunction V μ)⁻¹ *
    ∫ ω, ω f * ω g * interactingBoltzmannWeight V ω ∂μ := by
  simp only [schwinger2, interactingMeasure]
  rw [integral_smul_measure]
  congr 1
  · simp [ENNReal.toReal_inv, ENNReal.toReal_ofReal
      (le_of_lt (interactingPartitionFunction_pos V μ hV_meas hV_below))]
  · rw [integral_withDensity_eq_integral_toReal_smul₀
        (interactingBoltzmannWeight_ennreal_measurable V hV_meas).aemeasurable
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    congr 1 with ω
    rw [ENNReal.toReal_ofReal
      (le_of_lt (interactingBoltzmannWeight_pos V ω)),
      smul_eq_mul, mul_comm]

end Pphi2
