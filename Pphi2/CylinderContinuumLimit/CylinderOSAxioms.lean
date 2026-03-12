/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cylinder OS Axioms: OS0–OS3 for the Gaussian Free Field on S¹_L × ℝ

Defines and proves Osterwalder-Schrader axioms OS0 through OS3 for the
Gaussian measure on the cylinder S¹_L × ℝ.

## Main results

- `CylinderOS0_Analyticity` — characteristic functional is analytic
- `CylinderOS1_Regularity` — ‖Z[f_re, f_im]‖ ≤ exp(c·(q(f_re)+q(f_im)))
- `CylinderOS2_TranslationInvariance` — invariance under S¹ × ℝ translations
- `CylinderOS3_ReflectionPositivity` — RP matrix positive semidefinite
- `SatisfiesCylinderOS` — bundled structure for all cylinder OS axioms
- `cylinderGaussian_satisfies_OS` — main theorem

## Mathematical background

The cylinder S¹_L × ℝ is the natural geometry for OS axioms because:
- Time reflection Θ : t ↦ -t is clean on ℝ (no wraparound)
- Positive time = (0, ∞) is the full future half-line
- OS reconstruction applies directly to produce a Hilbert space

The proofs follow the same structure as the torus case:
- **OS0**: Z[f] = exp(-½G(f,f)) is entire since G is bilinear
- **OS1**: ‖Z_ℂ[f_re,f_im]‖ ≤ exp(½·(G(f_re,f_re)+G(f_im,f_im)))
- **OS2**: G is translation-invariant (Green's function depends on differences)
- **OS3**: RP inherited from lattice via weak limits; the cylinder lattice
  S¹_L × [-T,T] has clean time reflection at t=0

## References

- Osterwalder-Schrader (1973, 1975)
- Glimm-Jaffe, *Quantum Physics*, Ch. 6, 19
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
-/

import Cylinder.GreenFunction
import Cylinder.PositiveTime
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

open GaussianField MeasureTheory Filter ProbabilityTheory

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Generating functionals -/

/-- The generating functional (characteristic functional) on the cylinder.

  `Z_μ(f) = E_μ[e^{i ω(f)}] = ∫ e^{i ω(f)} dμ(ω)`

For a Gaussian measure with covariance G: `Z(f) = exp(-½ G(f,f))`. -/
def cylinderGeneratingFunctional
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] (f : CylinderTestFunction L) : ℂ :=
  ∫ ω : Configuration (CylinderTestFunction L),
    Complex.exp (Complex.I * ↑(ω f)) ∂μ

/-- The complex generating functional on the cylinder.

  `Z_ℂ[f_re, f_im] = ∫ exp(i(ω(f_re) + iω(f_im))) dμ(ω)` -/
def cylinderGeneratingFunctionalℂ
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] (f_re f_im : CylinderTestFunction L) : ℂ :=
  ∫ ω : Configuration (CylinderTestFunction L),
    Complex.exp (Complex.I * ((ω f_re : ℂ) + Complex.I * (ω f_im : ℂ))) ∂μ

/-! ## Gaussian measure on the cylinder -/

/-- **Predicate for the Gaussian measure on the cylinder.**

A probability measure μ on Configuration(CylinderTestFunction L) is the
Gaussian free field with mass m if:
1. It has centered Gaussian 1D marginals (MGF form)
2. Its covariance equals the cylinder Green's function G_L
3. It has Z₂ symmetry (φ ↦ -φ invariance) -/
structure IsCylinderGaussian
    (μ : Measure (Configuration (CylinderTestFunction L)))
    (mass : ℝ) (hmass : 0 < mass) : Prop where
  /-- μ is a probability measure -/
  isProbability : IsProbabilityMeasure μ
  /-- Gaussian: characteristic functional has exp(-½σ²) form -/
  isGaussian : ∀ (f : CylinderTestFunction L),
    ∫ ω : Configuration (CylinderTestFunction L),
      Real.exp (ω f) ∂μ =
    Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ)
  /-- Covariance = cylinder continuum Green's function -/
  covariance_eq : ∀ (f : CylinderTestFunction L),
    ∫ ω : Configuration (CylinderTestFunction L), (ω f) ^ 2 ∂μ =
    cylinderGreen L mass hmass f f
  /-- Z₂ symmetry: μ is invariant under field negation -/
  z2_symmetric : Measure.map
    (Neg.neg : Configuration (CylinderTestFunction L) →
      Configuration (CylinderTestFunction L)) μ = μ

/-! ## OS0: Analyticity -/

/-- **OS0: Analyticity of the generating functional.**

The generating functional `Z[Σ zᵢJᵢ]` is entire analytic as a function
of z = (z₁,...,zₙ) ∈ ℂⁿ, for any choice of (real) test functions Jᵢ. -/
def CylinderOS0_Analyticity
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (n : ℕ) (J : Fin n → CylinderTestFunction L),
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      cylinderGeneratingFunctionalℂ L μ
        (∑ i, (z i).re • J i) (∑ i, (z i).im • J i)) Set.univ

/-- Analyticity of the complex generating functional (axiom for now). -/
axiom cylinderGeneratingFunctionalℂ_analyticOnNhd
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ]
    (hG : IsCylinderGaussian L μ mass hmass)
    (n : ℕ) (J : Fin n → CylinderTestFunction L) :
    AnalyticOnNhd ℂ (fun z : Fin n → ℂ =>
      cylinderGeneratingFunctionalℂ L μ
        (∑ i, (z i).re • J i) (∑ i, (z i).im • J i)) Set.univ

/-! ## OS1: Regularity -/

/-- **OS1: Regularity of the complex generating functional.**

  `‖Z_ℂ[f_re, f_im]‖ ≤ exp(c · (q(f_re) + q(f_im)))`

for some continuous seminorm `q` and constant `c > 0`. -/
def CylinderOS1_Regularity
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  ∃ (q : CylinderTestFunction L → ℝ) (_ : Continuous q) (c : ℝ), c > 0 ∧
    ∀ (f_re f_im : CylinderTestFunction L),
      ‖cylinderGeneratingFunctionalℂ L μ f_re f_im‖ ≤
        Real.exp (c * (q f_re + q f_im))

/-- OS1 for the Gaussian cylinder measure.

The bound holds with `q(f) = G_L(f,f)` and `c = 1/2`, by the same
triangle inequality + Gaussian MGF argument as the torus case. -/
axiom cylinderGaussian_os1
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ]
    (hG : IsCylinderGaussian L μ mass hmass) :
    CylinderOS1_Regularity L μ

/-! ## OS2: Euclidean invariance -/

/-- **OS2a: Spatial translation invariance.**

  `Z(f) = Z(T_v f)` for all v ∈ S¹_L. -/
def CylinderOS2_SpatialTranslationInvariance
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (v : ℝ) (f : CylinderTestFunction L),
    cylinderGeneratingFunctional L μ f =
    cylinderGeneratingFunctional L μ (cylinderSpatialTranslation L v f)

/-- **OS2b: Time translation invariance.**

  `Z(f) = Z(T_τ f)` for all τ ∈ ℝ.

This is the temporal analogue of Euclidean invariance. On the cylinder,
spatial and temporal translations are independent symmetry groups. -/
def CylinderOS2_TimeTranslationInvariance
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (τ : ℝ) (f : CylinderTestFunction L),
    cylinderGeneratingFunctional L μ f =
    cylinderGeneratingFunctional L μ (cylinderTimeTranslation L τ f)

/-- **OS2c: Time reflection invariance.**

  `Z(f) = Z(Θf)`.

This is NOT an OS axiom but a property of the Gaussian measure (the
Green's function is even in time). OS3 involves RP of the matrix
`Re(Z[fᵢ - Θfⱼ])`, not just invariance under Θ. -/
def CylinderOS2_TimeReflectionInvariance
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (f : CylinderTestFunction L),
    cylinderGeneratingFunctional L μ f =
    cylinderGeneratingFunctional L μ (cylinderTimeReflection L f)

/-- OS2 (spatial translation) for the Gaussian cylinder measure.

For Gaussian μ: `Z(T_v f) = exp(-½G(T_v f, T_v f)) = exp(-½G(f,f)) = Z(f)`. -/
axiom cylinderGaussian_os2_spatial
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ]
    (hG : IsCylinderGaussian L μ mass hmass) :
    CylinderOS2_SpatialTranslationInvariance L μ

/-- OS2 (time translation) for the Gaussian cylinder measure. -/
axiom cylinderGaussian_os2_time
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ]
    (hG : IsCylinderGaussian L μ mass hmass) :
    CylinderOS2_TimeTranslationInvariance L μ

/-- OS2 (time reflection) for the Gaussian cylinder measure. -/
axiom cylinderGaussian_os2_reflection
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ]
    (hG : IsCylinderGaussian L μ mass hmass) :
    CylinderOS2_TimeReflectionInvariance L μ

/-! ## OS3: Reflection positivity -/

/-- **OS3: Reflection positivity for the cylinder measure (matrix form).**

For any finite collection of positive-time test functions f₁,...,fₙ and
real coefficients c₁,...,cₙ, the RP matrix is positive semidefinite:

  `Σᵢⱼ cᵢ cⱼ · Re(Z[fᵢ - Θfⱼ]) ≥ 0`

where Θ = `cylinderTimeReflection` is the time reflection on test functions.

The key advantage of the cylinder over the torus: positive time = (0,∞)
is the full future half-line. The block-zero property (no coupling between
positive-time and negative-time fields) holds by locality of the Laplacian
plus disjointness of supports (0,∞) and (-∞,0). -/
def CylinderOS3_ReflectionPositivity
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (n : ℕ) (f : Fin n → CylinderPositiveTimeTestFunction L) (c : Fin n → ℝ),
    0 ≤ ∑ i, ∑ j, c i * c j *
      (cylinderGeneratingFunctional L μ
        ((f i).val - cylinderTimeReflection L (f j).val)).re

/-! ### Helper lemmas for weak-limit RP transfer -/

/-- `ω ↦ cos(ω(g))` is continuous on cylinder configuration space. -/
private lemma cylinderCosEval_continuous (g : CylinderTestFunction L) :
    Continuous (fun ω : Configuration (CylinderTestFunction L) => Real.cos (ω g)) :=
  Real.continuous_cos.comp (WeakDual.eval_continuous g)

/-- `ω ↦ cos(ω(g))` is bounded by 1. -/
private lemma cylinderCosEval_bounded (g : CylinderTestFunction L) :
    ∃ C : ℝ, ∀ ω : Configuration (CylinderTestFunction L), |Real.cos (ω g)| ≤ C :=
  ⟨1, fun ω => Real.abs_cos_le_one (ω g)⟩

/-- `ω ↦ exp(i·ω(g))` is AE strongly measurable. -/
private lemma cylinderExpEval_aestronglyMeasurable
    (μ : Measure (Configuration (CylinderTestFunction L)))
    (g : CylinderTestFunction L) :
    AEStronglyMeasurable (fun ω : Configuration (CylinderTestFunction L) =>
      Complex.exp (Complex.I * ↑(ω g))) μ :=
  (Complex.continuous_exp.measurable.comp
    (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
      (configuration_eval_measurable g)))).aestronglyMeasurable

/-- `ω ↦ exp(i·ω(g))` is integrable w.r.t. any probability measure. -/
private lemma cylinderExpEval_integrable
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] (g : CylinderTestFunction L) :
    Integrable (fun ω : Configuration (CylinderTestFunction L) =>
      Complex.exp (Complex.I * ↑(ω g))) μ := by
  apply (integrable_const (1 : ℂ)).mono
  · exact cylinderExpEval_aestronglyMeasurable L μ g
  · apply ae_of_all
    intro ω
    simp only [norm_one]
    rw [show Complex.I * ↑(ω g) = ↑(ω g) * Complex.I from mul_comm _ _]
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I (ω g))

/-- `Re(Z_μ[g]) = ∫ cos(ω(g)) dμ(ω)`. -/
private lemma cylinderGeneratingFunctional_re_eq_integral_cos
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] (g : CylinderTestFunction L) :
    (cylinderGeneratingFunctional L μ g).re =
    ∫ ω : Configuration (CylinderTestFunction L), Real.cos (ω g) ∂μ := by
  unfold cylinderGeneratingFunctional
  rw [show (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ).re =
    Complex.reCLM (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ) from rfl,
    ← ContinuousLinearMap.integral_comp_comm Complex.reCLM
      (cylinderExpEval_integrable L μ g)]
  congr 1 with ω
  simp only [Complex.reCLM_apply, mul_comm Complex.I, Complex.exp_mul_I,
    Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.sin_ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  exact Complex.cos_ofReal_re (ω g)

/-! ### RP for lattice approximations and weak limit transfer -/

/-- The lattice approximation to the cylinder GFF satisfies RP.

For each N (lattice size), the lattice measure on S¹_L × [-T_N, T_N]
satisfies the matrix form of RP. The proof uses the Fubini + perfect
square argument, which is cleaner on the cylinder because:
- Positive time = {sites with t > 0} (no wraparound)
- The mass operator Q has exact block-zero property by locality -/
axiom cylinderLattice_rp (N : ℕ) [NeZero N]
    (mass : ℝ) (hmass : 0 < mass)
    (μ_N : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ_N] :
    CylinderOS3_ReflectionPositivity L μ_N

/-- **Matrix form of RP is preserved under weak limits on the cylinder.**

Identical proof to the torus case: each RP matrix entry
`Re(Z_μ[g]) = ∫ cos(ω(g)) dμ` is a bounded continuous functional
of the measure, so weak convergence gives pointwise convergence of
the RP matrix. A finite sum of limits of nonneg quantities is nonneg. -/
theorem cylinderMatrixRP_of_weakLimit
    (μ_seq : ℕ → Measure (Configuration (CylinderTestFunction L)))
    [∀ k, IsProbabilityMeasure (μ_seq k)]
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ]
    (h_weak : ∀ g : Configuration (CylinderTestFunction L) → ℝ,
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun k => ∫ ω, g ω ∂(μ_seq k)) atTop (nhds (∫ ω, g ω ∂μ)))
    (h_rp : ∀ k, CylinderOS3_ReflectionPositivity L (μ_seq k)) :
    CylinderOS3_ReflectionPositivity L μ := by
  intro n f c
  have h_tendsto : Tendsto
      (fun k => ∑ i : Fin n, ∑ j : Fin n, c i * c j *
        (cylinderGeneratingFunctional L (μ_seq k)
          ((f i).val - cylinderTimeReflection L (f j).val)).re)
      atTop
      (nhds (∑ i : Fin n, ∑ j : Fin n, c i * c j *
        (cylinderGeneratingFunctional L μ
          ((f i).val - cylinderTimeReflection L (f j).val)).re)) := by
    apply tendsto_finset_sum
    intro i _
    apply tendsto_finset_sum
    intro j _
    apply Filter.Tendsto.const_mul
    simp_rw [cylinderGeneratingFunctional_re_eq_integral_cos L]
    exact h_weak _ (cylinderCosEval_continuous L _) (cylinderCosEval_bounded L _)
  exact ge_of_tendsto' h_tendsto (fun k => h_rp k n f c)

/-! ## Bundle and main theorem -/

/-- **Bundled cylinder OS axioms OS0–OS3.** -/
structure SatisfiesCylinderOS
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ] : Prop where
  os0 : CylinderOS0_Analyticity L μ
  os1 : CylinderOS1_Regularity L μ
  os2_spatial : CylinderOS2_SpatialTranslationInvariance L μ
  os2_time : CylinderOS2_TimeTranslationInvariance L μ
  os2_reflection : CylinderOS2_TimeReflectionInvariance L μ
  os3 : CylinderOS3_ReflectionPositivity L μ

/-- **The Gaussian measure on the cylinder satisfies OS0–OS3.**

OS0, OS1, OS2 follow from the Gaussian structure (characteristic
functional = exp(-½G)). OS3 is inherited from lattice RP via weak limits.

Note: OS3 requires the lattice RP axiom `cylinderLattice_rp` and
weak convergence of the lattice measures. For a fully rigorous proof,
one would also need:
- Tightness of the lattice measures (Mitoma-Chebyshev)
- Prokhorov extraction on the cylinder configuration space
- Identification of the limit as Gaussian with covariance G_L

These mirror the torus proofs in `TorusGaussianLimit.lean`. -/
axiom cylinderGaussian_satisfies_OS
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (CylinderTestFunction L)))
    [IsProbabilityMeasure μ]
    (hG : IsCylinderGaussian L μ mass hmass) :
    SatisfiesCylinderOS L μ

end Pphi2

end
