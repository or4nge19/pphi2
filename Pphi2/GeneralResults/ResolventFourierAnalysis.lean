/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas

# Resolvent Fourier Analysis

General Fourier-analytic identities for the massive resolvent on ℝ: L² inner
products of resolvent-multiplied Schwartz functions expressed as kernel
integrals, Fourier transform of the resolvent kernel, and rescaling between
analyst-normalized and physicist-normalized conventions.

These results are independent of any lattice, torus, or cylinder geometry and
are used by `CovarianceConvergence.lean` for the torus → cylinder Green's
function convergence.

## Main results

- `resolventMultiplier_l2Inner_eq_mathlibResolventKernel_integral` — L²
  inner product of resolvent-multiplied functions = integral against the
  resolvent kernel π/ω · exp(-2πω|t|)
- `physicalResolventMultiplier_l2Inner_eq_freeKernel_integral` — same in
  physicist normalization (kernel = exp(-ω|t|)/(2ω))
- `realFourierMultiplier_inverseSymbol_eq_convolution` — inverse resolvent
  symbol as a convolution operator
- `scaledFreeKernel_integral_eq_freeKernel_integral_of_twoPiRescale` —
  2π-rescaling identity between the two normalizations
-/

import Pphi2.GeneralResults.PeriodicResolvent1D
import Mathlib.Analysis.Fourier.Convolution

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory PeriodicResolvent1D

private theorem schwartz_l2InnerProduct_eq_integral_mul
    (f g : SchwartzMap ℝ ℝ) :
    l2InnerProduct f g = ∫ t, f t * g t := by
  let φ : SchwartzMap ℝ ℝ →L[ℝ] ℝ :=
    (SchwartzMap.integralCLM (𝕜 := ℝ) (μ := MeasureTheory.volume)).comp
      (SchwartzMap.smulLeftCLM ℝ (fun t : ℝ => g t))
  calc
    l2InnerProduct f g = ∑' n, hermiteCoeff1D n f * hermiteCoeff1D n g := by
      rfl
    _ = ∑' n, hermiteCoeff1D n f * φ (schwartzHermiteBasis1D n) := by
      congr with n
      congr 1
      calc
        hermiteCoeff1D n g = ∫ t, g t * hermiteFunction n t := rfl
        _ = φ (schwartzHermiteBasis1D n) := by
          unfold φ
          rw [ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply]
          congr 1
          ext t
          rw [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth]
          rw [schwartzHermiteBasis1D_apply, smul_eq_mul]
    _ = φ f := by
      symm
      exact schwartz_hermite_expansion_CLF φ f
    _ = ∫ t, f t * g t := by
      unfold φ
      rw [ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply]
      congr 1
      ext t
      rw [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth, smul_eq_mul]
      ring

private theorem resolventSymbol_mul_self
    (ω : ℝ) (hω : 0 < ω) (ξ : ℝ) :
    resolventSymbol ω ξ * resolventSymbol ω ξ = (ξ ^ 2 + ω ^ 2)⁻¹ := by
  have hpos : 0 < ξ ^ 2 + ω ^ 2 := by positivity
  unfold resolventSymbol
  rw [← Real.rpow_add hpos]
  have hsum : -(1 : ℝ) / 2 + -(1 : ℝ) / 2 = ((-1 : ℤ) : ℝ) := by
    norm_num
  rw [hsum]
  simpa using (Real.rpow_intCast (ξ ^ 2 + ω ^ 2) (-1 : ℤ))

private theorem resolventMultiplierCLM_comp_eq_squaredSymbol
    (ω : ℝ) (hω : 0 < ω) :
    (resolventMultiplierCLM hω).comp (resolventMultiplierCLM hω) =
      realFourierMultiplierCLM
        (fun ξ : ℝ => resolventSymbol ω ξ * resolventSymbol ω ξ)
        ((resolventSymbol_hasTemperateGrowth ω hω).mul
          (resolventSymbol_hasTemperateGrowth ω hω)) := by
  simpa [resolventMultiplierCLM] using
    (realFourierMultiplierCLM_comp
      (σ₁ := resolventSymbol ω) (σ₂ := resolventSymbol ω)
      (hσ₁ := resolventSymbol_hasTemperateGrowth ω hω)
      (hσ₂ := resolventSymbol_hasTemperateGrowth ω hω)
      (hσ₂_even := resolventSymbol_even ω))

private theorem resolventInverseSymbol_hasTemperateGrowth
    (ω : ℝ) (hω : 0 < ω) :
    Function.HasTemperateGrowth (fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹) := by
  convert
    (resolventSymbol_hasTemperateGrowth ω hω).mul
      (resolventSymbol_hasTemperateGrowth ω hω) using 1
  ext ξ
  exact (resolventSymbol_mul_self ω hω ξ).symm

theorem resolventMultiplierCLM_comp_apply_eq_inverseSymbol
    (ω : ℝ) (hω : 0 < ω) (h : SchwartzMap ℝ ℝ) :
    resolventMultiplierCLM hω (resolventMultiplierCLM hω h) =
      realFourierMultiplierCLM
        (fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
        (resolventInverseSymbol_hasTemperateGrowth ω hω)
        h := by
  have happly :=
    congr_fun (congr_arg DFunLike.coe (resolventMultiplierCLM_comp_eq_squaredSymbol ω hω)) h
  simpa [resolventSymbol_mul_self ω hω] using happly

attribute [local instance] SMulCommClass.symm in
private theorem schwartzToComplex_realFourierMultiplier_eq
    (σ : ℝ → ℝ) (hσ : σ.HasTemperateGrowth)
    (heven : ∀ ξ, σ (-ξ) = σ ξ) (f : SchwartzMap ℝ ℝ) :
    schwartzToComplex (realFourierMultiplierCLM σ hσ f) =
      SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ (schwartzToComplex f) := by
  have preserves := fourierMultiplier_preserves_real σ hσ heven
  have happly := ContinuousLinearMap.ext_iff.mp preserves f
  simp only [ContinuousLinearMap.comp_apply] at happly
  simpa [realFourierMultiplierCLM] using happly

private theorem schwartzToComplex_integral_inner_eq_ofReal_integral_mul
    (f g : SchwartzMap ℝ ℝ) :
    (∫ x, @inner ℂ ℂ _ (schwartzToComplex f x) (schwartzToComplex g x)) =
      ((∫ x, f x * g x : ℝ) : ℂ) := by
  have hfg :
      (fun x => @inner ℂ ℂ _ (schwartzToComplex f x) (schwartzToComplex g x)) =
        fun x => ((f x * g x : ℝ) : ℂ) := by
    funext x
    simp [schwartzToComplex, RCLike.inner_apply, mul_comm]
  rw [hfg]
  simpa using
    (integral_complex_ofReal (f := fun x : ℝ => f x * g x) (μ := MeasureTheory.volume))

private theorem resolventInverseSymbol_even
    (ω : ℝ) (ξ : ℝ) :
    ((-ξ) ^ 2 + ω ^ 2)⁻¹ = (ξ ^ 2 + ω ^ 2)⁻¹ := by
  ring_nf

def mathlibResolventKernelReal (ω t : ℝ) : ℝ :=
  Real.pi / ω * Real.exp (-(2 * Real.pi * ω) * |t|)

private def mathlibResolventKernelC (ω : ℝ) : ℝ → ℂ :=
  fun t => (mathlibResolventKernelReal ω t : ℂ)

theorem continuous_mathlibResolventKernelReal (ω : ℝ) :
    Continuous (mathlibResolventKernelReal ω) := by
  change Continuous (fun t : ℝ =>
    Real.pi / ω * Real.exp (-(2 * Real.pi * ω) * |t|))
  fun_prop

private theorem continuous_mathlibResolventKernelC (ω : ℝ) :
    Continuous (mathlibResolventKernelC ω) := by
  change Continuous (fun t : ℝ =>
    (((Real.pi / ω * Real.exp (-(2 * Real.pi * ω) * |t|) : ℝ)) : ℂ))
  fun_prop

private theorem integrable_mathlibResolventKernelC
    (ω : ℝ) (hω : 0 < ω) :
    Integrable (mathlibResolventKernelC ω) := by
  rw [← MeasureTheory.integrableOn_univ, ← Set.Iic_union_Ioi, MeasureTheory.integrableOn_union]
  constructor
  · let c : ℂ := ((Real.pi / ω : ℝ) : ℂ)
    let a : ℂ := ((2 * Real.pi * ω : ℝ) : ℂ)
    have ha : 0 < a.re := by
      change 0 < 2 * Real.pi * ω
      positivity
    have hmodel :
        MeasureTheory.IntegrableOn (fun t : ℝ => c * Complex.exp (a * t)) (Set.Iic 0) := by
      exact (integrableOn_exp_mul_complex_Iic ha 0).const_mul c
    refine MeasureTheory.IntegrableOn.congr_fun hmodel ?_ measurableSet_Iic
    intro t ht
    have habs : |t| = -t := abs_of_nonpos ht
    simp [mathlibResolventKernelC, mathlibResolventKernelReal, c, a, habs, Complex.ofReal_exp,
      div_eq_mul_inv]
  · let c : ℂ := ((Real.pi / ω : ℝ) : ℂ)
    let a : ℂ := ((-(2 * Real.pi * ω : ℝ)) : ℂ)
    have ha : a.re < 0 := by
      change -(2 * Real.pi * ω) < 0
      nlinarith [Real.pi_pos, hω]
    have hmodel :
        MeasureTheory.IntegrableOn (fun t : ℝ => c * Complex.exp (a * t)) (Set.Ioi 0) := by
      exact (integrableOn_exp_mul_complex_Ioi ha 0).const_mul c
    refine MeasureTheory.IntegrableOn.congr_fun hmodel ?_ measurableSet_Ioi
    intro t ht
    have habs : |t| = t := abs_of_nonneg (le_of_lt ht)
    simp [mathlibResolventKernelC, mathlibResolventKernelReal, c, a, habs, Complex.ofReal_exp,
      div_eq_mul_inv]

private theorem bddAbove_norm_mathlibResolventKernelC
    (ω : ℝ) (hω : 0 < ω) :
    BddAbove (Set.range fun t => ‖mathlibResolventKernelC ω t‖) := by
  refine ⟨Real.pi / ω, ?_⟩
  rintro y ⟨t, rfl⟩
  have hcoef_nonneg : 0 ≤ Real.pi / ω := by positivity
  have hexp_nonneg : 0 ≤ Real.exp (-(2 * Real.pi * ω) * |t|) := by positivity
  have hexp_le_one : Real.exp (-(2 * Real.pi * ω) * |t|) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (2 * Real.pi * ω) * |t| := by positivity
    linarith
  have hbound :
      (Real.pi / ω) * Real.exp (-(2 * Real.pi * ω) * |t|) ≤ Real.pi / ω := by
    calc
      (Real.pi / ω) * Real.exp (-(2 * Real.pi * ω) * |t|)
        ≤ (Real.pi / ω) * 1 := by
            exact mul_le_mul_of_nonneg_left hexp_le_one hcoef_nonneg
      _ = Real.pi / ω := by ring
  have hnorm :
      ‖mathlibResolventKernelC ω t‖ =
        (Real.pi / ω) * Real.exp (-(2 * Real.pi * ω) * |t|) := by
    rw [mathlibResolventKernelC, mathlibResolventKernelReal, Complex.norm_real]
    apply abs_of_nonneg
    positivity
  change ‖mathlibResolventKernelC ω t‖ ≤ Real.pi / ω
  rw [hnorm]
  exact hbound

private theorem fourier_mathlibResolventKernelC
    (ω : ℝ) (hω : 0 < ω) :
    FourierTransform.fourier (mathlibResolventKernelC ω) =
      fun ξ : ℝ => ((((ξ ^ 2 + ω ^ 2)⁻¹ : ℝ)) : ℂ) := by
  ext ξ
  change FourierTransform.fourier
      (fun t : ℝ => (((Real.pi / ω * Real.exp (-(2 * Real.pi * ω) * |t|) : ℝ)) : ℂ)) ξ =
    ((((ξ ^ 2 + ω ^ 2)⁻¹ : ℝ)) : ℂ)
  simpa using
    fourier_mathlib_resolventKernel ω hω ξ

private def mathlibResolventConvolution (ω : ℝ) (h : SchwartzMap ℝ ℝ) : ℝ → ℂ :=
  MeasureTheory.convolution (mathlibResolventKernelC ω) (schwartzToComplex h)
    (ContinuousLinearMap.mul ℂ ℂ) MeasureTheory.volume

attribute [local instance] SMulCommClass.symm in
private theorem realFourierMultiplier_inverseSymbol_eq_convolution
    (ω : ℝ) (hω : 0 < ω) (h : SchwartzMap ℝ ℝ) :
    schwartzToComplex
      (realFourierMultiplierCLM
        (fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
        (resolventInverseSymbol_hasTemperateGrowth ω hω) h) =
      mathlibResolventConvolution ω h := by
  let lhs : SchwartzMap ℝ ℂ :=
    schwartzToComplex
      (realFourierMultiplierCLM
        (fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
        (resolventInverseSymbol_hasTemperateGrowth ω hω) h)
  let rhs : ℝ → ℂ := mathlibResolventConvolution ω h
  have hk_cont : Continuous (mathlibResolventKernelC ω) :=
    continuous_mathlibResolventKernelC ω
  have hk_int : Integrable (mathlibResolventKernelC ω) :=
    integrable_mathlibResolventKernelC ω hω
  have hg_cont : Continuous (schwartzToComplex h) := (schwartzToComplex h).continuous
  have hg_int : Integrable (schwartzToComplex h) := (schwartzToComplex h).integrable
  have hrhs_cont : Continuous rhs :=
    (bddAbove_norm_mathlibResolventKernelC ω hω).continuous_convolution_left_of_integrable
      (L := ContinuousLinearMap.mul ℂ ℂ) hk_cont hg_int
  have hrhs_int : Integrable rhs :=
    hk_int.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) hg_int
  have hlhs_fourier_eq :
      FourierTransform.fourier (lhs : ℝ → ℂ) =
        FourierTransform.fourier rhs := by
    ext ξ
    unfold rhs mathlibResolventConvolution
    rw [Real.fourier_mul_convolution_eq hk_int hg_int hk_cont hg_cont]
    rw [show FourierTransform.fourier (lhs : ℝ → ℂ) ξ =
        FourierTransform.fourier
          (schwartzToComplex
            (realFourierMultiplierCLM
              (fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
              (resolventInverseSymbol_hasTemperateGrowth ω hω) h)) ξ by
      rw [SchwartzMap.fourier_coe]]
    rw [schwartzToComplex_realFourierMultiplier_eq
      (σ := fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
      (hσ := resolventInverseSymbol_hasTemperateGrowth ω hω)
      (heven := resolventInverseSymbol_even ω) h]
    rw [SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq]
    rw [SchwartzMap.smulLeftCLM_apply_apply (resolventInverseSymbol_hasTemperateGrowth ω hω)]
    rw [SchwartzMap.fourier_coe, fourier_mathlibResolventKernelC ω hω]
    change
      ((((ξ ^ 2 + ω ^ 2)⁻¹ : ℝ) : ℂ) *
          FourierTransform.fourier (⇑(schwartzToComplex h)) ξ) =
        (((((ξ ^ 2 + ω ^ 2)⁻¹ : ℝ) : ℂ)) *
          FourierTransform.fourier (⇑(schwartzToComplex h)) ξ)
    rfl
  have hlhs_int : Integrable lhs := lhs.integrable
  have hlhs_fourier_int : Integrable (FourierTransform.fourier (lhs : ℝ → ℂ)) := by
    simpa [SchwartzMap.fourier_coe] using (FourierTransform.fourier lhs).integrable
  have hrhs_fourier_int : Integrable (FourierTransform.fourier rhs) := by
    rw [← hlhs_fourier_eq]
    exact hlhs_fourier_int
  ext t
  have hlhs_inv :
      FourierTransform.fourierInv (FourierTransform.fourier (lhs : ℝ → ℂ)) = (lhs : ℝ → ℂ) :=
    lhs.continuous.fourierInv_fourier_eq hlhs_int hlhs_fourier_int
  have hrhs_inv :
      FourierTransform.fourierInv (FourierTransform.fourier rhs) = rhs :=
    hrhs_cont.fourierInv_fourier_eq hrhs_int hrhs_fourier_int
  calc
    lhs t = FourierTransform.fourierInv (FourierTransform.fourier (lhs : ℝ → ℂ)) t := by
      symm
      exact congrArg (fun f : ℝ → ℂ => f t) hlhs_inv
    _ = FourierTransform.fourierInv (FourierTransform.fourier rhs) t := by
      rw [hlhs_fourier_eq]
    _ = rhs t := by
      exact congrArg (fun f : ℝ → ℂ => f t) hrhs_inv

private theorem realFourierMultiplier_inverseSymbol_apply_eq_integral
    (ω : ℝ) (hω : 0 < ω) (h : SchwartzMap ℝ ℝ) (t : ℝ) :
    realFourierMultiplierCLM
      (fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
      (resolventInverseSymbol_hasTemperateGrowth ω hω) h t =
    ∫ s, mathlibResolventKernelReal ω (t - s) * h s := by
  have hconv :=
    congrArg (fun f : ℝ → ℂ => f t)
      (realFourierMultiplier_inverseSymbol_eq_convolution ω hω h)
  change
    ↑((realFourierMultiplierCLM
      (fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
      (resolventInverseSymbol_hasTemperateGrowth ω hω) h) t) =
      mathlibResolventConvolution ω h t at hconv
  unfold mathlibResolventConvolution at hconv
  rw [convolution_mul_swap] at hconv
  apply Complex.ofReal_injective
  have hreal :
      ∫ s, mathlibResolventKernelC ω (t - s) * (schwartzToComplex h) s =
        ((∫ s, mathlibResolventKernelReal ω (t - s) * h s : ℝ) : ℂ) := by
    simpa [mathlibResolventKernelC, mathlibResolventKernelReal, schwartzToComplex,
      Complex.ofReal_exp, mul_assoc] using
      (integral_complex_ofReal
        (f := fun s : ℝ => mathlibResolventKernelReal ω (t - s) * h s)
        (μ := MeasureTheory.volume))
  exact hconv.trans hreal

attribute [local instance] SMulCommClass.symm in
private theorem resolventMultiplier_l2Inner_eq_inverseSymbol
    (ω : ℝ) (hω : 0 < ω) (h₁ h₂ : SchwartzMap ℝ ℝ) :
    l2InnerProduct (resolventMultiplierCLM hω h₁)
      (resolventMultiplierCLM hω h₂) =
    l2InnerProduct h₁
      (realFourierMultiplierCLM
        (fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
        (resolventInverseSymbol_hasTemperateGrowth ω hω) h₂) := by
  apply Complex.ofRealLI.injective
  let σ : ℝ → ℝ := resolventSymbol ω
  let σInv : ℝ → ℝ := fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹
  let F : SchwartzMap ℝ ℂ := schwartzToComplex h₁
  let G : SchwartzMap ℝ ℂ := schwartzToComplex h₂
  have hMσ_h₁ :
      schwartzToComplex (resolventMultiplierCLM hω h₁) =
        SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ F := by
    simpa [σ, F, resolventMultiplierCLM] using
      schwartzToComplex_realFourierMultiplier_eq
        (σ := resolventSymbol ω)
        (hσ := resolventSymbol_hasTemperateGrowth ω hω)
        (heven := resolventSymbol_even ω) h₁
  have hMσ_h₂ :
      schwartzToComplex (resolventMultiplierCLM hω h₂) =
        SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ G := by
    simpa [σ, G, resolventMultiplierCLM] using
      schwartzToComplex_realFourierMultiplier_eq
        (σ := resolventSymbol ω)
        (hσ := resolventSymbol_hasTemperateGrowth ω hω)
        (heven := resolventSymbol_even ω) h₂
  have hMσInv_h₂ :
      schwartzToComplex
          (realFourierMultiplierCLM σInv
            (resolventInverseSymbol_hasTemperateGrowth ω hω) h₂) =
        SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σInv G := by
    simpa [σInv, G] using
      schwartzToComplex_realFourierMultiplier_eq
        (σ := fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
        (hσ := resolventInverseSymbol_hasTemperateGrowth ω hω)
        (heven := resolventInverseSymbol_even ω) h₂
  have hMσ_fourier (f : SchwartzMap ℝ ℂ) :
      FourierTransform.fourier
          (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ f) =
        SchwartzMap.smulLeftCLM ℂ σ (FourierTransform.fourier f) := by
    rw [SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq]
  have hMσInv_fourier (f : SchwartzMap ℝ ℂ) :
      FourierTransform.fourier
          (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σInv f) =
        SchwartzMap.smulLeftCLM ℂ σInv (FourierTransform.fourier f) := by
    rw [SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq]
  calc
    ((l2InnerProduct (resolventMultiplierCLM hω h₁)
        (resolventMultiplierCLM hω h₂) : ℝ) : ℂ)
      =
        (∫ x,
          @inner ℂ ℂ _
            ((SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ F) x)
            ((SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ G) x)) := by
          rw [schwartz_l2InnerProduct_eq_integral_mul]
          rw [← hMσ_h₁, ← hMσ_h₂]
          exact (schwartzToComplex_integral_inner_eq_ofReal_integral_mul
            (resolventMultiplierCLM hω h₁)
            (resolventMultiplierCLM hω h₂)).symm
    _ =
        (∫ ξ,
          @inner ℂ ℂ _
            (FourierTransform.fourier
              (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ F) ξ)
            (FourierTransform.fourier
              (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ G) ξ)) := by
          symm
          simpa using
            SchwartzMap.integral_inner_fourier_fourier
              (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ F)
              (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ G)
    _ =
        (∫ ξ,
          @inner ℂ ℂ _
            (FourierTransform.fourier F ξ)
            (FourierTransform.fourier
              (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σInv G) ξ)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with ξ
          rw [hMσ_fourier, hMσ_fourier, hMσInv_fourier]
          rw [SchwartzMap.smulLeftCLM_apply_apply
              (resolventSymbol_hasTemperateGrowth ω hω)]
          rw [SchwartzMap.smulLeftCLM_apply_apply
              (resolventSymbol_hasTemperateGrowth ω hω)]
          rw [SchwartzMap.smulLeftCLM_apply_apply
              (resolventInverseSymbol_hasTemperateGrowth ω hω)]
          rw [RCLike.inner_apply, RCLike.inner_apply]
          have hs :
              (((resolventSymbol ω ξ : ℝ) : ℂ) * (resolventSymbol ω ξ : ℂ)) =
                ((((ξ ^ 2 + ω ^ 2)⁻¹ : ℝ)) : ℂ) := by
            exact_mod_cast resolventSymbol_mul_self ω hω ξ
          calc
            resolventSymbol ω ξ • (FourierTransform.fourier G ξ) *
                (starRingEnd ℂ) (resolventSymbol ω ξ • (FourierTransform.fourier F ξ))
              = (((resolventSymbol ω ξ : ℝ) : ℂ) *
                    FourierTransform.fourier G ξ) *
                  (((resolventSymbol ω ξ : ℝ) : ℂ) *
                    (starRingEnd ℂ) (FourierTransform.fourier F ξ)) := by
                      simp [mul_comm, mul_left_comm]
            _ = ((((ξ ^ 2 + ω ^ 2)⁻¹ : ℝ)) : ℂ) *
                  (FourierTransform.fourier G ξ *
                    (starRingEnd ℂ) (FourierTransform.fourier F ξ)) := by
                      rw [← hs]
                      ring
            _ = ((((ξ ^ 2 + ω ^ 2)⁻¹ : ℝ)) : ℂ) *
                  FourierTransform.fourier G ξ *
                    (starRingEnd ℂ) (FourierTransform.fourier F ξ) := by
                      ring
            _ = (ξ ^ 2 + ω ^ 2)⁻¹ • (FourierTransform.fourier G) ξ *
                  (starRingEnd ℂ) ((FourierTransform.fourier F) ξ) := by
                      simp
    _ =
        (∫ x,
          @inner ℂ ℂ _ (F x)
            ((SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σInv G) x)) := by
          simpa using
            SchwartzMap.integral_inner_fourier_fourier F
              (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σInv G)
    _ = ((l2InnerProduct h₁
          (realFourierMultiplierCLM σInv
            (resolventInverseSymbol_hasTemperateGrowth ω hω) h₂) : ℝ) : ℂ) := by
          rw [schwartz_l2InnerProduct_eq_integral_mul]
          rw [← hMσInv_h₂]
          simpa [F] using
            schwartzToComplex_integral_inner_eq_ofReal_integral_mul h₁
              (realFourierMultiplierCLM σInv
                (resolventInverseSymbol_hasTemperateGrowth ω hω) h₂)

theorem resolventMultiplier_l2Inner_eq_inverseSymbol_integral
    (ω : ℝ) (hω : 0 < ω) (h₁ h₂ : SchwartzMap ℝ ℝ) :
    l2InnerProduct (resolventMultiplierCLM hω h₁)
      (resolventMultiplierCLM hω h₂) =
    ∫ t, h₁ t *
      realFourierMultiplierCLM
        (fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
        (resolventInverseSymbol_hasTemperateGrowth ω hω) h₂ t := by
  rw [resolventMultiplier_l2Inner_eq_inverseSymbol]
  exact schwartz_l2InnerProduct_eq_integral_mul h₁
    (realFourierMultiplierCLM
      (fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
      (resolventInverseSymbol_hasTemperateGrowth ω hω) h₂)

theorem resolventMultiplier_l2Inner_eq_mathlibResolventKernel_integral
    (ω : ℝ) (hω : 0 < ω) (h₁ h₂ : SchwartzMap ℝ ℝ) :
    l2InnerProduct (resolventMultiplierCLM hω h₁)
      (resolventMultiplierCLM hω h₂) =
    ∫ t, h₁ t * (∫ s, mathlibResolventKernelReal ω (t - s) * h₂ s) := by
  rw [resolventMultiplier_l2Inner_eq_inverseSymbol_integral]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [realFourierMultiplier_inverseSymbol_apply_eq_integral ω hω h₂ t]

theorem schwartz_l2InnerProduct_smul_smul
    (c : ℝ) (f g : SchwartzMap ℝ ℝ) :
    l2InnerProduct (c • f) (c • g) = c ^ 2 * l2InnerProduct f g := by
  rw [schwartz_l2InnerProduct_eq_integral_mul, schwartz_l2InnerProduct_eq_integral_mul]
  have hfg :
      (fun t : ℝ => (c • f) t * (c • g) t) = fun t => c ^ 2 * (f t * g t) := by
    funext t
    simp [smul_eq_mul]
    ring
  rw [hfg, integral_const_mul]

theorem inv_two_pi_sq_mul_two_pi_sq
    (x : ℝ) :
    (((2 * Real.pi : ℝ)⁻¹) ^ 2) * (((2 * Real.pi) ^ 2) * x) = x := by
  have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp [h2pi_ne]

private def twoPiUnit : ℝˣ :=
  Units.mk0 (2 * Real.pi) (by positivity)

/-- Temporal rescaling `h(t) ↦ √(2π) h(2π t)` converting the analyst-normalized cylinder
resolvent into the physicist-normalized one. -/
def schwartzTwoPiRescaleCLM :
    SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ :=
  (Real.sqrt (2 * Real.pi : ℝ)) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      ((ContinuousLinearEquiv.unitsEquivAut ℝ) twoPiUnit)

@[simp] private theorem schwartzTwoPiRescaleCLM_apply
    (h : SchwartzMap ℝ ℝ) (t : ℝ) :
    schwartzTwoPiRescaleCLM h t =
      Real.sqrt (2 * Real.pi) * h (2 * Real.pi * t) := by
  simp [schwartzTwoPiRescaleCLM, twoPiUnit, mul_comm, mul_assoc]

private theorem sq_mul_freeKernel_mul_eq_mul_freeKernel_comp_mul
    {a ω x : ℝ} (ha : 0 < a) (hω : 0 < ω) :
    a ^ 2 * freeKernel (a * ω) x = a * freeKernel ω (a * x) := by
  unfold freeKernel
  rw [abs_mul, abs_of_nonneg ha.le]
  rw [show -ω * (a * |x|) = -(a * ω) * |x| by ring]
  calc
    a ^ 2 * (Real.exp (-(a * ω) * |x|) / (2 * (a * ω)))
      = (a ^ 2 / (2 * (a * ω))) * Real.exp (-(a * ω) * |x|) := by ring
    _ = (a / (2 * ω)) * Real.exp (-(a * ω) * |x|) := by
          field_simp [ha.ne', hω.ne']
    _ = a * (Real.exp (-(a * ω) * |x|) / (2 * ω)) := by ring

private theorem scaledFreeKernel_integral_eq_freeKernel_integral_of_twoPiRescale
    (ω : ℝ) (hω : 0 < ω) (h₁ h₂ : SchwartzMap ℝ ℝ) :
    ∫ t, schwartzTwoPiRescaleCLM h₁ t *
      (∫ s, (((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (t - s)) *
        schwartzTwoPiRescaleCLM h₂ s) =
    ∫ t, h₁ t * (∫ s, freeKernel ω (t - s) * h₂ s) := by
  let a : ℝ := 2 * Real.pi
  let c : ℝ := Real.sqrt a
  let J : ℝ → ℝ := fun u => ∫ s, freeKernel ω (u - s) * h₂ s
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have ha_ne : a ≠ 0 := ha_pos.ne'
  have hc_sq : c ^ 2 = a := by
    dsimp [c]
    nlinarith [Real.sq_sqrt (show 0 ≤ a by positivity)]
  have hinner : ∀ t,
      (∫ s, (((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (t - s)) *
          schwartzTwoPiRescaleCLM h₂ s) =
        c * J (a * t) := by
    intro t
    have hstep1 :
        ∫ s, (((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (t - s)) *
            schwartzTwoPiRescaleCLM h₂ s =
          ∫ s, (a * freeKernel ω (a * (t - s))) * (c * h₂ (a * s)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with s
      rw [schwartzTwoPiRescaleCLM_apply]
      rw [show ((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (t - s) =
        a * freeKernel ω (a * (t - s)) by
        simpa [a] using
          sq_mul_freeKernel_mul_eq_mul_freeKernel_comp_mul
            (a := a) (ω := ω) (x := t - s) ha_pos hω]
    have hstep2 :
        ∫ s, (a * freeKernel ω (a * (t - s))) * (c * h₂ (a * s)) =
          ∫ s, a * c * (freeKernel ω (a * t - a * s) * h₂ (a * s)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with s
      rw [show a * (t - s) = a * t - a * s by ring]
      ring_nf
    have hstep3 :
        ∫ s, a * c * (freeKernel ω (a * t - a * s) * h₂ (a * s)) =
          a * c * ∫ s, (fun u : ℝ => freeKernel ω (a * t - u) * h₂ u) (a * s) := by
      rw [MeasureTheory.integral_const_mul]
    have hcomp :
        ∫ s, (fun u : ℝ => freeKernel ω (a * t - u) * h₂ u) (a * s) =
          |a⁻¹| * ∫ u, freeKernel ω (a * t - u) * h₂ u := by
      simpa [smul_eq_mul] using
        (Measure.integral_comp_mul_left
          (g := fun u : ℝ => freeKernel ω (a * t - u) * h₂ u) (a := a))
    calc
      ∫ s, (((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (t - s)) *
          schwartzTwoPiRescaleCLM h₂ s
        = ∫ s, (a * freeKernel ω (a * (t - s))) * (c * h₂ (a * s)) := hstep1
      _ = ∫ s, a * c * (freeKernel ω (a * t - a * s) * h₂ (a * s)) := by
            exact hstep2
      _ = a * c * ∫ s, (fun u : ℝ => freeKernel ω (a * t - u) * h₂ u) (a * s) := hstep3
      _ = a * c * (|a⁻¹| * ∫ u, freeKernel ω (a * t - u) * h₂ u) := by rw [hcomp]
      _ = c * J (a * t) := by
            dsimp [J]
            rw [abs_of_pos (inv_pos.mpr ha_pos)]
            rw [show a * c * (a⁻¹ * ∫ u, freeKernel ω (a * t - u) * h₂ u) =
              c * (a * a⁻¹) * ∫ u, freeKernel ω (a * t - u) * h₂ u by ring]
            simp [ha_ne]
  have hout1 :
      ∫ t, schwartzTwoPiRescaleCLM h₁ t *
        (∫ s, (((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (t - s)) *
          schwartzTwoPiRescaleCLM h₂ s) =
      ∫ t, (c * h₁ (a * t)) * (c * J (a * t)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [schwartzTwoPiRescaleCLM_apply, hinner t]
  have hmul :
      (fun t : ℝ => (c * h₁ (a * t)) * (c * J (a * t))) =
        fun t : ℝ => c ^ 2 * ((fun u : ℝ => h₁ u * J u) (a * t)) := by
    funext t
    ring_nf
  have hout2 :
      ∫ t, (c * h₁ (a * t)) * (c * J (a * t)) =
        c ^ 2 * ∫ t, (fun u : ℝ => h₁ u * J u) (a * t) := by
    rw [hmul, MeasureTheory.integral_const_mul]
  have houtComp :
      ∫ t, (fun u : ℝ => h₁ u * J u) (a * t) =
        |a⁻¹| * ∫ u, h₁ u * J u := by
    simpa [smul_eq_mul] using
      (Measure.integral_comp_mul_left (g := fun u : ℝ => h₁ u * J u) (a := a))
  calc
    ∫ t, schwartzTwoPiRescaleCLM h₁ t *
      (∫ s, (((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (t - s)) *
        schwartzTwoPiRescaleCLM h₂ s)
      = ∫ t, (c * h₁ (a * t)) * (c * J (a * t)) := hout1
    _ = c ^ 2 * ∫ t, (fun u : ℝ => h₁ u * J u) (a * t) := hout2
    _ = c ^ 2 * (|a⁻¹| * ∫ u, h₁ u * J u) := by rw [houtComp]
    _ = ∫ u, h₁ u * J u := by
          rw [hc_sq, abs_of_pos (inv_pos.mpr ha_pos)]
          rw [show a * (a⁻¹ * ∫ u, h₁ u * J u) = (a * a⁻¹) * ∫ u, h₁ u * J u by ring]
          simp [ha_ne]
    _ = ∫ t, h₁ t * (∫ s, freeKernel ω (t - s) * h₂ s) := by
          rfl

def physicalResolventMultiplierCLM
    (ω : ℝ) (hω : 0 < ω) :
    SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ :=
  let hω' : 0 < ω / (2 * Real.pi) := by
    have h2pi_pos : 0 < (2 * Real.pi : ℝ) := by positivity
    exact div_pos hω h2pi_pos
  ((2 * Real.pi : ℝ)⁻¹) • resolventMultiplierCLM hω'

theorem physicalResolventMultiplier_l2Inner_eq_freeKernel_integral
    (ω : ℝ) (hω : 0 < ω) (h₁ h₂ : SchwartzMap ℝ ℝ) :
    l2InnerProduct (physicalResolventMultiplierCLM ω hω h₁)
      (physicalResolventMultiplierCLM ω hω h₂) =
    ∫ t, h₁ t * (∫ s, freeKernel ω (t - s) * h₂ s) := by
  let c : ℝ := (2 * Real.pi : ℝ)⁻¹
  let ω' : ℝ := ω / (2 * Real.pi)
  have hω' : 0 < ω' := by
    dsimp [ω']
    have h2pi_pos : 0 < (2 * Real.pi : ℝ) := by positivity
    exact div_pos hω h2pi_pos
  have hfreq : 2 * Real.pi * ω' = ω := by
    dsimp [ω']
    field_simp [Real.pi_ne_zero]
  calc
    l2InnerProduct (physicalResolventMultiplierCLM ω hω h₁)
        (physicalResolventMultiplierCLM ω hω h₂)
      = c ^ 2 * l2InnerProduct (resolventMultiplierCLM hω' h₁)
          (resolventMultiplierCLM hω' h₂) := by
            simpa [physicalResolventMultiplierCLM, c, ω', hω'] using
              schwartz_l2InnerProduct_smul_smul c
                (resolventMultiplierCLM hω' h₁)
                (resolventMultiplierCLM hω' h₂)
    _ = c ^ 2 * ∫ t, h₁ t *
          (∫ s, mathlibResolventKernelReal ω' (t - s) * h₂ s) := by
            rw [resolventMultiplier_l2Inner_eq_mathlibResolventKernel_integral]
    _ = ∫ t, h₁ t * (∫ s, freeKernel ω (t - s) * h₂ s) := by
          rw [← integral_const_mul]
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          calc
            c ^ 2 * (h₁ t * ∫ s, mathlibResolventKernelReal ω' (t - s) * h₂ s)
              = h₁ t * (c ^ 2 * ∫ s, mathlibResolventKernelReal ω' (t - s) * h₂ s) := by
                  ring
            _ = h₁ t * (∫ s, c ^ 2 *
                  (mathlibResolventKernelReal ω' (t - s) * h₂ s)) := by
                  rw [← integral_const_mul]
            _ = h₁ t * (∫ s, freeKernel ω (t - s) * h₂ s) := by
                  congr 1
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards with s
                  rw [show c ^ 2 *
                    (mathlibResolventKernelReal ω' (t - s) * h₂ s) =
                      (c ^ 2 * mathlibResolventKernelReal ω' (t - s)) * h₂ s by
                    ring]
                  rw [show mathlibResolventKernelReal ω' (t - s) =
                    ((2 * Real.pi) ^ 2) * freeKernel ω (t - s) by
                    simpa [mathlibResolventKernelReal, hfreq] using
                      PeriodicResolvent1D.mathlibResolventKernel_eq_scaled_freeKernel
                        ω' hω' (t - s)]
                  rw [inv_two_pi_sq_mul_two_pi_sq]

theorem resolventMultiplier_l2Inner_eq_scaledFreeKernel_integral
    (ω : ℝ) (hω : 0 < ω) (h₁ h₂ : SchwartzMap ℝ ℝ) :
    l2InnerProduct (resolventMultiplierCLM hω h₁)
      (resolventMultiplierCLM hω h₂) =
    ∫ t, h₁ t *
      (∫ s, (((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (t - s)) * h₂ s) := by
  rw [resolventMultiplier_l2Inner_eq_mathlibResolventKernel_integral]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  refine congrArg (fun z : ℝ => h₁ t * z) ?_
  apply MeasureTheory.integral_congr_ae
  filter_upwards with s
  rw [show
    mathlibResolventKernelReal ω (t - s) =
      ((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (t - s) by
    simpa [mathlibResolventKernelReal] using
      PeriodicResolvent1D.mathlibResolventKernel_eq_scaled_freeKernel ω hω (t - s)]

theorem resolventMultiplier_l2Inner_eq_physical_after_twoPiRescale
    (ω : ℝ) (hω : 0 < ω) (h₁ h₂ : SchwartzMap ℝ ℝ) :
    l2InnerProduct (resolventMultiplierCLM hω (schwartzTwoPiRescaleCLM h₁))
      (resolventMultiplierCLM hω (schwartzTwoPiRescaleCLM h₂)) =
    l2InnerProduct (physicalResolventMultiplierCLM ω hω h₁)
      (physicalResolventMultiplierCLM ω hω h₂) := by
  rw [resolventMultiplier_l2Inner_eq_scaledFreeKernel_integral,
    physicalResolventMultiplier_l2Inner_eq_freeKernel_integral]
  exact scaledFreeKernel_integral_eq_freeKernel_integral_of_twoPiRescale ω hω h₁ h₂


end Pphi2
