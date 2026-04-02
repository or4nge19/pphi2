/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Generic Complex Test-Function API

This file packages the standard real/complex Schwartz-function conversions and
their interaction with Euclidean motions and generating functionals for an
arbitrary Euclidean background.

The canonical 2D API in `Pphi2/OSforGFF/ComplexTestFunction.lean` then becomes
just a thin specialization layer.
-/

import Pphi2.EuclideanOS

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

/-- Embed a real Schwartz function as a complex-valued Schwartz function via
`Complex.ofReal`. -/
def schwartzOfReal {B : EuclideanPlaneBackground}
    (f : EuclideanPlaneBackground.RealTestFunction B) :
    EuclideanPlaneBackground.ComplexTestFunction B :=
  SchwartzMap.mk (fun x => (f x : ℂ))
    (Complex.ofRealCLM.contDiff.comp f.smooth')
    (by
      intro k n
      obtain ⟨C, hC⟩ := f.decay' k n
      use C * ‖Complex.ofRealCLM‖
      intro x
      have h_eq : (fun y => ((f y : ℝ) : ℂ)) = Complex.ofRealCLM ∘ f.toFun := rfl
      rw [h_eq, ContinuousLinearMap.iteratedFDeriv_comp_left Complex.ofRealCLM
        f.smooth'.contDiffAt (WithTop.coe_le_coe.mpr le_top)]
      calc ‖x‖ ^ k * ‖Complex.ofRealCLM.compContinuousMultilinearMap
              (iteratedFDeriv ℝ n f.toFun x)‖
          ≤ ‖x‖ ^ k * (‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ n f.toFun x‖) :=
            mul_le_mul_of_nonneg_left
              (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _)
              (pow_nonneg (norm_nonneg _) _)
        _ = ‖Complex.ofRealCLM‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f.toFun x‖) := by ring
        _ ≤ ‖Complex.ofRealCLM‖ * C := mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
        _ = C * ‖Complex.ofRealCLM‖ := by ring)

@[simp] theorem schwartzOfReal_apply {B : EuclideanPlaneBackground}
    (f : EuclideanPlaneBackground.RealTestFunction B)
    (x : EuclideanPlaneBackground.SpaceTime B) :
    schwartzOfReal f x = (f x : ℂ) := rfl

@[simp] theorem schwartzRe_schwartzOfReal {B : EuclideanPlaneBackground}
    (f : EuclideanPlaneBackground.RealTestFunction B) :
    EuclideanOS.schwartzRe (schwartzOfReal f) = f := by
  ext x
  change (((f x : ℝ) : ℂ)).re = f x
  simp [Complex.ofReal_re]

@[simp] theorem schwartzIm_schwartzOfReal {B : EuclideanPlaneBackground}
    (f : EuclideanPlaneBackground.RealTestFunction B) :
    EuclideanOS.schwartzIm (schwartzOfReal f) = 0 := by
  ext x
  change (((f x : ℝ) : ℂ)).im = 0
  simp [Complex.ofReal_im]

@[simp] theorem actionComplex_schwartzOfReal {B : EuclideanPlaneBackground}
    (g : EuclideanPlaneBackground.Motion B)
    (f : EuclideanPlaneBackground.RealTestFunction B) :
    EuclideanPlaneBackground.actionComplex g (schwartzOfReal f) =
      schwartzOfReal (EuclideanPlaneBackground.action g f) := by
  ext x
  rfl

@[simp] theorem schwartzRe_actionComplex {B : EuclideanPlaneBackground}
    (g : EuclideanPlaneBackground.Motion B)
    (J : EuclideanPlaneBackground.ComplexTestFunction B) :
    EuclideanOS.schwartzRe (EuclideanPlaneBackground.actionComplex g J) =
      EuclideanPlaneBackground.action g (EuclideanOS.schwartzRe J) := by
  ext x
  rfl

@[simp] theorem schwartzIm_actionComplex {B : EuclideanPlaneBackground}
    (g : EuclideanPlaneBackground.Motion B)
    (J : EuclideanPlaneBackground.ComplexTestFunction B) :
    EuclideanOS.schwartzIm (EuclideanPlaneBackground.actionComplex g J) =
      EuclideanPlaneBackground.action g (EuclideanOS.schwartzIm J) := by
  ext x
  rfl

lemma generatingFunctionalℂ_ofReal_add_real_smul {B : EuclideanPlaneBackground}
    (μ : Measure (EuclideanPlaneBackground.Distribution B)) [IsProbabilityMeasure μ]
    (f h : EuclideanPlaneBackground.RealTestFunction B) (r : ℝ) :
    EuclideanOS.generatingFunctionalℂ μ (schwartzOfReal f + (r : ℂ) • schwartzOfReal h) =
      EuclideanOS.generatingFunctional μ (f + r • h) := by
  unfold EuclideanOS.generatingFunctionalℂ EuclideanOS.generatingFunctional
  have hre :
      EuclideanOS.schwartzRe (schwartzOfReal f + (r : ℂ) • schwartzOfReal h) = f + r • h := by
    ext x
    change Complex.re ((f x : ℂ) + (r : ℂ) * (h x : ℂ)) = f x + r * h x
    simp [Complex.add_re, Complex.mul_re]
  have him :
      EuclideanOS.schwartzIm (schwartzOfReal f + (r : ℂ) • schwartzOfReal h) = 0 := by
    ext x
    change Complex.im ((f x : ℂ) + (r : ℂ) * (h x : ℂ)) = 0
    simp [Complex.add_im, Complex.mul_im]
  simp_rw [hre, him]
  simp

lemma schwartz_decompose {B : EuclideanPlaneBackground}
    (J : EuclideanPlaneBackground.ComplexTestFunction B) :
    J = schwartzOfReal (EuclideanOS.schwartzRe J) +
      (Complex.I : ℂ) • schwartzOfReal (EuclideanOS.schwartzIm J) := by
  ext x
  change J x = ((J x).re : ℂ) + Complex.I * ((J x).im : ℂ)
  simpa [mul_comm] using (Complex.re_add_im (J x)).symm

lemma schwartz_decompose_actionComplex {B : EuclideanPlaneBackground}
    (g : EuclideanPlaneBackground.Motion B)
    (J : EuclideanPlaneBackground.ComplexTestFunction B) :
    EuclideanPlaneBackground.actionComplex g J =
      schwartzOfReal (EuclideanPlaneBackground.action g (EuclideanOS.schwartzRe J)) +
        (Complex.I : ℂ) •
          schwartzOfReal (EuclideanPlaneBackground.action g (EuclideanOS.schwartzIm J)) := by
  calc
    EuclideanPlaneBackground.actionComplex g J
        = schwartzOfReal (EuclideanOS.schwartzRe (EuclideanPlaneBackground.actionComplex g J)) +
            (Complex.I : ℂ) •
              schwartzOfReal
                (EuclideanOS.schwartzIm (EuclideanPlaneBackground.actionComplex g J)) :=
          schwartz_decompose (EuclideanPlaneBackground.actionComplex g J)
    _ = schwartzOfReal (EuclideanPlaneBackground.action g (EuclideanOS.schwartzRe J)) +
          (Complex.I : ℂ) •
            schwartzOfReal (EuclideanPlaneBackground.action g (EuclideanOS.schwartzIm J)) := by
        rw [schwartzRe_actionComplex, schwartzIm_actionComplex]

end Pphi2
