/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L² Multiplication Operators

Multiplication by a bounded measurable function defines a continuous linear
map on L². This is a standard result used to construct the transfer operator
from its kernel factorization.

Adapted from aqft2/OSforGFF/FunctionalAnalysis.lean (complex version by
M. Douglas, S. Hoback, A. Mei, R. Nissim) to the real-valued setting.

## Main definitions

- `mulCLM` — Given `w : α → ℝ` with `‖w‖_∞ ≤ C`, constructs `M_w : L² →L[ℝ] L²`
- `mulCLM_spec` — Pointwise specification: `(M_w f)(x) = w(x) * f(x)` a.e.
- `mulCLM_isSelfAdjoint` — M_w is self-adjoint (since w is real-valued)

## Mathematical background

For `w ∈ L∞(μ)` with `‖w‖_∞ ≤ C`, the multiplication operator `M_w(f) = w · f`
is bounded on `L²` with `‖M_w f‖₂ ≤ C · ‖f‖₂` (Hölder's inequality with
exponents ∞ and 2).

## References

- Reed-Simon I, §VI.2 (Multiplication operators)
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-! ## L∞ × L² → L² multiplication -/

/-- Norm bound for the multiplication operator: `‖w · f‖₂ ≤ C · ‖f‖₂`
when `‖w‖_∞ ≤ C`. Uses `eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm`. -/
lemma mul_L2_bound {μ : Measure α}
    (w : α → ℝ) (_hw_meas : Measurable w) (C : ℝ) (_hC : 0 < C)
    (hw_bound : ∀ᵐ x ∂μ, ‖w x‖ ≤ C)
    (f : Lp ℝ 2 μ) :
    eLpNorm (w * ⇑f) 2 μ ≤ ENNReal.ofReal C * eLpNorm f 2 μ := by
  -- For ℝ, multiplication is the same as scalar multiplication
  have h_eq : w * ⇑f = w • ⇑f := rfl
  rw [h_eq]
  -- Use the L∞ × Lp → Lp bound for smul
  have h_smul_le := eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm (p := 2)
    (Lp.memLp f).aestronglyMeasurable w
  have h_w_norm : eLpNorm w ∞ μ ≤ ENNReal.ofReal C := by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound hw_bound
  calc eLpNorm (w • ⇑f) 2 μ
      ≤ eLpNorm w ∞ μ * eLpNorm f 2 μ := h_smul_le
    _ ≤ ENNReal.ofReal C * eLpNorm f 2 μ := by gcongr

/-- Given a measurable function `w` essentially bounded by `C`,
multiplication by `w` defines a bounded linear operator on `L²(μ, ℝ)`.

Construction: Uses `MemLp.mul` with Hölder triple (∞, 2, 2) to show
`w · f ∈ L²`, then `LinearMap.mkContinuous` with the norm bound. -/
noncomputable def mulCLM {μ : Measure α}
    (w : α → ℝ) (hw_meas : Measurable w) (C : ℝ) (hC : 0 < C)
    (hw_bound : ∀ᵐ x ∂μ, ‖w x‖ ≤ C) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := by
  have hw_mem : MemLp w ∞ μ := memLp_top_of_bound hw_meas.aestronglyMeasurable C hw_bound
  refine LinearMap.mkContinuous
    { toFun := fun f =>
        (MemLp.mul (p := ∞) (q := 2) (r := 2) (Lp.memLp f) hw_mem).toLp (w * ⇑f)
      map_add' := fun f1 f2 => by
        ext1
        filter_upwards [
          MemLp.coeFn_toLp (MemLp.mul (p := ∞) (q := 2) (r := 2)
            (Lp.memLp (f1 + f2)) hw_mem),
          MemLp.coeFn_toLp (MemLp.mul (p := ∞) (q := 2) (r := 2)
            (Lp.memLp f1) hw_mem),
          MemLp.coeFn_toLp (MemLp.mul (p := ∞) (q := 2) (r := 2)
            (Lp.memLp f2) hw_mem),
          Lp.coeFn_add f1 f2,
          Lp.coeFn_add
            ((MemLp.mul (p := ∞) (q := 2) (r := 2) (Lp.memLp f1) hw_mem).toLp (w * ⇑f1))
            ((MemLp.mul (p := ∞) (q := 2) (r := 2) (Lp.memLp f2) hw_mem).toLp (w * ⇑f2))
        ] with x h1 h2 h3 h4 h5
        simp only [h1, h2, h3, h4, h5, Pi.add_apply, Pi.mul_apply, mul_add]
      map_smul' := fun c f => by
        ext1
        filter_upwards [
          MemLp.coeFn_toLp (MemLp.mul (p := ∞) (q := 2) (r := 2)
            (Lp.memLp (c • f)) hw_mem),
          MemLp.coeFn_toLp (MemLp.mul (p := ∞) (q := 2) (r := 2)
            (Lp.memLp f) hw_mem),
          Lp.coeFn_smul c f,
          Lp.coeFn_smul c
            ((MemLp.mul (p := ∞) (q := 2) (r := 2) (Lp.memLp f) hw_mem).toLp (w * ⇑f))
        ] with x h1 h2 h3 h4
        simp only [h1, h2, h3, h4, Pi.smul_apply, Pi.mul_apply, RingHom.id_apply, smul_eq_mul]
        ring }
    C
    (fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp]
      apply ENNReal.toReal_le_of_le_ofReal (by positivity)
      refine (mul_L2_bound w hw_meas C hC hw_bound f).trans ?_
      rw [ENNReal.ofReal_mul (le_of_lt hC)]
      gcongr
      exact le_of_eq (ENNReal.ofReal_toReal (Lp.memLp f).eLpNorm_ne_top).symm)

/-- The multiplication operator acts pointwise a.e.: `(M_w f)(x) = w(x) * f(x)`. -/
lemma mulCLM_spec {μ : Measure α}
    (w : α → ℝ) (hw_meas : Measurable w) (C : ℝ) (hC : 0 < C)
    (hw_bound : ∀ᵐ x ∂μ, ‖w x‖ ≤ C)
    (f : Lp ℝ 2 μ) :
    (mulCLM w hw_meas C hC hw_bound f) =ᵐ[μ] fun x => w x * f x := by
  let hw_mem : MemLp w ∞ μ := memLp_top_of_bound hw_meas.aestronglyMeasurable C hw_bound
  change ((MemLp.mul (p := ∞) (q := 2) (r := 2) (Lp.memLp f) hw_mem).toLp (w * ⇑f)) =ᵐ[μ]
    fun x => w x * f x
  exact MemLp.coeFn_toLp _

/-- The operator norm of the multiplication operator satisfies `‖M_w f‖ ≤ C · ‖f‖`. -/
theorem mulCLM_norm_bound {μ : Measure α}
    (w : α → ℝ) (hw_meas : Measurable w) (C : ℝ) (hC : 0 < C)
    (hw_bound : ∀ᵐ x ∂μ, ‖w x‖ ≤ C)
    (f : Lp ℝ 2 μ) :
    ‖mulCLM w hw_meas C hC hw_bound f‖ ≤ C * ‖f‖ := by
  have eq : mulCLM w hw_meas C hC hw_bound f =
    (MemLp.mul (p := ∞) (q := 2) (r := 2) (Lp.memLp f)
      (memLp_top_of_bound hw_meas.aestronglyMeasurable C hw_bound)).toLp (w * ⇑f) := rfl
  rw [eq, Lp.norm_toLp]
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  refine (mul_L2_bound w hw_meas C hC hw_bound f).trans ?_
  rw [ENNReal.ofReal_mul (le_of_lt hC)]
  gcongr
  exact le_of_eq (ENNReal.ofReal_toReal (Lp.memLp f).eLpNorm_ne_top).symm

/-- The multiplication operator is self-adjoint: `⟨f, M_w g⟩ = ⟨M_w f, g⟩`.

This is because `w` is real-valued, so:
  `⟨f, M_w g⟩ = ∫ f(x) · (w(x) · g(x)) dμ = ∫ (w(x) · f(x)) · g(x) dμ = ⟨M_w f, g⟩`
by commutativity and associativity of real multiplication. -/
theorem mulCLM_isSelfAdjoint {μ : Measure α}
    (w : α → ℝ) (hw_meas : Measurable w) (C : ℝ) (hC : 0 < C)
    (hw_bound : ∀ᵐ x ∂μ, ‖w x‖ ≤ C) :
    IsSelfAdjoint (mulCLM w hw_meas C hC hw_bound) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  simp only [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  -- Both sides: ∫ ⟨(M_w f)(x), g(x)⟩ dμ = ∫ ⟨f(x), (M_w g)(x)⟩ dμ
  -- Using M_w acts by pointwise multiplication: (M_w f)(x) =ᵐ w(x) * f(x)
  have hf := mulCLM_spec w hw_meas C hC hw_bound f
  have hg := mulCLM_spec w hw_meas C hC hw_bound g
  filter_upwards [hf, hg] with x hfx hgx
  erw [hfx, hgx]
  simp only [inner, starRingEnd_apply, star_trivial]
  ring_nf

end
