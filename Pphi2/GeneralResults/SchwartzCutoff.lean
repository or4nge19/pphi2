/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas

# Schwartz Cutoff Approximation

Smooth cutoff operators on Schwartz space S(R) and their convergence in
Schwartz seminorms. Given a smooth bump function χ_N that equals 1 on
[-N-1, N+1] and vanishes outside [-2(N+1), 2(N+1)], the multiplication
operator h ↦ χ_N · h converges to the identity on S(R) as N → ∞.

## Main results

- `schwartzCutoffCLM` — the multiplication operator χ_N · (−) as a CLM on S(R)
- `schwartzCutoff_error_seminorm_le` — explicit seminorm bound for the error
  h − χ_N h in terms of (N+1)⁻¹ and finitely many seminorms of h
- `schwartzCutoffCLM_tendsto` — χ_N h → h in S(R) as N → ∞
-/

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace

noncomputable section

namespace Pphi2

open MeasureTheory Filter

def schwartzCutoffBump (N : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨(N : ℝ) + 1, 2 * ((N : ℝ) + 1), by positivity, by linarith⟩

def schwartzCutoff (N : ℕ) : ℝ → ℝ :=
  schwartzCutoffBump N

theorem schwartzCutoff_nonneg (N : ℕ) (x : ℝ) :
    0 ≤ schwartzCutoff N x := by
  simpa [schwartzCutoff] using (schwartzCutoffBump N).nonneg' x

theorem schwartzCutoff_le_one (N : ℕ) (x : ℝ) :
    schwartzCutoff N x ≤ 1 := by
  simpa [schwartzCutoff] using (schwartzCutoffBump N).le_one

theorem schwartzCutoff_eq_one_of_abs_le (N : ℕ) {x : ℝ}
    (hx : |x| ≤ (N : ℝ) + 1) :
    schwartzCutoff N x = 1 := by
  exact (schwartzCutoffBump N).one_of_mem_closedBall <| by
    simpa [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hx

theorem schwartzCutoff_eq_zero_of_two_mul_lt_abs (N : ℕ) {x : ℝ}
    (hx : 2 * ((N : ℝ) + 1) < |x|) :
    schwartzCutoff N x = 0 := by
  exact (schwartzCutoffBump N).zero_of_le_dist <| by
    simpa [dist_eq_norm, Real.norm_eq_abs] using hx.le

theorem schwartzCutoff_smooth (N : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (schwartzCutoff N) := by
  simpa [schwartzCutoff] using (schwartzCutoffBump N).contDiff

def schwartzCutoffProfileSchwartz : SchwartzMap ℝ ℝ :=
  (schwartzCutoffBump 0).hasCompactSupport.toSchwartzMap
    ((schwartzCutoffBump 0).contDiff)

theorem schwartzCutoff_eq_profile_scaled (N : ℕ) :
    schwartzCutoff N =
      fun x => schwartzCutoffProfileSchwartz ((((N : ℝ) + 1)⁻¹) * x) := by
  funext x
  have hNp : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  simp [schwartzCutoff, schwartzCutoffBump, schwartzCutoffProfileSchwartz,
    ContDiffBump.apply, div_eq_mul_inv, sub_eq_add_neg, mul_left_comm, mul_comm,
    hNp.ne']

theorem schwartzCutoff_hasTemperateGrowth (N : ℕ) :
    (schwartzCutoff N).HasTemperateGrowth := by
  have hscale : (fun x : ℝ => (((N : ℝ) + 1)⁻¹) * x).HasTemperateGrowth := by
    fun_prop
  simpa [schwartzCutoff_eq_profile_scaled (N := N)] using
    schwartzCutoffProfileSchwartz.hasTemperateGrowth.comp hscale

theorem abs_iteratedDeriv_schwartzCutoff_le
    (i N : ℕ) (x : ℝ) :
    |iteratedDeriv i (schwartzCutoff N) x| ≤
      (((N : ℝ) + 1)⁻¹) ^ i *
        SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz := by
  have hscale :
      iteratedDeriv i (schwartzCutoff N) x =
        (((N : ℝ) + 1)⁻¹) ^ i *
          iteratedDeriv i schwartzCutoffProfileSchwartz ((((N : ℝ) + 1)⁻¹) * x) := by
    rw [schwartzCutoff_eq_profile_scaled (N := N)]
    simpa using
      congrFun
        (iteratedDeriv_comp_const_mul
          (n := i) (h := schwartzCutoffProfileSchwartz.smooth i) (((N : ℝ) + 1)⁻¹)) x
  have hsemi :
      |iteratedDeriv i schwartzCutoffProfileSchwartz ((((N : ℝ) + 1)⁻¹) * x)| ≤
        SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz := by
    simpa [pow_zero, Real.norm_eq_abs] using
      (SchwartzMap.le_seminorm' (𝕜 := ℝ) (k := 0) (n := i)
        schwartzCutoffProfileSchwartz ((((N : ℝ) + 1)⁻¹) * x))
  have hinv_nonneg : 0 ≤ (((N : ℝ) + 1)⁻¹) ^ i := by positivity
  calc
    |iteratedDeriv i (schwartzCutoff N) x|
      = |((((N : ℝ) + 1)⁻¹) ^ i *
          iteratedDeriv i schwartzCutoffProfileSchwartz ((((N : ℝ) + 1)⁻¹) * x))| := by
          rw [hscale]
    _ = (((N : ℝ) + 1)⁻¹) ^ i *
          |iteratedDeriv i schwartzCutoffProfileSchwartz ((((N : ℝ) + 1)⁻¹) * x)| := by
          rw [abs_mul, abs_of_nonneg hinv_nonneg]
    _ ≤ (((N : ℝ) + 1)⁻¹) ^ i *
          SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz := by
          gcongr

def schwartzCutoffCLM (N : ℕ) : SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ :=
  SchwartzMap.smulLeftCLM ℝ (schwartzCutoff N)

theorem schwartzCutoffCLM_apply (N : ℕ) (h : SchwartzMap ℝ ℝ) :
    schwartzCutoffCLM N h = fun x => schwartzCutoff N x * h x := by
  simpa [schwartzCutoffCLM, smul_eq_mul] using
    (SchwartzMap.smulLeftCLM_apply (F := ℝ) (g := schwartzCutoff N)
      (hg := schwartzCutoff_hasTemperateGrowth N) h)

@[simp] private theorem schwartzCutoffCLM_apply_apply
    (N : ℕ) (h : SchwartzMap ℝ ℝ) (x : ℝ) :
    schwartzCutoffCLM N h x = schwartzCutoff N x * h x := by
  simpa [schwartzCutoffCLM, smul_eq_mul] using
    (SchwartzMap.smulLeftCLM_apply_apply (F := ℝ) (g := schwartzCutoff N)
      (hg := schwartzCutoff_hasTemperateGrowth N) h x)

theorem schwartzCutoffCLM_eq_zero_of_two_mul_lt_abs
    (N : ℕ) (h : SchwartzMap ℝ ℝ) {x : ℝ}
    (hx : 2 * ((N : ℝ) + 1) < |x|) :
    schwartzCutoffCLM N h x = 0 := by
  rw [schwartzCutoffCLM_apply_apply, schwartzCutoff_eq_zero_of_two_mul_lt_abs N hx]
  simp

theorem schwartzCutoff_error_seminorm_le
    (h : SchwartzMap ℝ ℝ) (k n N : ℕ) :
    SchwartzMap.seminorm ℝ k n (h - schwartzCutoffCLM N h) ≤
      (Finset.sum (Finset.range (n + 1)) fun i =>
        if i = 0 then
          SchwartzMap.seminorm ℝ (k + 1) n h
        else
          (n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz *
            SchwartzMap.seminorm ℝ k (n - i) h) *
        (((N : ℝ) + 1)⁻¹) := by
  let Cterm : ℕ → ℝ := fun i =>
    if i = 0 then
      SchwartzMap.seminorm ℝ (k + 1) n h
    else
      (n.choose i : ℝ) *
        SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz *
        SchwartzMap.seminorm ℝ k (n - i) h
  have hCterm_nonneg : ∀ i, 0 ≤ Cterm i := by
    intro i
    by_cases hi : i = 0
    · simp only [Cterm, hi, if_true]
      exact apply_nonneg _ _
    · simp only [Cterm, hi, if_false]
      positivity
  refine SchwartzMap.seminorm_le_bound' (𝕜 := ℝ) (F := ℝ)
    (k := k) (n := n) (f := h - schwartzCutoffCLM N h) ?_ ?_
  · have hsum_nonneg : 0 ≤ Finset.sum (Finset.range (n + 1)) Cterm := by
      exact Finset.sum_nonneg fun i _ => hCterm_nonneg i
    positivity
  · intro x
    have hcut : ContDiffAt ℝ n (fun t => 1 - schwartzCutoff N t) x := by
      have hsmooth :
          ContDiff ℝ n (fun t => 1 - schwartzCutoff N t) :=
        contDiff_const.add
          (((schwartzCutoff_smooth N).of_le (by exact_mod_cast le_top)).neg)
      simpa [sub_eq_add_neg] using
        hsmooth.contDiffAt
    have hh : ContDiffAt ℝ n h x := by
      simpa using (h.smooth n).contDiffAt
    have hderiv :
        iteratedDeriv n (h - schwartzCutoffCLM N h) x =
          Finset.sum (Finset.range (n + 1)) fun i =>
            (n.choose i : ℝ) * iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x *
              iteratedDeriv (n - i) h x := by
      have hmul := iteratedDeriv_fun_mul (f := fun t => 1 - schwartzCutoff N t) (g := h) hcut hh
      have hEq : ((h - schwartzCutoffCLM N h : SchwartzMap ℝ ℝ) : ℝ → ℝ) =
          fun t => (1 - schwartzCutoff N t) * h t := by
        funext t
        simp [sub_eq_add_neg, schwartzCutoffCLM_apply_apply]
        ring
      change iteratedDeriv n (((h - schwartzCutoffCLM N h : SchwartzMap ℝ ℝ) : ℝ → ℝ)) x = _
      rw [hEq]
      simpa using hmul
    calc
      |x| ^ k * ‖iteratedDeriv n (h - schwartzCutoffCLM N h) x‖
        = |x| ^ k * ‖Finset.sum (Finset.range (n + 1)) fun i =>
            (n.choose i : ℝ) * iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x *
              iteratedDeriv (n - i) h x‖ := by
              rw [hderiv]
      _ ≤ Finset.sum (Finset.range (n + 1)) fun i =>
            |x| ^ k * ‖(n.choose i : ℝ) * iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x *
              iteratedDeriv (n - i) h x‖ := by
              have hx_nonneg : 0 ≤ |x| ^ k := by positivity
              have hsum_norm :
                  ‖Finset.sum (Finset.range (n + 1)) (fun i =>
                      (n.choose i : ℝ) * iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x *
                        iteratedDeriv (n - i) h x)‖ ≤
                    Finset.sum (Finset.range (n + 1)) (fun i =>
                      ‖(n.choose i : ℝ) * iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x *
                        iteratedDeriv (n - i) h x‖) := by
                exact norm_sum_le _ _
              calc
                |x| ^ k *
                    ‖Finset.sum (Finset.range (n + 1)) (fun i =>
                        (n.choose i : ℝ) * iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x *
                          iteratedDeriv (n - i) h x)‖
                  ≤ |x| ^ k *
                      Finset.sum (Finset.range (n + 1)) (fun i =>
                        ‖(n.choose i : ℝ) * iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x *
                          iteratedDeriv (n - i) h x‖) :=
                    mul_le_mul_of_nonneg_left hsum_norm hx_nonneg
                _ = Finset.sum (Finset.range (n + 1)) (fun i =>
                      |x| ^ k *
                        ‖(n.choose i : ℝ) * iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x *
                          iteratedDeriv (n - i) h x‖) := by
                    rw [Finset.mul_sum]
      _ ≤ Finset.sum (Finset.range (n + 1)) fun i => Cterm i * (((N : ℝ) + 1)⁻¹) := by
              apply Finset.sum_le_sum
              intro i hi
              by_cases hi0 : i = 0
              · subst hi0
                by_cases hx : |x| ≤ (N : ℝ) + 1
                · have hnonneg : 0 ≤ Cterm 0 * (((N : ℝ) + 1)⁻¹) := by
                    positivity
                  simpa [Cterm, schwartzCutoff_eq_one_of_abs_le N hx] using hnonneg
                · have hlarge : (N : ℝ) + 1 < |x| := lt_of_not_ge hx
                  have hfactor :
                      |1 - schwartzCutoff N x| ≤ 1 := by
                    have hnonneg : 0 ≤ 1 - schwartzCutoff N x := by
                      linarith [schwartzCutoff_le_one N x]
                    rw [abs_of_nonneg hnonneg]
                    linarith [schwartzCutoff_nonneg N x]
                  have hsemi :
                      |x| ^ (k + 1) * |iteratedDeriv n h x| ≤
                        SchwartzMap.seminorm ℝ (k + 1) n h := by
                    simpa [Real.norm_eq_abs] using
                      (SchwartzMap.le_seminorm' (𝕜 := ℝ) (k := k + 1) (n := n) h x)
                  have htail :
                      |x| ^ k * |iteratedDeriv n h x| ≤
                        SchwartzMap.seminorm ℝ (k + 1) n h * (((N : ℝ) + 1)⁻¹) := by
                    have hmul :
                        ((N : ℝ) + 1) * (|x| ^ k * |iteratedDeriv n h x|) ≤
                          SchwartzMap.seminorm ℝ (k + 1) n h := by
                      calc
                        ((N : ℝ) + 1) * (|x| ^ k * |iteratedDeriv n h x|)
                          ≤ |x| * (|x| ^ k * |iteratedDeriv n h x|) := by
                              gcongr
                        _ = |x| ^ (k + 1) * |iteratedDeriv n h x| := by ring
                        _ ≤ SchwartzMap.seminorm ℝ (k + 1) n h := hsemi
                    have hNp : 0 < (N : ℝ) + 1 := by positivity
                    have hunit : ((N : ℝ) + 1) * (((N : ℝ) + 1)⁻¹) = 1 := by
                      field_simp [hNp.ne']
                    calc
                      |x| ^ k * |iteratedDeriv n h x|
                        = (((N : ℝ) + 1) * (((N : ℝ) + 1)⁻¹)) *
                            (|x| ^ k * |iteratedDeriv n h x|) := by
                              rw [hunit, one_mul]
                      _ = (((N : ℝ) + 1) * (|x| ^ k * |iteratedDeriv n h x|)) *
                            (((N : ℝ) + 1)⁻¹) := by ring
                      _ ≤ SchwartzMap.seminorm ℝ (k + 1) n h * (((N : ℝ) + 1)⁻¹) := by
                              gcongr
                  calc
                    |x| ^ k *
                        ‖(n.choose 0 : ℝ) * iteratedDeriv 0 (fun t => 1 - schwartzCutoff N t) x *
                          iteratedDeriv (n - 0) h x‖
                      = |x| ^ k * (|1 - schwartzCutoff N x| * |iteratedDeriv n h x|) := by
                          simp [Real.norm_eq_abs]
                    _ ≤ |x| ^ k * (1 * |iteratedDeriv n h x|) := by
                          gcongr
                    _ = |x| ^ k * |iteratedDeriv n h x| := by ring
                    _ ≤ Cterm 0 * (((N : ℝ) + 1)⁻¹) := by
                          simpa [Cterm]
                            using htail
              · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
                have hcutBoundAbs :
                    |iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x| ≤
                      (((N : ℝ) + 1)⁻¹) ^ i *
                        SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz := by
                  rw [iteratedDeriv_const_sub hi_pos (1 : ℝ), iteratedDeriv_neg, abs_neg]
                  exact abs_iteratedDeriv_schwartzCutoff_le i N x
                have hcutBound :
                    ‖iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x‖ ≤
                      (((N : ℝ) + 1)⁻¹) ^ i *
                        SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz := by
                  simpa [Real.norm_eq_abs] using hcutBoundAbs
                have hhBoundAbs :
                    |x| ^ k * |iteratedDeriv (n - i) h x| ≤
                      SchwartzMap.seminorm ℝ k (n - i) h := by
                  simpa [Real.norm_eq_abs] using
                    (SchwartzMap.le_seminorm' (𝕜 := ℝ) (k := k) (n := n - i) h x)
                have hinv_nonneg : 0 ≤ ((N : ℝ) + 1)⁻¹ := by positivity
                have hinv_le_one : ((N : ℝ) + 1)⁻¹ ≤ 1 := by
                  have hone : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith
                  exact inv_le_one_of_one_le₀ hone
                have hpow_le :
                    (((N : ℝ) + 1)⁻¹) ^ i ≤ ((N : ℝ) + 1)⁻¹ := by
                  rcases Nat.exists_eq_succ_of_ne_zero hi0 with ⟨j, rfl⟩
                  have hpowj : (((N : ℝ) + 1)⁻¹) ^ j ≤ 1 := by
                    exact pow_le_one₀ hinv_nonneg hinv_le_one
                  calc
                    (((N : ℝ) + 1)⁻¹) ^ (j + 1)
                      = (((N : ℝ) + 1)⁻¹) ^ j * ((N : ℝ) + 1)⁻¹ := by
                          rw [pow_succ]
                    _ ≤ 1 * ((N : ℝ) + 1)⁻¹ := by
                          exact mul_le_mul_of_nonneg_right hpowj hinv_nonneg
                    _ = ((N : ℝ) + 1)⁻¹ := by ring
                calc
                  |x| ^ k *
                      ‖(n.choose i : ℝ) * iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x *
                        iteratedDeriv (n - i) h x‖
                    = (n.choose i : ℝ) *
                        (|iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x| *
                          (|x| ^ k * |iteratedDeriv (n - i) h x|)) := by
                            rw [Real.norm_eq_abs, abs_mul, abs_mul,
                              abs_of_nonneg (by positivity : 0 ≤ (n.choose i : ℝ))]
                            ring
                  _ ≤ (n.choose i : ℝ) *
                        ((((N : ℝ) + 1)⁻¹) ^ i *
                          SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz) *
                        SchwartzMap.seminorm ℝ k (n - i) h := by
                          have hchoose_nonneg : 0 ≤ (n.choose i : ℝ) := by positivity
                          have hrhs_nonneg :
                              0 ≤ (((N : ℝ) + 1)⁻¹) ^ i *
                                SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz := by
                            positivity
                          have htail_nonneg : 0 ≤ |x| ^ k * |iteratedDeriv (n - i) h x| := by
                            positivity
                          have hprod_bound :
                              |iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x| *
                                  (|x| ^ k * |iteratedDeriv (n - i) h x|) ≤
                                ((((N : ℝ) + 1)⁻¹) ^ i *
                                  SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz) *
                                  SchwartzMap.seminorm ℝ k (n - i) h := by
                            exact mul_le_mul hcutBoundAbs hhBoundAbs htail_nonneg hrhs_nonneg
                          simpa [mul_assoc] using
                            (mul_le_mul_of_nonneg_left hprod_bound hchoose_nonneg)
                  _ ≤ (n.choose i : ℝ) *
                        ((((N : ℝ) + 1)⁻¹) *
                          SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz) *
                        SchwartzMap.seminorm ℝ k (n - i) h := by
                          have hsemi_nonneg :
                              0 ≤ SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz := by
                            exact apply_nonneg _ _
                          have hhsemi_nonneg :
                              0 ≤ SchwartzMap.seminorm ℝ k (n - i) h := by
                            exact apply_nonneg _ _
                          apply mul_le_mul_of_nonneg_right
                          · apply mul_le_mul_of_nonneg_left
                            · exact mul_le_mul_of_nonneg_right hpow_le hsemi_nonneg
                            · positivity
                          · exact hhsemi_nonneg
                  _ = Cterm i * (((N : ℝ) + 1)⁻¹) := by
                          simp [Cterm, hi0, mul_left_comm, mul_comm]
      _ = (Finset.sum (Finset.range (n + 1)) Cterm) * (((N : ℝ) + 1)⁻¹) := by
              rw [Finset.sum_mul]

theorem schwartzCutoffCLM_tendsto
    (h : SchwartzMap ℝ ℝ) :
    Tendsto (fun N => schwartzCutoffCLM N h) atTop (nhds h) := by
  rw [(schwartz_withSeminorms ℝ ℝ ℝ).tendsto_nhds]
  intro m ε hε
  let C : ℝ :=
    Finset.sum (Finset.range (m.2 + 1)) fun i =>
      if i = 0 then
        SchwartzMap.seminorm ℝ (m.1 + 1) m.2 h
      else
        (m.2.choose i : ℝ) *
          SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz *
          SchwartzMap.seminorm ℝ m.1 (m.2 - i) h
  have hC_nonneg : 0 ≤ C := by
    unfold C
    exact Finset.sum_nonneg fun i _ => by
      by_cases hi : i = 0
      · simp only [hi, if_true]
        exact apply_nonneg _ _
      · simp only [hi, if_false]
        positivity
  have h_inv :
      Tendsto (fun N : ℕ => (((N : ℝ) + 1)⁻¹)) atTop (nhds 0) := by
    simpa using
      (tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop))
  have h_bound_tend :
      Tendsto (fun N : ℕ => C * (((N : ℝ) + 1)⁻¹)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul h_inv)
  have h_bound_ev : ∀ᶠ N : ℕ in atTop, C * (((N : ℝ) + 1)⁻¹) < ε := by
    exact (Metric.tendsto_nhds.mp h_bound_tend) ε hε |>.mono fun N hN => by
      have hInv_nonneg : 0 ≤ (((N : ℝ) + 1)⁻¹) := by positivity
      have hNatAbs : |((N : ℝ) + 1)| = (N : ℝ) + 1 := by
        exact abs_of_nonneg (by positivity)
      have hCabs : |C| = C := abs_of_nonneg hC_nonneg
      have hInvabs : |(((N : ℝ) + 1)⁻¹)| = (((N : ℝ) + 1)⁻¹) := abs_of_nonneg hInv_nonneg
      simpa [Real.dist_eq, abs_mul, hCabs, hInvabs, hNatAbs] using hN
  filter_upwards [h_bound_ev] with N hN
  have hle :
      SchwartzMap.seminorm ℝ m.1 m.2 (schwartzCutoffCLM N h - h) ≤
        C * (((N : ℝ) + 1)⁻¹) := by
    have hsym : schwartzCutoffCLM N h - h = -(h - schwartzCutoffCLM N h) := by
      abel
    calc
      SchwartzMap.seminorm ℝ m.1 m.2 (schwartzCutoffCLM N h - h)
        = SchwartzMap.seminorm ℝ m.1 m.2 (h - schwartzCutoffCLM N h) := by
            rw [hsym, map_neg_eq_map]
      _ ≤ C * (((N : ℝ) + 1)⁻¹) := by
            unfold C
            exact schwartzCutoff_error_seminorm_le h m.1 m.2 N
  exact lt_of_le_of_lt hle hN


end Pphi2
