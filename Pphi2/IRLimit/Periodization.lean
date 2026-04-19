/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas
-/

/-
# Periodization: Re-export from gaussian-field

The periodization CLM `𝓢(ℝ) →L[ℝ] C∞(S¹_L)` is defined in
`SchwartzNuclear.Periodization` in the gaussian-field package.
This file re-exports it for use in pphi2's IR limit.
-/

import SchwartzNuclear.Periodization

namespace Pphi2

-- Re-export periodizeCLM from gaussian-field
open GaussianField Filter

section
variable (L : ℝ) [hL : Fact (0 < L)]

/-- Symmetric-window version of `GaussianField.periodizeCLM_eq_on_large_period`.

If a Schwartz function is supported in `[-T, T]`, then once the circle period is larger than
`4 * T`, its periodization agrees with the original function on the same symmetric interval.
The proof shifts `[-T, T]` to `[0, 2 * T]`, applies the one-sided large-period lemma there,
and then shifts back. -/
theorem periodizeCLM_eq_on_symmetric_large_period
    (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (hL_large : L > 4 * T) :
    ∀ t ∈ Set.Icc (-T) T, (periodizeCLM L h).toFun t = h t := by
  let hshift := schwartzTranslation T h
  have hshift_supp : ∀ u, 2 * T < |u| → hshift u = 0 := by
    intro u hu
    have hu' : T < |u - T| := by
      by_cases hu_nonneg : 0 ≤ u
      · rw [abs_of_nonneg hu_nonneg] at hu
        by_cases hTu : T ≤ u
        · rw [abs_of_nonneg (sub_nonneg.mpr hTu)]
          linarith
        · have hu_lt : u < T := by
            linarith
          rw [abs_of_neg (sub_neg.mpr hu_lt)]
          linarith
      · have hu_neg : u < 0 := lt_of_not_ge hu_nonneg
        rw [abs_of_neg hu_neg] at hu
        have hsub_neg : u - T < 0 := by
          linarith
        rw [abs_of_neg hsub_neg]
        linarith
    simp [hshift, schwartzTranslation_apply, hsupp (u - T) hu']
  have hshift_eq :=
    periodizeCLM_eq_on_large_period (L := L) hshift (2 * T)
      (by positivity) hshift_supp (by linarith [hL_large])
  intro t ht
  have ht_shift : t + T ∈ Set.Icc 0 (L / 2) := by
    constructor
    · linarith [ht.1]
    · have hLT : 2 * T < L / 2 := by
        linarith [hL_large]
      linarith [ht.2, hLT]
  have hmain := hshift_eq (t + T) ht_shift
  change (periodizeCLM L hshift) (t + T) = hshift (t + T) at hmain
  change (periodizeCLM L h) t = h t
  have hcomm :
      (periodizeCLM L hshift) (t + T) = (periodizeCLM L h) t := by
    rw [show hshift = schwartzTranslation T h by rfl, periodizeCLM_comp_schwartzTranslation]
    simp [circleTranslation]
  calc
    (periodizeCLM L h) t = (periodizeCLM L hshift) (t + T) := by
      symm
      exact hcomm
    _ = hshift (t + T) := hmain
    _ = h t := by
      simp [hshift, schwartzTranslation_apply]

end

/-- For compactly supported Schwartz functions, periodization converges uniformly on the fixed
symmetric support window because it is eventually exactly equal there. -/
theorem periodizeCLM_tendsto_uniformlyOn_symmetricCompact
    (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn
      (fun n t => (@periodizeCLM (Lt n) (hLt n) h).toFun t)
      h atTop (Set.Icc (-T) T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlarge : ∀ᶠ n in atTop, 4 * T + 1 ≤ Lt n :=
    (Filter.tendsto_atTop.mp hLt_tend) (4 * T + 1)
  filter_upwards [hlarge] with n hn t ht
  have heq :=
    periodizeCLM_eq_on_symmetric_large_period
      (L := Lt n) h T hT hsupp (by linarith) t ht
  rw [Real.dist_eq]
  simpa [heq] using hε

/-- Summability of the quadratic model tail on `ℤ`. -/
private theorem summable_inv_int_sq_mul (C L : ℝ) :
    Summable (fun k : ℤ => C / ((↑|k| : ℝ) * L) ^ 2) := by
  by_cases hL : L = 0
  · simp [hL]
  · have heq :
      (fun k : ℤ => C / ((↑|k| : ℝ) * L) ^ 2) =
        (fun k : ℤ => (C / L ^ 2) * (1 / (↑|k| : ℝ) ^ 2)) := by
      ext k
      ring
    rw [heq]
    apply Summable.mul_left
    rw [summable_int_iff_summable_nat_and_neg]
    refine ⟨?_, ?_⟩ <;>
      exact ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)).congr
        fun n => by simp [abs_of_nonneg (Int.natCast_nonneg n), abs_neg]

/-- Universal square-summable tail constant over `ℤ`. -/
private noncomputable def intInvSqSum : ℝ :=
  ∑' k : ℤ, 1 / (↑|k| : ℝ) ^ 2

private theorem intInvSqSum_nonneg : 0 ≤ intInvSqSum := by
  unfold intInvSqSum
  exact tsum_nonneg fun k => by positivity

/-- Split off the `k = 0` term in the periodization sum. -/
private theorem periodizeFun_sub_eq_tsum_tail
    {L : ℝ} [Fact (0 < L)] (h : SchwartzMap ℝ ℝ) (t : ℝ) :
    periodizeFun L h t - h t =
      ∑' k : ℤ, if k = 0 then 0 else h (t + k * L) := by
  let g : ℤ → ℝ := fun k => if k = 0 then h t else 0
  let r : ℤ → ℝ := fun k => if k = 0 then 0 else h (t + k * L)
  have hs : Summable (fun k : ℤ => h (t + k * L)) := periodize_summable L h t
  have hg : Summable g := (hasSum_ite_eq (0 : ℤ) (h t)).summable
  have hr_eq : r = (fun k : ℤ => h (t + k * L)) - g := by
    funext k
    by_cases hk : k = 0 <;> simp [g, r, hk]
  have hr : Summable r := by
    rw [hr_eq]
    exact hs.sub hg
  unfold periodizeFun
  calc
    ∑' k : ℤ, h (t + k * L) - h t
      = (∑' k : ℤ, (g k + r k)) - h t := by
          rw [show (fun k : ℤ => h (t + k * L)) = fun k : ℤ => g k + r k from by
            funext k
            by_cases hk : k = 0 <;> simp [g, r, hk]]
    _ = (∑' k : ℤ, g k) + ∑' k : ℤ, r k - h t := by
          rw [← (hg.hasSum.add hr.hasSum).tsum_eq]
    _ = ∑' k : ℤ, r k := by
          simp [g, r, tsum_ite_eq]
    _ = ∑' k : ℤ, if k = 0 then 0 else h (t + k * L) := by
          rfl

/-- If `t` lies in the centered fundamental window, every nonzero period shift
stays at least `|k|L/2` away from the origin. -/
private theorem centered_window_shift_abs_lower_bound
    {L t : ℝ} (hL : 0 < L) (ht : |t| ≤ L / 2)
    (k : ℤ) (hk : k ≠ 0) :
    ((↑|k| : ℝ) * L) / 2 ≤ |t + k * L| := by
  have hk_pos_nat : 0 < |k| := by
    simpa using Int.natAbs_pos.mpr hk
  have hk_ge_one : (1 : ℝ) ≤ (↑|k| : ℝ) := by
    exact_mod_cast hk_pos_nat
  have hhalf_le : L / 2 ≤ (↑|k| : ℝ) * L / 2 := by
    nlinarith
  have h_abs_kL : |(k : ℝ) * L| = (↑|k| : ℝ) * L := by
    rw [abs_mul, abs_of_pos hL]
    push_cast
    rfl
  have hmain : (↑|k| : ℝ) * L ≤ |t + k * L| + |t| := by
    calc
      (↑|k| : ℝ) * L = |(k : ℝ) * L| := h_abs_kL.symm
      _ = |(t + k * L) + (-t)| := by ring_nf
      _ ≤ |t + k * L| + |-t| := abs_add_le _ _
      _ = |t + k * L| + |t| := by rw [abs_neg]
  linarith

/-- Quantitative large-period control: on every fixed symmetric compact window,
the difference between a Schwartz function and its periodization is `O(L⁻²)`. -/
private theorem periodizeCLM_sub_abs_le_inv_sq_on_symmetricCompact_aux
    (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {L : ℝ} [Fact (0 < L)], 4 * T ≤ L →
        ∀ t ∈ Set.Icc (-T) T,
          |(@periodizeCLM L ‹Fact (0 < L)› h).toFun t - h t| ≤ C / L ^ 2 := by
  set S : ℝ :=
    2 ^ (2 : ℕ) *
      ((Finset.Iic ((2 : ℕ), (0 : ℕ))).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) h
  have hS_nonneg : 0 ≤ S := by
    positivity
  have hdecay : ∀ x : ℝ, |h x| ≤ S / (1 + |x|) ^ 2 := by
    intro x
    have hraw :=
      SchwartzMap.one_add_le_sup_seminorm_apply
        (𝕜 := ℝ) (m := (2, 0)) (k := 2) (n := 0)
        (le_refl 2) (le_refl 0) h x
    simp only [norm_iteratedFDeriv_zero] at hraw
    have hraw' : (1 + |x|) ^ 2 * |h x| ≤ S := by
      simpa [S, Real.norm_eq_abs] using hraw
    have hden_pos : 0 < (1 + |x|) ^ 2 := by positivity
    exact (le_div_iff₀ hden_pos).2 (by simpa [mul_comm] using hraw')
  let C : ℝ := 4 * S * intInvSqSum
  refine ⟨C, by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by positivity) hS_nonneg) intInvSqSum_nonneg, ?_⟩
  intro L hL hL_large t ht
  let F : ℤ → ℝ := fun k => if k = 0 then 0 else h (t + k * L)
  have hL_pos : 0 < L := Fact.out
  have ht_abs : |t| ≤ T := by
    rw [abs_le]
    simpa using ht
  have ht_half : |t| ≤ L / 2 := by
    linarith
  have hpt :
      ∀ k : ℤ, |F k| ≤ 4 * S / ((↑|k| : ℝ) * L) ^ 2 := by
    intro k
    by_cases hk : k = 0
    · simp [F, hk]
    · have hshift :
        ((↑|k| : ℝ) * L) / 2 ≤ |t + k * L| := by
          exact centered_window_shift_abs_lower_bound hL_pos ht_half k hk
      have hbase :
          ((↑|k| : ℝ) * L) / 2 ≤ 1 + |t + k * L| := by
        linarith
      have hpow :
          (((↑|k| : ℝ) * L) / 2) ^ 2 ≤ (1 + |t + k * L|) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) hbase 2
      have hmain :
          |h (t + k * L)| ≤ 4 * S / ((↑|k| : ℝ) * L) ^ 2 := by
        calc
          |h (t + k * L)| ≤ S / (1 + |t + k * L|) ^ 2 := hdecay (t + k * L)
          _ ≤ S / ((((↑|k| : ℝ) * L) / 2) ^ 2) := by
                apply div_le_div_of_nonneg_left hS_nonneg
                · positivity
                · exact hpow
          _ = 4 * S / ((↑|k| : ℝ) * L) ^ 2 := by
                have hkL_ne : ((↑|k| : ℝ) * L) ≠ 0 := by positivity
                field_simp [hkL_ne]
                ring
      simpa [F, hk] using hmain
  have hdom_sum :
      Summable (fun k : ℤ => 4 * S / ((↑|k| : ℝ) * L) ^ 2) :=
    summable_inv_int_sq_mul (4 * S) L
  have hdom_sum' :
      Summable (fun k : ℤ => 4 * S / ((abs (k : ℝ)) * L) ^ 2) := by
    simpa using hdom_sum
  have hnorm_sum : Summable (fun k : ℤ => ‖F k‖) := by
    apply Summable.of_nonneg_of_le
    · intro k
      exact norm_nonneg _
    · intro k
      simpa [F, Real.norm_eq_abs] using hpt k
    · exact hdom_sum'
  have htail :
      |(@periodizeCLM L hL h).toFun t - h t| ≤
        ∑' k : ℤ, 4 * S / ((↑|k| : ℝ) * L) ^ 2 := by
    change |periodizeFun L h t - h t| ≤
      ∑' k : ℤ, 4 * S / ((↑|k| : ℝ) * L) ^ 2
    rw [periodizeFun_sub_eq_tsum_tail (h := h) (t := t)]
    calc
      |∑' k : ℤ, F k| = ‖∑' k : ℤ, F k‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∑' k : ℤ, ‖F k‖ := norm_tsum_le_tsum_norm hnorm_sum
      _ ≤ ∑' k : ℤ, 4 * S / ((↑|k| : ℝ) * L) ^ 2 := by
            apply Summable.tsum_le_tsum
            · intro k
              simpa [F, Real.norm_eq_abs] using hpt k
            · exact hnorm_sum
            · exact hdom_sum
  have hseries :
      ∑' k : ℤ, 4 * S / ((↑|k| : ℝ) * L) ^ 2 =
        (4 * S / L ^ 2) * intInvSqSum := by
    have heq :
        (fun k : ℤ => 4 * S / ((↑|k| : ℝ) * L) ^ 2) =
          (fun k : ℤ => (4 * S / L ^ 2) * (1 / (↑|k| : ℝ) ^ 2)) := by
      ext k
      ring
    rw [heq, tsum_mul_left]
    simp [intInvSqSum]
  calc
    |(@periodizeCLM L hL h).toFun t - h t|
      ≤ ∑' k : ℤ, 4 * S / ((↑|k| : ℝ) * L) ^ 2 := htail
    _ = (4 * S / L ^ 2) * intInvSqSum := hseries
    _ = C / L ^ 2 := by
          dsimp [C]
          ring

/-- For every Schwartz function, periodization converges uniformly to the
original function on each fixed symmetric compact window as the period tends to
infinity. Unlike `periodizeCLM_tendsto_uniformlyOn_symmetricCompact`, no
compact-support hypothesis is required. -/
theorem periodizeCLM_tendsto_uniformlyOn_symmetricCompact_schwartz
    (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn
      (fun n t => (@periodizeCLM (Lt n) (hLt n) h).toFun t)
      h atTop (Set.Icc (-T) T) := by
  obtain ⟨C, hC_nonneg, hbound⟩ :=
    periodizeCLM_sub_abs_le_inv_sq_on_symmetricCompact_aux h T hT
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlarge :
      ∀ᶠ n in atTop, max (4 * T) (Real.sqrt (C / ε) + 1) ≤ Lt n :=
    (Filter.tendsto_atTop.mp hLt_tend) (max (4 * T) (Real.sqrt (C / ε) + 1))
  filter_upwards [hlarge] with n hn t ht
  letI : Fact (0 < Lt n) := hLt n
  have hLn_pos : 0 < Lt n := Fact.out
  have hsmall_aux_nonneg : 0 ≤ C / ε := by
    exact div_nonneg hC_nonneg hε.le
  have hthreshold_sq :
      (Real.sqrt (C / ε) + 1) ^ 2 ≤ (Lt n) ^ 2 := by
    have hthreshold_le : Real.sqrt (C / ε) + 1 ≤ Lt n := le_trans (le_max_right _ _) hn
    exact pow_le_pow_left₀ (by positivity) hthreshold_le 2
  have hsmall_aux :
      C / ε < (Real.sqrt (C / ε) + 1) ^ 2 := by
    calc
      C / ε = (Real.sqrt (C / ε)) ^ 2 := by
        symm
        exact Real.sq_sqrt hsmall_aux_nonneg
      _ < (Real.sqrt (C / ε) + 1) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (C / ε)]
  have hsmall_ratio : C / ε < (Lt n) ^ 2 :=
    lt_of_lt_of_le hsmall_aux hthreshold_sq
  have hsmall : C / (Lt n) ^ 2 < ε := by
    have hLt_sq_pos : 0 < (Lt n) ^ 2 := by positivity
    have hmult : C < (Lt n) ^ 2 * ε := by
      rw [div_lt_iff₀ hε] at hsmall_ratio
      nlinarith [hsmall_ratio]
    rw [div_lt_iff₀ hLt_sq_pos]
    nlinarith [hmult]
  have hmain := hbound (L := Lt n) (le_trans (le_max_left _ _) hn) t ht
  rw [Real.dist_eq]
  simpa [abs_sub_comm] using (lt_of_le_of_lt hmain hsmall)

end Pphi2
