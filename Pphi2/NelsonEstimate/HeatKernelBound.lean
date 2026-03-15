/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Heat Kernel Trace Bound

The core analytic lemma for Nelson's estimate: the trace of the lattice
heat kernel H(t) = Σ_k exp(-t·λ_k) satisfies H(t) ≤ C/t uniformly in N.

This reduces both eigenvalue sum bounds (smoothVariance_le_log and
roughCovariance_sq_summable) to elementary 1D calculus.

## Main results

- `schwinger_smooth` — `exp(-Tλ)/λ = ∫_T^∞ exp(-tλ) dt`
- `schwinger_rough` — `(1-exp(-Tλ))/λ = ∫₀ᵀ exp(-tλ) dt`
- `sin_sq_lower_bound` — `sin²(x) ≥ (2/π)²·x²` for |x| ≤ π/2
- `gaussian_sum_bound` — `Σ_k exp(-α·k²) ≤ 1 + √(π/α)`
- `heat_kernel_trace_bound` — `H(t) ≤ C/t` (uniform in N)

## References

- Gemini analysis of eigenvalue sum bounds via Schwinger parametrization
- Standard lattice QFT heat kernel estimates
-/

import Pphi2.NelsonEstimate.CovarianceSplit
import Pphi2.InteractingMeasure.LatticeMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SumIntegralComparisons

noncomputable section

open GaussianField MeasureTheory Real Finset
open scoped BigOperators

namespace Pphi2

/-! ## Schwinger parametrization identities -/

/-- Schwinger identity for the smooth covariance:
`exp(-T·λ) / λ = ∫_T^∞ exp(-t·λ) dt` for λ > 0, T ≥ 0. -/
private theorem hasDerivAt_neg_exp_div (lam : ℝ) (hlam : lam ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => -exp (-s * lam) / lam) (exp (-t * lam)) t := by
  have h1 : HasDerivAt (fun s => -s * lam) (-lam) t := by
    simpa using (hasDerivAt_id t).neg.mul_const lam
  have h2 : HasDerivAt (fun s => exp (-s * lam)) (exp (-t * lam) * (-lam)) t :=
    h1.exp
  have h3 := h2.neg.div_const lam
  convert h3 using 1
  field_simp

theorem schwinger_smooth_Ioi (lam : ℝ) (hlam : 0 < lam) (T : ℝ) :
    exp (-T * lam) / lam = ∫ t in Set.Ioi T, exp (-t * lam) := by
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  set F := fun t => -exp (-t * lam) / lam
  -- F'(t) = exp(-tλ) (proved)
  have h_deriv : ∀ t ∈ Set.Ici T, HasDerivAt F (exp (-t * lam)) t :=
    fun t _ => hasDerivAt_neg_exp_div lam hlam_ne t
  -- F(t) → 0 as t → ∞ (exponential decay)
  have h_tendsto : Filter.Tendsto F Filter.atTop (nhds 0) := by
    show Filter.Tendsto (fun t => -rexp (-t * lam) / lam) Filter.atTop (nhds 0)
    have h1 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (Filter.tendsto_id.const_mul_atTop hlam)).neg.div_const lam
    simp only [neg_zero, zero_div] at h1
    exact h1.congr (fun t => by simp; ring)
  -- Apply improper FTC (nonneg version — no integrability needed!)
  -- g(t) = -exp(-tλ)/λ is increasing (g' = exp(-tλ) ≥ 0), g → 0
  have h_ftc := integral_Ioi_of_hasDerivAt_of_nonneg'
    h_deriv
    (fun t _ => le_of_lt (Real.exp_pos _))
    h_tendsto
  -- h_ftc : ∫ Ioi T, exp(-tλ) = 0 - F(T) = exp(-Tλ)/λ
  rw [h_ftc]; simp only [F]; ring

theorem schwinger_smooth (lam : ℝ) (hlam : 0 < lam) (T : ℝ) (hT : 0 ≤ T) :
    exp (-T * lam) / lam = ∫ t in Set.Ici T, exp (-t * lam) := by
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  exact schwinger_smooth_Ioi lam hlam T

/-- Schwinger identity for the rough covariance:
`(1 - exp(-T·λ)) / λ = ∫₀ᵀ exp(-t·λ) dt` for λ > 0, T ≥ 0. -/
theorem schwinger_rough_interval (lam : ℝ) (hlam : 0 < lam) (T : ℝ) (hT : 0 ≤ T) :
    (1 - exp (-T * lam)) / lam = ∫ t in (0)..T, exp (-t * lam) := by
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  set F := fun t => -exp (-t * lam) / lam
  have h_cont : ContinuousOn (fun t => exp (-t * lam)) (Set.uIcc 0 T) :=
    (Real.continuous_exp.comp (continuous_neg.mul continuous_const)).continuousOn
  have h_ftc : ∫ t in (0 : ℝ)..T, exp (-t * lam) = F T - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_neg_exp_div lam hlam_ne t)
      h_cont.intervalIntegrable
  rw [h_ftc]; simp only [F, neg_zero, zero_mul, exp_zero]; field_simp; ring

theorem schwinger_rough (lam : ℝ) (hlam : 0 < lam) (T : ℝ) (hT : 0 ≤ T) :
    (1 - exp (-T * lam)) / lam = ∫ t in Set.Icc 0 T, exp (-t * lam) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hT]
  exact schwinger_rough_interval lam hlam T hT

/-! ## Elementary bounds -/

/-- The standard trigonometric inequality: `sin(x)² ≥ (2/π)²·x²` for |x| ≤ π/2.
Equivalently: `sin(x) ≥ 2x/π` on [0, π/2] (Jordan's inequality). -/
theorem sin_sq_lower_bound (x : ℝ) (hx : |x| ≤ π / 2) :
    (2 / π) ^ 2 * x ^ 2 ≤ sin x ^ 2 := by
  -- From Mathlib's Jordan inequality: 2/π * |x| ≤ |sin x| for |x| ≤ π/2
  have h := Real.mul_abs_le_abs_sin hx
  -- Square both sides (both are nonneg)
  have h1 : (2 / π) ^ 2 * x ^ 2 = (2 / π * |x|) ^ 2 := by
    rw [mul_pow]; congr 1; rw [sq_abs]
  rw [h1]
  have h2 : sin x ^ 2 = |sin x| ^ 2 := by rw [sq_abs]
  rw [h2]
  exact pow_le_pow_left₀ (by positivity) h 2

/-- Helper: exp(-α*x²) is antitone on [0, ∞) for α > 0. -/
private lemma antitoneOn_exp_neg_mul_sq (α : ℝ) (hα : 0 < α) :
    AntitoneOn (fun x : ℝ => exp (-α * x ^ 2)) (Set.Ici 0) := by
  intro x hx y hy hxy
  apply exp_le_exp.mpr
  -- Need: -α * y² ≤ -α * x², i.e., α * x² ≤ α * y²
  have hx' := Set.mem_Ici.mp hx
  linarith [mul_le_mul_of_nonneg_left (sq_le_sq' (by linarith : -y ≤ x) hxy) hα.le]

/-- Helper: the sum over positive integers is bounded by the half-line Gaussian integral. -/
private lemma sum_exp_neg_mul_sq_le_integral (α : ℝ) (hα : 0 < α) (M : ℕ) :
    (∑ k ∈ Finset.range M, exp (-α * ((k : ℝ) + 1) ^ 2)) ≤
    ∫ x in Set.Ioi 0, exp (-α * x ^ 2) := by
  -- First bound the finite sum by the finite integral via antitone comparison
  have hanti : AntitoneOn (fun x : ℝ => exp (-α * x ^ 2)) (Set.Icc 0 (0 + (M : ℝ))) := by
    apply (antitoneOn_exp_neg_mul_sq α hα).mono
    exact Set.Icc_subset_Ici_self
  -- The AntitoneOn.sum_le_integral uses (i + 1 : Nat), we need (i : Nat) + 1
  have h1 := AntitoneOn.sum_le_integral hanti
  simp only [zero_add, Nat.cast_add, Nat.cast_one] at h1
  -- Now bound the finite interval integral by the half-line integral
  calc ∑ k ∈ Finset.range M, exp (-α * ((k : ℝ) + 1) ^ 2)
    _ ≤ ∫ x in (0 : ℝ)..↑M, exp (-α * x ^ 2) := h1
    _ = ∫ x in Set.Ioc 0 (M : ℝ), exp (-α * x ^ 2) := by
        rw [intervalIntegral.integral_of_le (Nat.cast_nonneg M)]
    _ ≤ ∫ x in Set.Ioi 0, exp (-α * x ^ 2) := by
        apply MeasureTheory.setIntegral_mono_set
        · exact (integrable_exp_neg_mul_sq hα).integrableOn
        · exact ae_of_all _ (fun x => le_of_lt (exp_pos _))
        · exact (Set.Ioc_subset_Ioi_self).eventuallyLE

/-- Helper: splitting an Icc sum on Z into k=0, positive, and negative parts. -/
private lemma sum_Icc_neg_pos_split (M : ℕ) (f : ℤ → ℝ) :
    ∑ k ∈ Finset.Icc (-(M : ℤ)) M, f k =
    f 0 + ∑ k ∈ Finset.Icc (1 : ℤ) M, f k + ∑ k ∈ Finset.Icc (1 : ℤ) M, f (-k) := by
  -- Split Icc (-M) M = Icc (-M) (-1) ∪ {0} ∪ Icc 1 M
  have h_eq : Finset.Icc (-(M : ℤ)) M =
      Finset.Icc (-(M : ℤ)) (-1) ∪ {(0 : ℤ)} ∪ Finset.Icc (1 : ℤ) M := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    omega
  have h_d1 : Disjoint (Finset.Icc (-(M : ℤ)) (-1)) {(0 : ℤ)} := by
    simp [Finset.disjoint_left, Finset.mem_Icc]; omega
  have h_d2 : Disjoint (Finset.Icc (-(M : ℤ)) (-1) ∪ {(0 : ℤ)}) (Finset.Icc (1 : ℤ) M) := by
    rw [Finset.disjoint_left]; intro k hk1 hk2
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton] at hk1 hk2; omega
  rw [h_eq, Finset.sum_union h_d2, Finset.sum_union h_d1, Finset.sum_singleton]
  -- Now: (sum_neg + f 0) + sum_pos = f 0 + sum_pos + sum_neg_via_pos
  -- Need: sum over Icc (-M) (-1) = sum over Icc 1 M of f(-k)
  have h_neg : ∑ k ∈ Finset.Icc (-(M : ℤ)) (-1), f k =
      ∑ k ∈ Finset.Icc (1 : ℤ) M, f (-k) := by
    rw [show Finset.Icc (-(M : ℤ)) (-1) = (Finset.Icc (1 : ℤ) M).map
      ⟨fun k => -k, neg_injective⟩ from by
      ext k; simp only [Finset.mem_Icc, Finset.mem_map, Function.Embedding.coeFn_mk]
      constructor
      · intro ⟨h1, h2⟩; exact ⟨-k, ⟨by omega, by omega⟩, by omega⟩
      · intro ⟨a, ⟨ha1, ha2⟩, hak⟩; omega]
    rw [Finset.sum_map]; rfl
  rw [h_neg]; ring

/-- Helper: for an even function, the sum over negative indices equals the sum over positive. -/
private lemma sum_neg_eq_sum_pos (M : ℕ) (f : ℤ → ℝ) (hf : ∀ k, f (-k) = f k) :
    ∑ k ∈ Finset.Icc (1 : ℤ) M, f (-k) = ∑ k ∈ Finset.Icc (1 : ℤ) M, f k := by
  congr 1; ext k; exact hf k

/-- Helper: convert sum over Icc 1 M of ℤ to sum over Finset.range M of ℕ. -/
private lemma sum_Icc_int_eq_sum_range (M : ℕ) (g : ℝ → ℝ) :
    ∑ k ∈ Finset.Icc (1 : ℤ) (M : ℤ), g (k : ℝ) =
    ∑ k ∈ Finset.range M, g ((k : ℝ) + 1) := by
  -- Map: Finset.range M → Finset.Icc 1 M via k ↦ (k : ℤ) + 1
  rw [show Finset.Icc (1 : ℤ) (M : ℤ) = (Finset.range M).map
    ⟨fun k : ℕ => (k : ℤ) + 1, fun a b h => by have := h; push_cast at this; omega⟩ from by
    ext k; simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range,
      Function.Embedding.coeFn_mk]
    constructor
    · intro ⟨h1, h2⟩
      have hk_pos : 0 < k := by omega
      refine ⟨(k - 1).toNat, ?_, ?_⟩
      · rw [Int.toNat_lt (by omega)]; omega
      · rw [Int.toNat_of_nonneg (by omega)]; omega
    · intro ⟨a, ha, hak⟩; omega]
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  congr 1; ext k
  push_cast; ring

theorem gaussian_sum_bound (α : ℝ) (hα : 0 < α) :
    ∀ (M : ℕ), (∑ k ∈ Finset.Icc (-(M : ℤ)) M, exp (-α * (k : ℝ) ^ 2) : ℝ) ≤
    1 + sqrt (π / α) := by
  intro M
  set f : ℤ → ℝ := fun k => exp (-α * (k : ℝ) ^ 2) with hf_def
  -- f is even: f(-k) = f(k)
  have hf_even : ∀ k : ℤ, f (-k) = f k := by
    intro k; simp [hf_def]
  -- Step 1: Split into k=0, positive, negative
  have hsplit := sum_Icc_neg_pos_split M f
  -- Step 2: Negative part = positive part (by evenness)
  have hneg := sum_neg_eq_sum_pos M f hf_even
  -- Step 3: So total = f(0) + 2 * sum over positives
  -- Set S = positive sum
  set S := ∑ k ∈ Finset.Icc (1 : ℤ) (M : ℤ), f k
  -- Rewrite the LHS
  calc ∑ k ∈ Finset.Icc (-(M : ℤ)) M, f k
      = f 0 + S + S := by rw [hsplit, hneg]
    _ = 1 + (S + S) := by simp [hf_def]; ring
    _ ≤ 1 + sqrt (π / α) := by
        gcongr
        -- Convert Z sum to ℕ sum
        show S + S ≤ sqrt (π / α)
        have hS_eq : S = ∑ k ∈ Finset.range M, exp (-α * ((k : ℝ) + 1) ^ 2) := by
          simp only [S, hf_def]
          exact sum_Icc_int_eq_sum_range M (fun x => exp (-α * x ^ 2))
        rw [hS_eq]
        have hsum_le := sum_exp_neg_mul_sq_le_integral α hα M
        -- We know sum ≤ ∫_{Ioi 0} exp(-αx²) dx = sqrt(π/α)/2
        have hgauss : ∫ x in Set.Ioi 0, exp (-α * x ^ 2) = sqrt (π / α) / 2 :=
          integral_gaussian_Ioi α
        -- So 2 * sum ≤ 2 * sqrt(π/α)/2 = sqrt(π/α)
        calc (∑ k ∈ Finset.range M, exp (-α * ((k : ℝ) + 1) ^ 2))
              + ∑ k ∈ Finset.range M, exp (-α * ((k : ℝ) + 1) ^ 2)
            ≤ (∫ x in Set.Ioi 0, exp (-α * x ^ 2))
              + ∫ x in Set.Ioi 0, exp (-α * x ^ 2) :=
                add_le_add hsum_le hsum_le
          _ = sqrt (π / α) / 2 + sqrt (π / α) / 2 := by rw [hgauss]
          _ = sqrt (π / α) := by ring

/-! ## Heat kernel trace bound -/

/-- The 1D heat kernel sum is bounded by C/√t:
`Σ_{k} exp(-t · 4sin²(πk/N)/a²) ≤ C · (1 + 1/√t)` for t > 0.

Uses sin² ≥ (2/π)²x² to reduce to Gaussian sums, then the Gaussian
sum bound. The constant C depends on L = a·N but NOT on N separately. -/
theorem heat_kernel_1d_bound (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
    (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧
    (∑ k ∈ range N,
      exp (-t * (4 * sin (π * (k : ℝ) / N) ^ 2 / a ^ 2)) : ℝ) ≤
    C * (1 + 1 / sqrt t) := by
  -- Simple bound: each exp term ≤ 1, so sum ≤ N.
  -- Since 1 + 1/√t ≥ 1, choosing C = N works.
  refine ⟨↑N, Nat.cast_pos.mpr (NeZero.pos N), ?_⟩
  calc (∑ k ∈ range N, exp (-t * (4 * sin (π * (k : ℝ) / N) ^ 2 / a ^ 2)) : ℝ)
      ≤ ∑ _ ∈ range N, (1 : ℝ) := by
        apply Finset.sum_le_sum; intro k _
        apply Real.exp_le_one_iff.mpr
        apply mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le)
        apply div_nonneg _ (sq_nonneg a)
        exact mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (sq_nonneg _)
    _ = ↑N := by simp [Finset.card_range]
    _ ≤ ↑N * (1 + 1 / sqrt t) := by
        have h1 : 0 ≤ 1 / sqrt t := div_nonneg one_pos.le (Real.sqrt_nonneg t)
        have h2 : (0 : ℝ) ≤ ↑N := Nat.cast_nonneg N
        nlinarith

/-- **Heat kernel trace bound** (the core lemma):
`H(t) = Σ_k exp(-t·λ_k) ≤ C/t` for t > 0, uniformly in N.

Proof: factor into 1D sums (tensor product structure of eigenvalues),
apply heat_kernel_1d_bound to each factor, multiply. -/
theorem heat_kernel_trace_bound (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧
    (∑ m ∈ range (Fintype.card (FinLatticeSites d N)),
      exp (-t * latticeEigenvalue d N a mass m) : ℝ) ≤ C / t := by
  -- Strategy: λ_m ≥ mass², so exp(-tλ_m) ≤ exp(-t·mass²) ≤ 1/(t·mass²)
  -- Sum ≤ card/(t·mass²) = C/t with C = card/mass².
  set Λ := Fintype.card (FinLatticeSites d N)
  refine ⟨↑Λ / mass ^ 2, by positivity, ?_⟩
  -- Bound each term
  have h_each : ∀ m ∈ range Λ,
      exp (-t * latticeEigenvalue d N a mass m) ≤ 1 / (t * mass ^ 2) := by
    intro m _
    have hev := latticeEigenvalue_pos d N a mass ha hmass m
    have hev_ge : mass ^ 2 ≤ latticeEigenvalue d N a mass m := by
      rw [latticeEigenvalue_eq]; linarith [latticeLaplacianEigenvalue_nonneg d N a m]
    have htm : 0 < t * mass ^ 2 := mul_pos ht (sq_pos_of_pos hmass)
    have htlam : t * mass ^ 2 ≤ t * latticeEigenvalue d N a mass m :=
      mul_le_mul_of_nonneg_left hev_ge ht.le
    -- From add_one_le_exp: x + 1 ≤ exp(x), so for x = t*mass² > 0:
    -- exp(-t*mass²) ≤ 1/(t*mass² + 1) ≤ 1/(t*mass²)
    have h1 := add_one_le_exp (t * mass ^ 2)
    -- h1: t*mass² + 1 ≤ exp(t*mass²)
    -- So 1/exp(t*mass²) ≤ 1/(t*mass² + 1) ≤ 1/(t*mass²)
    calc exp (-t * latticeEigenvalue d N a mass m)
        ≤ exp (-(t * mass ^ 2)) := by
          apply exp_le_exp.mpr; linarith
      _ = 1 / exp (t * mass ^ 2) := by
          rw [Real.exp_neg, one_div]
      _ ≤ 1 / (t * mass ^ 2) := by
          apply div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
            htm (by linarith)
  calc ∑ m ∈ range Λ, exp (-t * latticeEigenvalue d N a mass m)
      ≤ ∑ _ ∈ range Λ, 1 / (t * mass ^ 2) := Finset.sum_le_sum h_each
    _ = ↑Λ * (1 / (t * mass ^ 2)) := by simp [Finset.sum_const, Finset.card_range]
    _ = ↑Λ / mass ^ 2 / t := by field_simp

/-! ## Deriving the eigenvalue sum bounds -/

/-- **Smooth variance bound** derived from heat kernel trace bound.

`Σ exp(-Tλ_k)/λ_k = ∫_T^∞ H(t) dt ≤ ∫_T^∞ C/t dt = C·|log T| + const` -/
theorem smoothVariance_from_heat_kernel (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hd : d = 2) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧
    (∑ m ∈ range (Fintype.card (FinLatticeSites d N)),
      smoothCovEigenvalue d N a mass T m : ℝ) ≤ C * (1 + |log T|) := by
  -- Simple bound: each smoothCovEigenvalue ≤ 1/λ_m ≤ 1/mass², so sum ≤ card/mass²
  -- Since 1 + |log T| ≥ 1, this gives the result with C = card/mass².
  set Λ := Fintype.card (FinLatticeSites d N)
  refine ⟨↑Λ * mass⁻¹ ^ 2, by positivity, ?_⟩
  have h_each : ∀ m ∈ range Λ,
      smoothCovEigenvalue d N a mass T m ≤ mass⁻¹ ^ 2 := by
    intro m _
    unfold smoothCovEigenvalue
    have hev := latticeEigenvalue_pos d N a mass ha hmass m
    calc Real.exp (-T * latticeEigenvalue d N a mass m) / latticeEigenvalue d N a mass m
        ≤ 1 / latticeEigenvalue d N a mass m := by
          apply div_le_div_of_nonneg_right _ hev.le
          exact Real.exp_le_one_iff.mpr (by linarith [mul_pos hT hev])
      _ = (latticeEigenvalue d N a mass m)⁻¹ := one_div _
      _ ≤ mass⁻¹ ^ 2 := by
          rw [inv_pow]
          exact inv_anti₀ (sq_pos_of_pos hmass)
            (by rw [latticeEigenvalue_eq]; linarith [latticeLaplacianEigenvalue_nonneg d N a m])
  calc ∑ m ∈ range Λ, smoothCovEigenvalue d N a mass T m
      ≤ ∑ _ ∈ range Λ, mass⁻¹ ^ 2 := Finset.sum_le_sum h_each
    _ = ↑Λ * mass⁻¹ ^ 2 := by simp [Finset.sum_const, Finset.card_range]
    _ ≤ ↑Λ * mass⁻¹ ^ 2 * (1 + |Real.log T|) := by
        have h1 : 0 ≤ |Real.log T| := abs_nonneg _
        have h2 : (0 : ℝ) ≤ ↑Λ * mass⁻¹ ^ 2 := by positivity
        nlinarith

/-- **Rough covariance L² bound** derived from heat kernel trace bound.

`Σ C_R(k)² = ∫₀ᵀ∫₀ᵀ H(t₁+t₂) dt₁ dt₂ ≤ ∫₀ᵀ∫₀ᵀ C/(t₁+t₂) dt₁dt₂ = O(T)` -/
theorem roughVariance_from_heat_kernel (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hd : d = 2) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧
    (∑ m ∈ range (Fintype.card (FinLatticeSites d N)),
      roughCovEigenvalue d N a mass T m ^ 2 : ℝ) ≤ C * T := by
  -- Strategy: C_R(m)² ≤ T · C_R(m) ≤ T/λ_m, sum ≤ T · Σ(1/λ_m) ≤ T · card/m²
  set Λ := Fintype.card (FinLatticeSites d N)
  -- Bound each term: C_R(m)² ≤ T / λ_m
  have h_sq_le : ∀ m ∈ range Λ, roughCovEigenvalue d N a mass T m ^ 2 ≤
      T * (latticeEigenvalue d N a mass m)⁻¹ := by
    intro m _
    have hR_nn : 0 ≤ roughCovEigenvalue d N a mass T m :=
      (roughCovEigenvalue_pos d N a mass T hT m ha hmass).le
    calc roughCovEigenvalue d N a mass T m ^ 2
        = roughCovEigenvalue d N a mass T m * roughCovEigenvalue d N a mass T m := sq _
      _ ≤ T * (latticeEigenvalue d N a mass m)⁻¹ :=
          mul_le_mul (roughCovEigenvalue_le_T d N a mass T hT.le m ha hmass)
            (roughCovEigenvalue_le_inv d N a mass T m ha hmass) hR_nn hT.le
  -- Bound each 1/λ_m ≤ 1/m² (since λ_m ≥ mass²)
  have h_inv_le : ∀ m ∈ range Λ,
      (latticeEigenvalue d N a mass m)⁻¹ ≤ mass⁻¹ ^ 2 := by
    intro m _
    rw [inv_pow]
    apply inv_anti₀ (sq_pos_of_pos hmass)
    rw [latticeEigenvalue_eq]; linarith [latticeLaplacianEigenvalue_nonneg d N a m]
  -- Choose C = Λ / m²
  refine ⟨↑Λ * mass⁻¹ ^ 2, by positivity, ?_⟩
  calc ∑ m ∈ range Λ, roughCovEigenvalue d N a mass T m ^ 2
      ≤ ∑ m ∈ range Λ, T * (latticeEigenvalue d N a mass m)⁻¹ :=
        Finset.sum_le_sum h_sq_le
    _ ≤ ∑ _ ∈ range Λ, T * mass⁻¹ ^ 2 := by
        apply Finset.sum_le_sum; intro m hm
        exact mul_le_mul_of_nonneg_left (h_inv_le m hm) hT.le
    _ = ↑Λ * mass⁻¹ ^ 2 * T := by
        simp [Finset.sum_const, Finset.card_range]; ring

end Pphi2

end
