/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas

# Covariance Convergence: Proof of Torus → Cylinder Limit

Proves that the torus Green's function of embedded cylinder test functions
converges to the physically normalized cylinder Green function as the temporal
period Lt → ∞, and that the IR limit measure has the correct covariance.

## Main results

- `asymTorusGreen_tendsto_physicalCylinderGreen` — covariance convergence
  for all test functions, extending from finite-rank via seminorm approximation
- `cylinderIRLimit_covariance_eq` — the IR limit measure has the correct
  physically normalized cylinder covariance (characteristic function method)

## References

- Glimm-Jaffe, *Quantum Physics*, §19.1 (infinite volume limit)
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII
-/

import Pphi2.IRLimit.CovarianceConvergence

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory Filter ProbabilityTheory Complex PeriodicResolvent1D

variable (Ls : ℝ) [hLs : Fact (0 < Ls)]

/-! ## Exponential convergence rate

The mass gap `m > 0` gives exponential convergence of the periodic Green's
function to the non-periodic one. The scalar 1D estimates live in
`PeriodicResolvent1D` (`periodicKernel`, `freeKernel`, and lemmas such as
`PeriodicResolvent1D.abs_sub_free_le`).

The `Pphi2.periodicResolvent_*` theorems below restate the same bounds in
expanded form for compatibility with the mixed spectral representation
`cosh(ω(Lt/2-|t|))/(2ω sinh(ωLt/2))` used in the torus Green's function. -/

/-- The 1D periodic resolvent converges exponentially to the free resolvent.

For ω > 0:
  `|cosh(ω(Lt/2 - |t|))/(2ω sinh(ωLt/2)) - e^{-ω|t|}/(2ω)|
    ≤ e^{-ω(Lt - |t|)} / (ω(1 - e^{-ω Lt}))`

See `PeriodicResolvent1D.abs_sub_free_le`. -/
theorem periodicResolvent_convergence_rate
    (ω : ℝ) (hω : 0 < ω)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) :
    |Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
     Real.exp (-ω * |t|) / (2 * ω)| ≤
    Real.exp (-ω * (Lt - |t|)) /
      (ω * (1 - Real.exp (-ω * Lt))) := by
  simpa [periodicKernel, freeKernel] using abs_sub_free_le ω hω t Lt hLt

/-- Uniform half-period decay; see `PeriodicResolvent1D.abs_sub_free_le_on_halfPeriodStrip`. -/
theorem periodicResolvent_convergence_rate_uniform
    (ω : ℝ) (hω : 0 < ω)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) (ht : |t| < Lt / 2) :
    |Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
      Real.exp (-ω * |t|) / (2 * ω)| ≤
    Real.exp (-ω * Lt / 2) /
      (ω * (1 - Real.exp (-ω * Lt))) := by
  simpa [periodicKernel, freeKernel] using
    abs_sub_free_le_on_halfPeriodStrip ω hω t Lt hLt ht

/-- Uniform mass-gap control; see `PeriodicResolvent1D.abs_sub_free_le_uniform_mass_gap`. -/
theorem periodicResolvent_convergence_rate_uniform_mass_gap
    (ω mass : ℝ) (hmass : 0 < mass) (hω : mass ≤ ω)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) (ht : |t| < Lt / 2) :
    |Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
      Real.exp (-ω * |t|) / (2 * ω)| ≤
    Real.exp (-mass * Lt / 2) /
      (mass * (1 - Real.exp (-mass * Lt))) := by
  simpa [periodicKernel, freeKernel] using
    abs_sub_free_le_uniform_mass_gap ω mass hmass hω t Lt hLt ht

omit hLs in
/-- Specialization of the uniform mass-gap bound to cylinder frequencies
`ω_n = resolventFreq Ls mass n`. -/
theorem periodicResolvent_resolventFreq_convergence_rate_uniform
    (mass : ℝ) (hmass : 0 < mass) (n : ℕ)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) (ht : |t| < Lt / 2) :
    |Real.cosh (resolventFreq Ls mass n * (Lt / 2 - |t|)) /
        (2 * resolventFreq Ls mass n * Real.sinh (resolventFreq Ls mass n * Lt / 2)) -
      Real.exp (-resolventFreq Ls mass n * |t|) / (2 * resolventFreq Ls mass n)| ≤
    Real.exp (-mass * Lt / 2) /
      (mass * (1 - Real.exp (-mass * Lt))) := by
  simpa [periodicKernel, freeKernel] using
    abs_sub_free_le_uniform_mass_gap
      (ω := resolventFreq Ls mass n) (mass := mass) hmass
      (resolventFreq_mass_le Ls mass hmass.le n) t Lt hLt ht

/-- For fixed `ω > 0` and `t`, the periodic 1D resolvent kernel converges to the free resolvent
kernel as `Lt → ∞`. See `PeriodicResolvent1D.tendsto_periodicKernel_freeKernel`. -/
theorem periodicResolvent_tendsto_free
    (ω : ℝ) (hω : 0 < ω) (t : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto
      (fun n =>
        Real.cosh (ω * (Lt n / 2 - |t|)) /
          (2 * ω * Real.sinh (ω * Lt n / 2)))
      atTop (nhds (Real.exp (-ω * |t|) / (2 * ω))) := by
  simpa [periodicKernel, freeKernel] using
    tendsto_periodicKernel_freeKernel ω hω t Lt hLt hLt_tend

/-- Uniform-on-compact convergence of the periodic resolvent to the free resolvent, with
the compact-window control depending only on a mass gap `mass ≤ ω`. -/
theorem periodicResolvent_tendsto_free_uniformOn_compact_mass_gap
    (ω mass : ℝ) (hmass : 0 < mass) (hω : mass ≤ ω)
    (R : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn
      (fun n t =>
        Real.cosh (ω * (Lt n / 2 - |t|)) /
          (2 * ω * Real.sinh (ω * Lt n / 2)))
      (fun t => Real.exp (-ω * |t|) / (2 * ω))
      atTop (Set.Icc (-R) R) := by
  simpa [periodicKernel, freeKernel] using
    tendstoUniformlyOn_periodicKernel_freeKernel_compact_of_mass_gap
      ω mass hmass hω R Lt hLt hLt_tend

/-- Fixed-frequency compact-window uniform convergence. -/
theorem periodicResolvent_tendsto_free_uniformOn_compact
    (ω : ℝ) (hω : 0 < ω)
    (R : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn
      (fun n t =>
        Real.cosh (ω * (Lt n / 2 - |t|)) /
          (2 * ω * Real.sinh (ω * Lt n / 2)))
      (fun t => Real.exp (-ω * |t|) / (2 * ω))
      atTop (Set.Icc (-R) R) := by
  simpa [periodicKernel, freeKernel] using
    tendstoUniformlyOn_periodicKernel_freeKernel_compact
      ω hω R Lt hLt hLt_tend

omit hLs in
/-- Compact-window specialization of `periodicResolvent_tendsto_free_uniformOn_compact_mass_gap`
to the cylinder frequencies `ω_n = resolventFreq Ls mass n`. -/
theorem periodicResolvent_resolventFreq_tendsto_free_uniformOn_compact
    (mass : ℝ) (hmass : 0 < mass) (n : ℕ)
    (R : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ k, Fact (0 < Lt k))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn
      (fun k t =>
        Real.cosh (resolventFreq Ls mass n * (Lt k / 2 - |t|)) /
          (2 * resolventFreq Ls mass n * Real.sinh (resolventFreq Ls mass n * Lt k / 2)))
      (fun t => Real.exp (-resolventFreq Ls mass n * |t|) / (2 * resolventFreq Ls mass n))
      atTop (Set.Icc (-R) R) := by
  simpa [periodicKernel, freeKernel] using
    tendstoUniformlyOn_periodicKernel_freeKernel_compact_of_mass_gap
      (ω := resolventFreq Ls mass n) (mass := mass) hmass
      (resolventFreq_mass_le Ls mass hmass.le n) R Lt hLt hLt_tend

/-- Two-variable compact-box version of
`periodicResolvent_tendsto_free_uniformOn_compact_mass_gap`, pulled back along
`(t, s) ↦ t - s`. -/
theorem periodicResolvent_tendsto_free_uniformOn_compactDiffBox_mass_gap
    (ω mass : ℝ) (hmass : 0 < mass) (hω : mass ≤ ω)
    (R : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ k, Fact (0 < Lt k))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn
      (fun k (p : ℝ × ℝ) =>
        Real.cosh (ω * (Lt k / 2 - |p.1 - p.2|)) /
          (2 * ω * Real.sinh (ω * Lt k / 2)))
      (fun p => Real.exp (-ω * |p.1 - p.2|) / (2 * ω))
      atTop (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) := by
  simpa [periodicKernel, freeKernel] using
    tendstoUniformlyOn_periodicKernel_freeKernel_compactDiffBox_of_mass_gap
      ω mass hmass hω R Lt hLt hLt_tend

omit hLs in
/-- Cylinder-frequency specialization of
`periodicResolvent_tendsto_free_uniformOn_compactDiffBox_mass_gap`. -/
theorem periodicResolvent_resolventFreq_tendsto_free_uniformOn_compactDiffBox
    (mass : ℝ) (hmass : 0 < mass) (n : ℕ)
    (R : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ k, Fact (0 < Lt k))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn
      (fun k (p : ℝ × ℝ) =>
        Real.cosh (resolventFreq Ls mass n * (Lt k / 2 - |p.1 - p.2|)) /
          (2 * resolventFreq Ls mass n * Real.sinh (resolventFreq Ls mass n * Lt k / 2)))
      (fun p =>
        Real.exp (-resolventFreq Ls mass n * |p.1 - p.2|) / (2 * resolventFreq Ls mass n))
      atTop (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) := by
  simpa [periodicKernel, freeKernel] using
    tendstoUniformlyOn_periodicKernel_freeKernel_compactDiffBox_of_mass_gap
      (ω := resolventFreq Ls mass n) (mass := mass) hmass
      (resolventFreq_mass_le Ls mass hmass.le n) R Lt hLt hLt_tend

omit hLs in
/-- Compact-support pure-temporal convergence on the support box.

If `h₁, h₂ : 𝓢(ℝ)` vanish outside `[-T, T]`, then on the box `[-T, T]²` their periodizations are
eventually equal to the original functions, so the only remaining convergence is the periodic/free
kernel convergence in the difference variable. This is the temporal core of the pure-tensor
torus-to-cylinder Green convergence argument. -/
theorem periodizedSchwartz_mul_periodicKernel_tendsto_freeKernel_uniformOn_compactDiffBox
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ) (hT : 0 < T)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0)
    (ω mass : ℝ) (hmass : 0 < mass) (hω : mass ≤ ω)
    (Lt : ℕ → ℝ) (hLt : ∀ k, Fact (0 < Lt k))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn
      (fun k (p : ℝ × ℝ) =>
        ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
          (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
          periodicKernel ω (Lt k) (p.1 - p.2))
      (fun p => (h₁ p.1 * h₂ p.2) * freeKernel ω (p.1 - p.2))
      atTop (Set.Icc (-T) T ×ˢ Set.Icc (-T) T) := by
  let K : Set (ℝ × ℝ) := Set.Icc (-T) T ×ˢ Set.Icc (-T) T
  have hK_compact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hper₁ :
      TendstoUniformlyOn
        (fun k t => (@periodizeCLM (Lt k) (hLt k) h₁).toFun t)
        h₁ atTop (Set.Icc (-T) T) :=
    periodizeCLM_tendsto_uniformlyOn_symmetricCompact
      h₁ T hT hsupp₁ Lt hLt hLt_tend
  have hper₂ :
      TendstoUniformlyOn
        (fun k t => (@periodizeCLM (Lt k) (hLt k) h₂).toFun t)
        h₂ atTop (Set.Icc (-T) T) :=
    periodizeCLM_tendsto_uniformlyOn_symmetricCompact
      h₂ T hT hsupp₂ Lt hLt hLt_tend
  have hper₁_box :
      TendstoUniformlyOn
        (fun k (p : ℝ × ℝ) => (@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1)
        (fun p => h₁ p.1) atTop K := by
    refine (hper₁.comp Prod.fst).mono ?_
    intro p hp
    exact hp.1
  have hper₂_box :
      TendstoUniformlyOn
        (fun k (p : ℝ × ℝ) => (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2)
        (fun p => h₂ p.2) atTop K := by
    refine (hper₂.comp Prod.snd).mono ?_
    intro p hp
    exact hp.2
  have hkernel :
      TendstoUniformlyOn
        (fun k (p : ℝ × ℝ) => periodicKernel ω (Lt k) (p.1 - p.2))
        (fun p => freeKernel ω (p.1 - p.2))
        atTop K :=
    tendstoUniformlyOn_periodicKernel_freeKernel_compactDiffBox_of_mass_gap
      ω mass hmass hω T Lt hLt hLt_tend
  have hper₁_cont : ContinuousOn (fun p : ℝ × ℝ => h₁ p.1) K := by
    exact (h₁.continuous.comp continuous_fst).continuousOn
  have hper₂_cont : ContinuousOn (fun p : ℝ × ℝ => h₂ p.2) K := by
    exact (h₂.continuous.comp continuous_snd).continuousOn
  have hkernel_cont : ContinuousOn (fun p : ℝ × ℝ => freeKernel ω (p.1 - p.2)) K := by
    exact ((continuous_freeKernel ω).comp (continuous_fst.sub continuous_snd)).continuousOn
  have hprod_loc :
      TendstoLocallyUniformlyOn
        (fun k (p : ℝ × ℝ) =>
          (@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
            (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2)
        (fun p => h₁ p.1 * h₂ p.2)
        atTop K := by
    exact hper₁_box.tendstoLocallyUniformlyOn.mul₀
      hper₂_box.tendstoLocallyUniformlyOn hper₁_cont hper₂_cont
  have hfull_loc :
      TendstoLocallyUniformlyOn
        (fun k (p : ℝ × ℝ) =>
          ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
            (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
            periodicKernel ω (Lt k) (p.1 - p.2))
        (fun p => (h₁ p.1 * h₂ p.2) * freeKernel ω (p.1 - p.2))
        atTop K := by
    exact hprod_loc.mul₀ hkernel.tendstoLocallyUniformlyOn
      (hper₁_cont.mul hper₂_cont) hkernel_cont
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK_compact).mp hfull_loc

omit hLs in
/-- Integrating the compact-support pure-temporal convergence over the support box yields
convergence of the corresponding temporal bilinear forms. This is the dominated-convergence
step in the pure-tensor torus-to-cylinder Green comparison. -/
theorem periodizedSchwartz_mul_periodicKernel_tendsto_freeKernel_integralOn_compactDiffBox
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ) (hT : 0 < T)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0)
    (ω mass : ℝ) (hmass : 0 < mass) (hω : mass ≤ ω)
    (Lt : ℕ → ℝ) (hLt : ∀ k, Fact (0 < Lt k))
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto
      (fun k =>
        ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
            (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
            periodicKernel ω (Lt k) (p.1 - p.2) ∂volume)
      atTop
      (nhds (∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
        (h₁ p.1 * h₂ p.2) * freeKernel ω (p.1 - p.2) ∂volume)) := by
  let K : Set (ℝ × ℝ) := Set.Icc (-T) T ×ˢ Set.Icc (-T) T
  let F : ℕ → ℝ × ℝ → ℝ := fun k p =>
    ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
      (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
      periodicKernel ω (Lt k) (p.1 - p.2)
  let F_lim : ℝ × ℝ → ℝ := fun p =>
    (h₁ p.1 * h₂ p.2) * freeKernel ω (p.1 - p.2)
  have hunif :
      TendstoUniformlyOn F F_lim atTop K := by
    simpa [F, F_lim, K] using
      periodizedSchwartz_mul_periodicKernel_tendsto_freeKernel_uniformOn_compactDiffBox
        (h₁ := h₁) (h₂ := h₂) T hT hsupp₁ hsupp₂ ω mass hmass hω Lt hLt hLt_tend
  have hK_compact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  haveI : IsFiniteMeasure (volume.restrict K) := by
    refine ⟨?_⟩
    simpa [Measure.restrict_apply, hK_meas, K] using hK_compact.measure_lt_top (μ := volume)
  have hF_cont : ∀ k, Continuous (F k) := by
    intro k
    have hper₁ :
        Continuous (fun p : ℝ × ℝ => (@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1) :=
      ((@periodizeCLM (Lt k) (hLt k) h₁).continuous.comp continuous_fst)
    have hper₂ :
        Continuous (fun p : ℝ × ℝ => (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) :=
      ((@periodizeCLM (Lt k) (hLt k) h₂).continuous.comp continuous_snd)
    have hkernel :
        Continuous (fun p : ℝ × ℝ => periodicKernel ω (Lt k) (p.1 - p.2)) :=
      (continuous_periodicKernel ω (Lt k)).comp (continuous_fst.sub continuous_snd)
    simpa [F] using (hper₁.mul hper₂).mul hkernel
  have hF_meas :
      ∀ᶠ k in atTop, AEStronglyMeasurable (F k) (volume.restrict K) := by
    exact Eventually.of_forall fun k =>
      (hF_cont k).stronglyMeasurable.aestronglyMeasurable
  have hF_lim_cont : ContinuousOn F_lim K := by
    have hper₁_cont : ContinuousOn (fun p : ℝ × ℝ => h₁ p.1) K := by
      exact (h₁.continuous.comp continuous_fst).continuousOn
    have hper₂_cont : ContinuousOn (fun p : ℝ × ℝ => h₂ p.2) K := by
      exact (h₂.continuous.comp continuous_snd).continuousOn
    have hkernel_cont : ContinuousOn (fun p : ℝ × ℝ => freeKernel ω (p.1 - p.2)) K := by
      exact ((continuous_freeKernel ω).comp (continuous_fst.sub continuous_snd)).continuousOn
    simpa [F_lim] using (hper₁_cont.mul hper₂_cont).mul hkernel_cont
  obtain ⟨C0, hC0_image⟩ : ∃ C, ∀ y ∈ F_lim '' K, ‖y‖ ≤ C :=
    Bornology.IsBounded.exists_norm_le (hK_compact.image_of_continuousOn hF_lim_cont).isBounded
  have hC0 : ∀ p ∈ K, ‖F_lim p‖ ≤ C0 := by
    intro p hp
    exact hC0_image _ (Set.mem_image_of_mem F_lim hp)
  have h_bound :
      ∃ C, ∀ᶠ k in atTop, (∀ᵐ p ∂(volume.restrict K), ‖F k p‖ ≤ C) := by
    refine ⟨C0 + 1, ?_⟩
    have hsmall : ∀ᶠ k in atTop, ∀ p ∈ K, dist (F k p) (F_lim p) < 1 := by
      filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hunif) 1 zero_lt_one] with k hk p hp
      simpa [dist_comm] using hk p hp
    filter_upwards [hsmall] with k hk
    refine (ae_restrict_mem hK_meas).mono ?_
    intro p hp
    have hk' := hk p hp
    have hdist : ‖F k p - F_lim p‖ < 1 := by
      simpa [Real.dist_eq, Real.norm_eq_abs] using hk'
    have hC0' := hC0 p hp
    calc
      ‖F k p‖ = ‖(F k p - F_lim p) + F_lim p‖ := by
        congr 1
        ring
      _ ≤ ‖F k p - F_lim p‖ + ‖F_lim p‖ := norm_add_le _ _
      _ ≤ C0 + 1 := by
        linarith
  have h_pointwise : ∀ p ∈ K, Tendsto (fun k => F k p) atTop (nhds (F_lim p)) := by
    intro p hp
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hunif ε hε)] with k hk
    simpa [dist_comm] using hk p hp
  have h_lim : ∀ᵐ p ∂(volume.restrict K), Tendsto (fun k => F k p) atTop (nhds (F_lim p)) := by
    exact (ae_restrict_mem hK_meas).mono fun p hp => h_pointwise p hp
  have h_tend :
      Tendsto (fun k => ∫ p, F k p ∂(volume.restrict K)) atTop
        (nhds (∫ p, F_lim p ∂(volume.restrict K))) := by
    exact tendsto_integral_filter_of_norm_le_const
      (μ := volume.restrict K) hF_meas h_bound h_lim
  simpa [K, F, F_lim] using h_tend

omit hLs in
/-- The compact-support temporal convergence theorem specialized to the cylinder frequencies
`ω_n = resolventFreq Ls mass n`, written in expanded resolvent form. -/
theorem periodizedSchwartz_mul_resolventFreq_tendsto_free_uniformOn_compactDiffBox
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ) (hT : 0 < T)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0)
    (mass : ℝ) (hmass : 0 < mass) (n : ℕ)
    (Lt : ℕ → ℝ) (hLt : ∀ k, Fact (0 < Lt k))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn
      (fun k (p : ℝ × ℝ) =>
        ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
          (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
          (Real.cosh (resolventFreq Ls mass n * (Lt k / 2 - |p.1 - p.2|)) /
            (2 * resolventFreq Ls mass n * Real.sinh (resolventFreq Ls mass n * Lt k / 2))))
      (fun p =>
        (h₁ p.1 * h₂ p.2) *
          (Real.exp (-resolventFreq Ls mass n * |p.1 - p.2|) /
            (2 * resolventFreq Ls mass n)))
      atTop (Set.Icc (-T) T ×ˢ Set.Icc (-T) T) := by
  simpa [periodicKernel, freeKernel] using
    periodizedSchwartz_mul_periodicKernel_tendsto_freeKernel_uniformOn_compactDiffBox
      (h₁ := h₁) (h₂ := h₂) T hT hsupp₁ hsupp₂
      (ω := resolventFreq Ls mass n) (mass := mass) hmass
      (resolventFreq_mass_le Ls mass hmass.le n) Lt hLt hLt_tend

omit hLs in
/-- Integrating the cylinder-frequency specialization over the support box yields convergence of the
corresponding temporal bilinear forms. -/
theorem periodizedSchwartz_mul_resolventFreq_tendsto_free_integralOn_compactDiffBox
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ) (hT : 0 < T)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0)
    (mass : ℝ) (hmass : 0 < mass) (n : ℕ)
    (Lt : ℕ → ℝ) (hLt : ∀ k, Fact (0 < Lt k))
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto
      (fun k =>
        ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
            (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
            (Real.cosh (resolventFreq Ls mass n * (Lt k / 2 - |p.1 - p.2|)) /
              (2 * resolventFreq Ls mass n * Real.sinh (resolventFreq Ls mass n * Lt k / 2)))
          ∂volume)
      atTop
      (nhds (∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
        (h₁ p.1 * h₂ p.2) *
          (Real.exp (-resolventFreq Ls mass n * |p.1 - p.2|) /
            (2 * resolventFreq Ls mass n)) ∂volume)) := by
  simpa [periodicKernel, freeKernel] using
    periodizedSchwartz_mul_periodicKernel_tendsto_freeKernel_integralOn_compactDiffBox
      (h₁ := h₁) (h₂ := h₂) T hT hsupp₁ hsupp₂
      (ω := resolventFreq Ls mass n) (mass := mass) hmass
      (resolventFreq_mass_le Ls mass hmass.le n) Lt hLt hLt_tend

private theorem integral_exp_mul_cos
    (σ α a b : ℝ) (hden : σ ^ 2 + α ^ 2 ≠ 0) :
    ∫ x in a..b, Real.exp (σ * x) * Real.cos (α * x) =
      (Real.exp (σ * b) * (σ * Real.cos (α * b) + α * Real.sin (α * b)) -
        Real.exp (σ * a) * (σ * Real.cos (α * a) + α * Real.sin (α * a))) /
        (σ ^ 2 + α ^ 2) := by
  let F : ℝ → ℝ := fun x =>
    (Real.exp (σ * x) * (σ * Real.cos (α * x) + α * Real.sin (α * x))) /
      (σ ^ 2 + α ^ 2)
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt F (Real.exp (σ * x) * Real.cos (α * x)) x := by
    intro x hx
    have hExp : HasDerivAt (fun y : ℝ => Real.exp (σ * y)) (σ * Real.exp (σ * x)) x := by
      simpa [mul_comm] using
        (Real.hasDerivAt_exp (σ * x)).comp x ((hasDerivAt_id x).const_mul σ)
    have hCos : HasDerivAt (fun y : ℝ => σ * Real.cos (α * y))
        (σ * (-α * Real.sin (α * x))) x := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (((Real.hasDerivAt_cos (α * x)).comp x ((hasDerivAt_id x).const_mul α)).const_mul σ)
    have hSin : HasDerivAt (fun y : ℝ => α * Real.sin (α * y))
        (α * (α * Real.cos (α * x))) x := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (((Real.hasDerivAt_sin (α * x)).comp x ((hasDerivAt_id x).const_mul α)).const_mul α)
    have hTrig : HasDerivAt (fun y : ℝ => σ * Real.cos (α * y) + α * Real.sin (α * y))
        (-σ * α * Real.sin (α * x) + α ^ 2 * Real.cos (α * x)) x := by
      convert hCos.add hSin using 1
      ring
    have hMul : HasDerivAt
        (fun y : ℝ => Real.exp (σ * y) * (σ * Real.cos (α * y) + α * Real.sin (α * y)))
        (Real.exp (σ * x) * ((σ ^ 2 + α ^ 2) * Real.cos (α * x))) x := by
      convert hExp.mul hTrig using 1
      ring
    have hDiv : HasDerivAt F
        ((Real.exp (σ * x) * ((σ ^ 2 + α ^ 2) * Real.cos (α * x))) /
          (σ ^ 2 + α ^ 2)) x := by
      simpa [F] using hMul.div_const (σ ^ 2 + α ^ 2)
    convert hDiv using 1
    field_simp [hden]
  have hint : IntervalIntegrable (fun x => Real.exp (σ * x) * Real.cos (α * x)) volume a b := by
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [F]
  field_simp [hden]

private theorem integral_exp_mul_sin
    (σ α a b : ℝ) (hden : σ ^ 2 + α ^ 2 ≠ 0) :
    ∫ x in a..b, Real.exp (σ * x) * Real.sin (α * x) =
      (Real.exp (σ * b) * (σ * Real.sin (α * b) - α * Real.cos (α * b)) -
        Real.exp (σ * a) * (σ * Real.sin (α * a) - α * Real.cos (α * a))) /
        (σ ^ 2 + α ^ 2) := by
  let F : ℝ → ℝ := fun x =>
    (Real.exp (σ * x) * (σ * Real.sin (α * x) - α * Real.cos (α * x))) /
      (σ ^ 2 + α ^ 2)
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt F (Real.exp (σ * x) * Real.sin (α * x)) x := by
    intro x hx
    have hExp : HasDerivAt (fun y : ℝ => Real.exp (σ * y)) (σ * Real.exp (σ * x)) x := by
      simpa [mul_comm] using
        (Real.hasDerivAt_exp (σ * x)).comp x ((hasDerivAt_id x).const_mul σ)
    have hSin : HasDerivAt (fun y : ℝ => σ * Real.sin (α * y))
        (σ * (α * Real.cos (α * x))) x := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (((Real.hasDerivAt_sin (α * x)).comp x ((hasDerivAt_id x).const_mul α)).const_mul σ)
    have hCos : HasDerivAt (fun y : ℝ => α * Real.cos (α * y))
        (α * (-α * Real.sin (α * x))) x := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (((Real.hasDerivAt_cos (α * x)).comp x ((hasDerivAt_id x).const_mul α)).const_mul α)
    have hTrig : HasDerivAt (fun y : ℝ => σ * Real.sin (α * y) - α * Real.cos (α * y))
        (σ * α * Real.cos (α * x) + α ^ 2 * Real.sin (α * x)) x := by
      convert hSin.sub hCos using 1
      ring
    have hMul : HasDerivAt
        (fun y : ℝ => Real.exp (σ * y) * (σ * Real.sin (α * y) - α * Real.cos (α * y)))
        (Real.exp (σ * x) * ((σ ^ 2 + α ^ 2) * Real.sin (α * x))) x := by
      convert hExp.mul hTrig using 1
      ring
    have hDiv : HasDerivAt F
        ((Real.exp (σ * x) * ((σ ^ 2 + α ^ 2) * Real.sin (α * x))) /
          (σ ^ 2 + α ^ 2)) x := by
      simpa [F] using hMul.div_const (σ ^ 2 + α ^ 2)
    convert hDiv using 1
    field_simp [hden]
  have hint : IntervalIntegrable (fun x => Real.exp (σ * x) * Real.sin (α * x)) volume a b := by
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [F]
  field_simp [hden]

private theorem periodicKernel_eq_freeKernel_add_wrap
    (ω Lt : ℝ) (hω : 0 < ω) (hLt : 0 < Lt)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) Lt) :
    periodicKernel ω Lt x =
      freeKernel ω x +
        (Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) /
          (2 * ω * (1 - Real.exp (-ω * Lt))) := by
  have hx_nonneg : 0 ≤ x := hx.1
  have hwrap := sub_free_eq_wrapAround ω hω x Lt hLt
  have hadd := congrArg (fun z : ℝ => z + freeKernel ω x) hwrap
  simpa [freeKernel, abs_of_nonneg hx_nonneg, add_comm, add_left_comm, add_assoc] using hadd

private theorem periodicKernel_sub_eq
    (ω Lt : ℝ) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) Lt) :
    periodicKernel ω Lt (Lt - u) = periodicKernel ω Lt u := by
  have hu_nonneg : 0 ≤ u := hu.1
  have hu_le : u ≤ Lt := hu.2
  unfold periodicKernel
  rw [abs_of_nonneg (sub_nonneg.mpr hu_le), abs_of_nonneg hu_nonneg]
  rw [show ω * (Lt / 2 - (Lt - u)) = -(ω * (Lt / 2 - u)) by ring]
  rw [Real.cosh_neg]

private theorem integral_exp_neg_mul_cos_circleFreq
    (ω Lt : ℝ) (hω : 0 < ω) (hLt : 0 < Lt) (k : ℕ) :
    ∫ x in (0 : ℝ)..Lt,
      Real.exp (-ω * x) * Real.cos ((2 * Real.pi * k / Lt) * x) =
      (-Real.exp (-ω * Lt) * ω + ω) /
        (ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2) := by
  let α : ℝ := 2 * Real.pi * k / Lt
  have hden_pos : 0 < (-ω : ℝ) ^ 2 + α ^ 2 := by
    nlinarith [sq_pos_of_pos hω, sq_nonneg α]
  have hden : (-ω : ℝ) ^ 2 + α ^ 2 ≠ 0 := hden_pos.ne'
  have hLt_ne : Lt ≠ 0 := hLt.ne'
  have hαLt : α * Lt = k * (2 * Real.pi) := by
    dsimp [α]
    field_simp [hLt_ne]
  have hI := integral_exp_mul_cos (-ω) α 0 Lt hden
  have hsin : Real.sin (k * (2 * Real.pi)) = 0 := by
    simpa using (Real.sin_nat_mul_two_pi_sub (x := (0 : ℝ)) k)
  rw [hαLt, Real.cos_nat_mul_two_pi, hsin] at hI
  simpa [α] using hI

private theorem integral_exp_neg_mul_sin_circleFreq
    (ω Lt : ℝ) (hω : 0 < ω) (hLt : 0 < Lt) (k : ℕ) :
    ∫ x in (0 : ℝ)..Lt,
      Real.exp (-ω * x) * Real.sin ((2 * Real.pi * k / Lt) * x) =
      (-Real.exp (-ω * Lt) * (2 * Real.pi * k / Lt) + (2 * Real.pi * k / Lt)) /
        (ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2) := by
  let α : ℝ := 2 * Real.pi * k / Lt
  have hden_pos : 0 < (-ω : ℝ) ^ 2 + α ^ 2 := by
    nlinarith [sq_pos_of_pos hω, sq_nonneg α]
  have hden : (-ω : ℝ) ^ 2 + α ^ 2 ≠ 0 := hden_pos.ne'
  have hLt_ne : Lt ≠ 0 := hLt.ne'
  have hαLt : α * Lt = k * (2 * Real.pi) := by
    dsimp [α]
    field_simp [hLt_ne]
  have hI := integral_exp_mul_sin (-ω) α 0 Lt hden
  have hsin : Real.sin (k * (2 * Real.pi)) = 0 := by
    simpa using (Real.sin_nat_mul_two_pi_sub (x := (0 : ℝ)) k)
  rw [hαLt, Real.cos_nat_mul_two_pi, hsin] at hI
  simpa [α] using hI

private theorem integral_exp_pos_mul_cos_circleFreq
    (ω Lt : ℝ) (hω : 0 < ω) (hLt : 0 < Lt) (k : ℕ) :
    ∫ x in (0 : ℝ)..Lt,
      Real.exp (ω * x) * Real.cos ((2 * Real.pi * k / Lt) * x) =
      (Real.exp (ω * Lt) * ω - ω) /
        (ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2) := by
  let α : ℝ := 2 * Real.pi * k / Lt
  have hden_pos : 0 < (ω : ℝ) ^ 2 + α ^ 2 := by
    nlinarith [sq_pos_of_pos hω, sq_nonneg α]
  have hden : (ω : ℝ) ^ 2 + α ^ 2 ≠ 0 := hden_pos.ne'
  have hLt_ne : Lt ≠ 0 := hLt.ne'
  have hαLt : α * Lt = k * (2 * Real.pi) := by
    dsimp [α]
    field_simp [hLt_ne]
  have hI := integral_exp_mul_cos ω α 0 Lt hden
  have hsin : Real.sin (k * (2 * Real.pi)) = 0 := by
    simpa using (Real.sin_nat_mul_two_pi_sub (x := (0 : ℝ)) k)
  rw [hαLt, Real.cos_nat_mul_two_pi, hsin] at hI
  simpa [α] using hI

private theorem integral_exp_pos_mul_sin_circleFreq
    (ω Lt : ℝ) (hω : 0 < ω) (hLt : 0 < Lt) (k : ℕ) :
    ∫ x in (0 : ℝ)..Lt,
      Real.exp (ω * x) * Real.sin ((2 * Real.pi * k / Lt) * x) =
      (-Real.exp (ω * Lt) * (2 * Real.pi * k / Lt) + (2 * Real.pi * k / Lt)) /
        (ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2) := by
  let α : ℝ := 2 * Real.pi * k / Lt
  have hden_pos : 0 < (ω : ℝ) ^ 2 + α ^ 2 := by
    nlinarith [sq_pos_of_pos hω, sq_nonneg α]
  have hden : (ω : ℝ) ^ 2 + α ^ 2 ≠ 0 := hden_pos.ne'
  have hLt_ne : Lt ≠ 0 := hLt.ne'
  have hαLt : α * Lt = k * (2 * Real.pi) := by
    dsimp [α]
    field_simp [hLt_ne]
  have hI := integral_exp_mul_sin ω α 0 Lt hden
  have hsin : Real.sin (k * (2 * Real.pi)) = 0 := by
    simpa using (Real.sin_nat_mul_two_pi_sub (x := (0 : ℝ)) k)
  rw [hαLt, Real.cos_nat_mul_two_pi, hsin] at hI
  simpa [α] using hI

private theorem integral_periodicKernel_mul_cos_circleFreq
    (ω Lt : ℝ) (hω : 0 < ω) (hLt : 0 < Lt) (k : ℕ) :
    ∫ x in (0 : ℝ)..Lt, periodicKernel ω Lt x * Real.cos ((2 * Real.pi * k / Lt) * x) =
      (ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2)⁻¹ := by
  let a : ℝ := 2 * Real.pi * k / Lt
  let q : ℝ := Real.exp (-ω * Lt)
  let C : ℝ := 2 * ω * (1 - q)
  let D : ℝ := ω ^ 2 + a ^ 2
  have hω_ne : ω ≠ 0 := hω.ne'
  have hq_lt_one : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    nlinarith
  have h1q_ne : 1 - q ≠ 0 := sub_ne_zero.mpr hq_lt_one.ne.symm
  have hC_ne : C ≠ 0 := by
    dsimp [C]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hω_ne) h1q_ne
  have hD_pos : 0 < D := by
    dsimp [D]
    nlinarith [sq_pos_of_pos hω, sq_nonneg a]
  have hD_ne : D ≠ 0 := hD_pos.ne'
  have hfree_int : IntervalIntegrable (fun x => freeKernel ω x * Real.cos (a * x)) volume 0 Lt := by
    exact ((continuous_freeKernel ω).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 Lt
  have hwrap_int : IntervalIntegrable
      (fun x =>
        ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.cos (a * x))
      volume 0 Lt := by
    have hcont :
        Continuous (fun x : ℝ =>
          ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.cos (a * x)) := by
      fun_prop
    exact hcont.intervalIntegrable 0 Lt
  have hsplit :
      ∫ x in (0 : ℝ)..Lt, periodicKernel ω Lt x * Real.cos (a * x) =
        ∫ x in (0 : ℝ)..Lt,
          (freeKernel ω x * Real.cos (a * x)) +
            (((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) *
              Real.cos (a * x)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxI : x ∈ Set.Icc (0 : ℝ) Lt := by
      simpa [Set.uIcc_of_le hLt.le] using hx
    have hpk := periodicKernel_eq_freeKernel_add_wrap ω Lt hω hLt hxI
    dsimp [C, q]
    rw [hpk]
    ring_nf
  have hfree :
      ∫ x in (0 : ℝ)..Lt, freeKernel ω x * Real.cos (a * x) =
        (2 * ω : ℝ)⁻¹ * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.cos (a * x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxI : x ∈ Set.Icc (0 : ℝ) Lt := by
      simpa [Set.uIcc_of_le hLt.le] using hx
    simp [freeKernel, abs_of_nonneg hxI.1, div_eq_mul_inv]
    ring
  have hInt1 : IntervalIntegrable
      (fun x => Real.exp (-ω * (Lt - x)) * Real.cos (a * x)) volume 0 Lt := by
    have hcont :
        Continuous (fun x : ℝ => Real.exp (-ω * (Lt - x)) * Real.cos (a * x)) := by
      fun_prop
    exact hcont.intervalIntegrable 0 Lt
  have hInt2 : IntervalIntegrable
      (fun x => Real.exp (-ω * (Lt + x)) * Real.cos (a * x)) volume 0 Lt := by
    have hcont :
        Continuous (fun x : ℝ => Real.exp (-ω * (Lt + x)) * Real.cos (a * x)) := by
      fun_prop
    exact hcont.intervalIntegrable 0 Lt
  have hA :
      ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt - x)) * Real.cos (a * x) =
        q * (∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.cos (a * x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [q]
    rw [show -ω * (Lt - x) = -ω * Lt + ω * x by ring, Real.exp_add]
    ring
  have hB :
      ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt + x)) * Real.cos (a * x) =
        q * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.cos (a * x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [q]
    rw [show -ω * (Lt + x) = -ω * Lt + -ω * x by ring, Real.exp_add]
    ring
  have hwrap :
      ∫ x in (0 : ℝ)..Lt,
        ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.cos (a * x) =
      C⁻¹ *
        ((q * (∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.cos (a * x))) +
          q * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.cos (a * x))) := by
    calc
      ∫ x in (0 : ℝ)..Lt,
          ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.cos (a * x)
        = C⁻¹ * ∫ x in (0 : ℝ)..Lt,
            (Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) * Real.cos (a * x) := by
              rw [← intervalIntegral.integral_const_mul]
              apply intervalIntegral.integral_congr
              intro x hx
              field_simp [hC_ne]
      _ = C⁻¹ *
            ((∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt - x)) * Real.cos (a * x)) +
              ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt + x)) * Real.cos (a * x)) := by
              congr 1
              calc
                ∫ x in (0 : ℝ)..Lt,
                    (Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) * Real.cos (a * x)
                  = ∫ x in (0 : ℝ)..Lt,
                      Real.exp (-ω * (Lt - x)) * Real.cos (a * x) +
                        Real.exp (-ω * (Lt + x)) * Real.cos (a * x) := by
                          apply intervalIntegral.integral_congr
                          intro x hx
                          ring
                _ = ((∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt - x)) * Real.cos (a * x)) +
                      ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt + x)) * Real.cos (a * x)) := by
                          rw [intervalIntegral.integral_add hInt1 hInt2]
      _ = C⁻¹ *
            ((q * (∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.cos (a * x))) +
              q * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.cos (a * x))) := by
              congr 1
              rw [hA, hB]
  have hnegcos :
      ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.cos (a * x) =
        ω * (1 - q) / D := by
    calc
      ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.cos (a * x)
        = (-Real.exp (-ω * Lt) * ω + ω) / D := by
            simpa [a, D] using integral_exp_neg_mul_cos_circleFreq ω Lt hω hLt k
      _ = ω * (1 - q) / D := by
            dsimp [q]
            ring
  have hposcos :
      ∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.cos (a * x) =
        ω * (Real.exp (ω * Lt) - 1) / D := by
    calc
      ∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.cos (a * x)
        = (Real.exp (ω * Lt) * ω - ω) / D := by
            simpa [a, D] using integral_exp_pos_mul_cos_circleFreq ω Lt hω hLt k
      _ = ω * (Real.exp (ω * Lt) - 1) / D := by ring
  calc
    ∫ x in (0 : ℝ)..Lt, periodicKernel ω Lt x * Real.cos (a * x)
      = (∫ x in (0 : ℝ)..Lt,
            (freeKernel ω x * Real.cos (a * x)) +
              (((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) *
                Real.cos (a * x))) := hsplit
    _ = ((∫ x in (0 : ℝ)..Lt, freeKernel ω x * Real.cos (a * x)) +
          ∫ x in (0 : ℝ)..Lt,
            ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.cos (a * x)) := by
            rw [intervalIntegral.integral_add hfree_int hwrap_int]
    _ = (((2 * ω : ℝ)⁻¹ * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.cos (a * x))) +
          ∫ x in (0 : ℝ)..Lt,
            ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.cos (a * x)) := by
            rw [hfree]
    _ = (((2 * ω : ℝ)⁻¹ * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.cos (a * x))) +
          C⁻¹ *
            ((q * (∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.cos (a * x))) +
              q * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.cos (a * x)))) := by
            rw [hwrap]
    _ = (((2 * ω : ℝ)⁻¹ * (ω * (1 - q) / D)) +
          C⁻¹ * ((q * (ω * (Real.exp (ω * Lt) - 1) / D)) + q * (ω * (1 - q) / D))) := by
            rw [hnegcos, hposcos]
    _ = D⁻¹ := by
          have hqexp : q * Real.exp (ω * Lt) = 1 := by
            dsimp [q]
            rw [← Real.exp_add]
            have : -ω * Lt + ω * Lt = 0 := by ring
            simp
          dsimp [C, D]
          field_simp [hω_ne, h1q_ne, hD_ne]
          nlinarith [hqexp]

private theorem integral_periodicKernel_mul_sin_circleFreq
    (ω Lt : ℝ) (hω : 0 < ω) (hLt : 0 < Lt) (k : ℕ) :
    ∫ x in (0 : ℝ)..Lt, periodicKernel ω Lt x * Real.sin ((2 * Real.pi * k / Lt) * x) = 0 := by
  let a : ℝ := 2 * Real.pi * k / Lt
  let q : ℝ := Real.exp (-ω * Lt)
  let C : ℝ := 2 * ω * (1 - q)
  let D : ℝ := ω ^ 2 + a ^ 2
  have hω_ne : ω ≠ 0 := hω.ne'
  have hq_lt_one : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    nlinarith
  have h1q_ne : 1 - q ≠ 0 := sub_ne_zero.mpr hq_lt_one.ne.symm
  have hC_ne : C ≠ 0 := by
    dsimp [C]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hω_ne) h1q_ne
  have hD_pos : 0 < D := by
    dsimp [D]
    nlinarith [sq_pos_of_pos hω, sq_nonneg a]
  have hD_ne : D ≠ 0 := hD_pos.ne'
  have hfree_int : IntervalIntegrable (fun x => freeKernel ω x * Real.sin (a * x)) volume 0 Lt := by
    exact ((continuous_freeKernel ω).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 Lt
  have hwrap_int : IntervalIntegrable
      (fun x =>
        ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.sin (a * x))
      volume 0 Lt := by
    have hcont :
        Continuous (fun x : ℝ =>
          ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.sin (a * x)) := by
      fun_prop
    exact hcont.intervalIntegrable 0 Lt
  have hsplit :
      ∫ x in (0 : ℝ)..Lt, periodicKernel ω Lt x * Real.sin (a * x) =
        ∫ x in (0 : ℝ)..Lt,
          (freeKernel ω x * Real.sin (a * x)) +
            (((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) *
              Real.sin (a * x)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxI : x ∈ Set.Icc (0 : ℝ) Lt := by
      simpa [Set.uIcc_of_le hLt.le] using hx
    have hpk := periodicKernel_eq_freeKernel_add_wrap ω Lt hω hLt hxI
    dsimp [C, q]
    rw [hpk]
    ring_nf
  have hfree :
      ∫ x in (0 : ℝ)..Lt, freeKernel ω x * Real.sin (a * x) =
        (2 * ω : ℝ)⁻¹ * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.sin (a * x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxI : x ∈ Set.Icc (0 : ℝ) Lt := by
      simpa [Set.uIcc_of_le hLt.le] using hx
    simp [freeKernel, abs_of_nonneg hxI.1, div_eq_mul_inv]
    ring
  have hInt1 : IntervalIntegrable
      (fun x => Real.exp (-ω * (Lt - x)) * Real.sin (a * x)) volume 0 Lt := by
    have hcont :
        Continuous (fun x : ℝ => Real.exp (-ω * (Lt - x)) * Real.sin (a * x)) := by
      fun_prop
    exact hcont.intervalIntegrable 0 Lt
  have hInt2 : IntervalIntegrable
      (fun x => Real.exp (-ω * (Lt + x)) * Real.sin (a * x)) volume 0 Lt := by
    have hcont :
        Continuous (fun x : ℝ => Real.exp (-ω * (Lt + x)) * Real.sin (a * x)) := by
      fun_prop
    exact hcont.intervalIntegrable 0 Lt
  have hA :
      ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt - x)) * Real.sin (a * x) =
        q * (∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.sin (a * x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [q]
    rw [show -ω * (Lt - x) = -ω * Lt + ω * x by ring, Real.exp_add]
    ring
  have hB :
      ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt + x)) * Real.sin (a * x) =
        q * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.sin (a * x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [q]
    rw [show -ω * (Lt + x) = -ω * Lt + -ω * x by ring, Real.exp_add]
    ring
  have hwrap :
      ∫ x in (0 : ℝ)..Lt,
        ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.sin (a * x) =
      C⁻¹ *
        ((q * (∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.sin (a * x))) +
          q * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.sin (a * x))) := by
    calc
      ∫ x in (0 : ℝ)..Lt,
          ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.sin (a * x)
        = C⁻¹ * ∫ x in (0 : ℝ)..Lt,
            (Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) * Real.sin (a * x) := by
              rw [← intervalIntegral.integral_const_mul]
              apply intervalIntegral.integral_congr
              intro x hx
              field_simp [hC_ne]
      _ = C⁻¹ *
            ((∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt - x)) * Real.sin (a * x)) +
              ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt + x)) * Real.sin (a * x)) := by
              congr 1
              calc
                ∫ x in (0 : ℝ)..Lt,
                    (Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) * Real.sin (a * x)
                  = ∫ x in (0 : ℝ)..Lt,
                      Real.exp (-ω * (Lt - x)) * Real.sin (a * x) +
                        Real.exp (-ω * (Lt + x)) * Real.sin (a * x) := by
                          apply intervalIntegral.integral_congr
                          intro x hx
                          ring
                _ = ((∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt - x)) * Real.sin (a * x)) +
                      ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt + x)) * Real.sin (a * x)) := by
                          rw [intervalIntegral.integral_add hInt1 hInt2]
      _ = C⁻¹ *
            ((q * (∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.sin (a * x))) +
              q * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.sin (a * x))) := by
              rw [hA, hB]
  have hnegsin :
      ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.sin (a * x) =
        a * (1 - q) / D := by
    calc
      ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.sin (a * x)
        = (-Real.exp (-ω * Lt) * a + a) / D := by
            simpa [a, D] using integral_exp_neg_mul_sin_circleFreq ω Lt hω hLt k
      _ = a * (1 - q) / D := by
            dsimp [q]
            ring
  have hpossin :
      ∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.sin (a * x) =
        a * (1 - Real.exp (ω * Lt)) / D := by
    calc
      ∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.sin (a * x)
        = (-Real.exp (ω * Lt) * a + a) / D := by
            simpa [a, D] using integral_exp_pos_mul_sin_circleFreq ω Lt hω hLt k
      _ = a * (1 - Real.exp (ω * Lt)) / D := by ring
  calc
    ∫ x in (0 : ℝ)..Lt, periodicKernel ω Lt x * Real.sin (a * x)
      = (∫ x in (0 : ℝ)..Lt,
            (freeKernel ω x * Real.sin (a * x)) +
              (((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) *
                Real.sin (a * x))) := hsplit
    _ = ((∫ x in (0 : ℝ)..Lt, freeKernel ω x * Real.sin (a * x)) +
          ∫ x in (0 : ℝ)..Lt,
            ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.sin (a * x)) := by
            rw [intervalIntegral.integral_add hfree_int hwrap_int]
    _ = (((2 * ω : ℝ)⁻¹ * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.sin (a * x))) +
          ∫ x in (0 : ℝ)..Lt,
            ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.sin (a * x)) := by
            rw [hfree]
    _ = (((2 * ω : ℝ)⁻¹ * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.sin (a * x))) +
          C⁻¹ *
            ((q * (∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.sin (a * x))) +
              q * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.sin (a * x)))) := by
            rw [hwrap]
    _ = (((2 * ω : ℝ)⁻¹ * (a * (1 - q) / D)) +
          C⁻¹ * ((q * (a * (1 - Real.exp (ω * Lt)) / D)) + q * (a * (1 - q) / D))) := by
            rw [hnegsin, hpossin]
    _ = 0 := by
          have hqexp : q * Real.exp (ω * Lt) = 1 := by
            dsimp [q]
            rw [← Real.exp_add]
            have : -ω * Lt + ω * Lt = 0 := by ring
            simp
          have hinner : (1 - q) ^ 2 + q * (1 - Real.exp (ω * Lt) + (1 - q)) = 0 := by
            nlinarith [hqexp]
          dsimp [C, D]
          field_simp [hω_ne, h1q_ne, hD_ne]
          rw [hinner]
          ring

private theorem periodicKernel_neg
    (ω Lt u : ℝ) :
    periodicKernel ω Lt (-u) = periodicKernel ω Lt u := by
  simp [periodicKernel, abs_neg]

private theorem integral_periodicKernel_mul_cos_circleFreq_tail
    (ω Lt : ℝ) (hLt : 0 < Lt) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) Lt) (k : ℕ) :
    ∫ u in (0 : ℝ)..Lt - t, periodicKernel ω Lt u * Real.cos ((2 * Real.pi * k / Lt) * u) =
      ∫ u in t..Lt, periodicKernel ω Lt u * Real.cos ((2 * Real.pi * k / Lt) * u) := by
  let a : ℝ := 2 * Real.pi * k / Lt
  have hLt_ne : Lt ≠ 0 := hLt.ne'
  have hαLt : a * Lt = k * (2 * Real.pi) := by
    dsimp [a]
    field_simp [hLt_ne]
  calc
    ∫ u in (0 : ℝ)..Lt - t, periodicKernel ω Lt u * Real.cos (a * u)
      = ∫ u in (0 : ℝ)..Lt - t, periodicKernel ω Lt (Lt - u) * Real.cos (a * (Lt - u)) := by
          apply intervalIntegral.integral_congr
          intro u hu
          change periodicKernel ω Lt u * Real.cos (a * u) =
            periodicKernel ω Lt (Lt - u) * Real.cos (a * (Lt - u))
          have hu_mem : u ∈ Set.Icc (0 : ℝ) (Lt - t) := by
            simpa [Set.uIcc_of_le (sub_nonneg.mpr ht.2)] using hu
          have huI : u ∈ Set.Icc (0 : ℝ) Lt := by
            exact ⟨hu_mem.1, le_trans hu_mem.2 (sub_le_self Lt ht.1)⟩
          rw [← periodicKernel_sub_eq ω Lt huI]
          have harg : a * (Lt - u) = k * (2 * Real.pi) - a * u := by
            dsimp [a]
            field_simp [hLt_ne]
          rw [harg]
          rw [Real.cos_nat_mul_two_pi_sub]
    _ = ∫ u in t..Lt, periodicKernel ω Lt u * Real.cos (a * u) := by
          simpa [a, sub_eq_add_neg] using
            (intervalIntegral.integral_comp_sub_left
              (f := fun u : ℝ => periodicKernel ω Lt u * Real.cos (a * u))
              (a := (0 : ℝ)) (b := Lt - t) Lt)

private theorem integral_periodicKernel_mul_sin_circleFreq_tail
    (ω Lt : ℝ) (hLt : 0 < Lt) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) Lt) (k : ℕ) :
    ∫ u in (0 : ℝ)..Lt - t, periodicKernel ω Lt u * Real.sin ((2 * Real.pi * k / Lt) * u) =
      -∫ u in t..Lt, periodicKernel ω Lt u * Real.sin ((2 * Real.pi * k / Lt) * u) := by
  let a : ℝ := 2 * Real.pi * k / Lt
  have hLt_ne : Lt ≠ 0 := hLt.ne'
  calc
    ∫ u in (0 : ℝ)..Lt - t, periodicKernel ω Lt u * Real.sin (a * u)
      = ∫ u in (0 : ℝ)..Lt - t,
          -(periodicKernel ω Lt (Lt - u) * Real.sin (a * (Lt - u))) := by
            apply intervalIntegral.integral_congr
            intro u hu
            change periodicKernel ω Lt u * Real.sin (a * u) =
              -(periodicKernel ω Lt (Lt - u) * Real.sin (a * (Lt - u)))
            have hu_mem : u ∈ Set.Icc (0 : ℝ) (Lt - t) := by
              simpa [Set.uIcc_of_le (sub_nonneg.mpr ht.2)] using hu
            have huI : u ∈ Set.Icc (0 : ℝ) Lt := by
              exact ⟨hu_mem.1, le_trans hu_mem.2 (sub_le_self Lt ht.1)⟩
            rw [← periodicKernel_sub_eq ω Lt huI]
            have harg : a * (Lt - u) = k * (2 * Real.pi) - a * u := by
              dsimp [a]
              field_simp [hLt_ne]
            rw [harg]
            rw [Real.sin_nat_mul_two_pi_sub]
            ring
    _ = -∫ u in (0 : ℝ)..Lt - t, periodicKernel ω Lt (Lt - u) * Real.sin (a * (Lt - u)) := by
          rw [intervalIntegral.integral_neg]
    _ = -∫ u in t..Lt, periodicKernel ω Lt u * Real.sin (a * u) := by
          congr 1
          simpa [a, sub_eq_add_neg] using
            (intervalIntegral.integral_comp_sub_left
              (f := fun u : ℝ => periodicKernel ω Lt u * Real.sin (a * u))
              (a := (0 : ℝ)) (b := Lt - t) Lt)

private theorem integral_periodicKernel_shift_mul_cos_circleFreq
    (ω Lt : ℝ) (hω : 0 < ω) (hLt : 0 < Lt)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) Lt) (k : ℕ) :
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) * Real.cos ((2 * Real.pi * k / Lt) * s) =
      (ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2)⁻¹ * Real.cos ((2 * Real.pi * k / Lt) * t) := by
  let a : ℝ := 2 * Real.pi * k / Lt
  let D : ℝ := ω ^ 2 + a ^ 2
  let kc : ℝ → ℝ := fun u => periodicKernel ω Lt u * Real.cos (a * u)
  let ks : ℝ → ℝ := fun u => periodicKernel ω Lt u * Real.sin (a * u)
  have hmain_cont :
      Continuous (fun s : ℝ => periodicKernel ω Lt (t - s) * Real.cos (a * s)) := by
    exact ((continuous_periodicKernel ω Lt).comp (continuous_const.sub continuous_id)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hmain_int₁ :
      IntervalIntegrable (fun s : ℝ => periodicKernel ω Lt (t - s) * Real.cos (a * s))
        volume 0 t := by
    exact hmain_cont.intervalIntegrable 0 t
  have hmain_int₂ :
      IntervalIntegrable (fun s : ℝ => periodicKernel ω Lt (t - s) * Real.cos (a * s))
        volume t Lt := by
    exact hmain_cont.intervalIntegrable t Lt
  have hkc_int₁ : IntervalIntegrable kc volume 0 t := by
    exact (((continuous_periodicKernel ω Lt).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 t)
  have hkc_int₂ : IntervalIntegrable kc volume t Lt := by
    exact (((continuous_periodicKernel ω Lt).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable t Lt)
  have hks_int₁ : IntervalIntegrable ks volume 0 t := by
    exact (((continuous_periodicKernel ω Lt).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 t)
  have hks_int₂ : IntervalIntegrable ks volume t Lt := by
    exact (((continuous_periodicKernel ω Lt).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable t Lt)
  have hkc_tail : IntervalIntegrable kc volume 0 (Lt - t) := by
    exact
      ((continuous_periodicKernel ω Lt).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable 0
        (Lt - t)
  have hks_tail : IntervalIntegrable ks volume 0 (Lt - t) := by
    exact
      ((continuous_periodicKernel ω Lt).mul
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable 0
        (Lt - t)
  have hsplit :
      ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) * Real.cos (a * s) =
        (∫ s in (0 : ℝ)..t, periodicKernel ω Lt (t - s) * Real.cos (a * s)) +
          ∫ s in t..Lt, periodicKernel ω Lt (t - s) * Real.cos (a * s) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hmain_int₁ hmain_int₂]
  have hI₁ :
      ∫ s in (0 : ℝ)..t, periodicKernel ω Lt (t - s) * Real.cos (a * s) =
        Real.cos (a * t) * (∫ u in (0 : ℝ)..t, kc u) +
          Real.sin (a * t) * (∫ u in (0 : ℝ)..t, ks u) := by
    calc
      ∫ s in (0 : ℝ)..t, periodicKernel ω Lt (t - s) * Real.cos (a * s)
        = ∫ u in (0 : ℝ)..t, periodicKernel ω Lt u * Real.cos (a * (t - u)) := by
            simpa [a] using
              (intervalIntegral.integral_comp_sub_left
                (f := fun u : ℝ => periodicKernel ω Lt u * Real.cos (a * (t - u)))
                (a := (0 : ℝ)) (b := t) t)
      _ = ∫ u in (0 : ℝ)..t,
            periodicKernel ω Lt u *
              (Real.cos (a * t) * Real.cos (a * u) +
                Real.sin (a * t) * Real.sin (a * u)) := by
            apply intervalIntegral.integral_congr
            intro u hu
            change periodicKernel ω Lt u * Real.cos (a * (t - u)) =
              periodicKernel ω Lt u *
                (Real.cos (a * t) * Real.cos (a * u) +
                  Real.sin (a * t) * Real.sin (a * u))
            have harg : a * (t - u) = a * t - a * u := by ring
            rw [harg, Real.cos_sub]
      _ = ∫ u in (0 : ℝ)..t, Real.cos (a * t) * kc u + Real.sin (a * t) * ks u := by
            apply intervalIntegral.integral_congr
            intro u hu
            simp [kc, ks]
            ring
      _ = (∫ u in (0 : ℝ)..t, Real.cos (a * t) * kc u) +
            ∫ u in (0 : ℝ)..t, Real.sin (a * t) * ks u := by
            rw [intervalIntegral.integral_add (hkc_int₁.const_mul _) (hks_int₁.const_mul _)]
      _ = Real.cos (a * t) * (∫ u in (0 : ℝ)..t, kc u) +
            Real.sin (a * t) * (∫ u in (0 : ℝ)..t, ks u) := by
            rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hI₂ :
      ∫ s in t..Lt, periodicKernel ω Lt (t - s) * Real.cos (a * s) =
        Real.cos (a * t) * (∫ u in (0 : ℝ)..Lt - t, kc u) -
          Real.sin (a * t) * (∫ u in (0 : ℝ)..Lt - t, ks u) := by
    calc
      ∫ s in t..Lt, periodicKernel ω Lt (t - s) * Real.cos (a * s)
        = ∫ u in (0 : ℝ)..Lt - t, periodicKernel ω Lt (-u) * Real.cos (a * (u + t)) := by
            simpa [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              (intervalIntegral.integral_comp_sub_right
                (f := fun u : ℝ => periodicKernel ω Lt (-u) * Real.cos (a * (u + t)))
                (a := t) (b := Lt) t)
      _ = ∫ u in (0 : ℝ)..Lt - t, periodicKernel ω Lt u * Real.cos (a * (u + t)) := by
            apply intervalIntegral.integral_congr
            intro u hu
            change periodicKernel ω Lt (-u) * Real.cos (a * (u + t)) =
              periodicKernel ω Lt u * Real.cos (a * (u + t))
            rw [periodicKernel_neg]
      _ = ∫ u in (0 : ℝ)..Lt - t,
            periodicKernel ω Lt u *
              (Real.cos (a * t) * Real.cos (a * u) -
                Real.sin (a * t) * Real.sin (a * u)) := by
            apply intervalIntegral.integral_congr
            intro u hu
            change periodicKernel ω Lt u * Real.cos (a * (u + t)) =
              periodicKernel ω Lt u *
                (Real.cos (a * t) * Real.cos (a * u) -
                  Real.sin (a * t) * Real.sin (a * u))
            have harg : a * (u + t) = a * t + a * u := by ring
            rw [harg, Real.cos_add]
      _ = ∫ u in (0 : ℝ)..Lt - t, Real.cos (a * t) * kc u - Real.sin (a * t) * ks u := by
            apply intervalIntegral.integral_congr
            intro u hu
            simp [kc, ks]
            ring
      _ = (∫ u in (0 : ℝ)..Lt - t, Real.cos (a * t) * kc u) +
            ∫ u in (0 : ℝ)..Lt - t, (-Real.sin (a * t)) * ks u := by
            rw [show (fun u : ℝ => Real.cos (a * t) * kc u - Real.sin (a * t) * ks u) =
              fun u : ℝ => Real.cos (a * t) * kc u + (-Real.sin (a * t)) * ks u by
              ext u
              ring]
            have hcos_tail :
                IntervalIntegrable (fun u : ℝ => Real.cos (a * t) * kc u) volume 0 (Lt - t) :=
              hkc_tail.const_mul _
            have hsin_tail :
                IntervalIntegrable (fun u : ℝ => (-Real.sin (a * t)) * ks u) volume 0 (Lt - t) :=
              hks_tail.const_mul _
            rw [intervalIntegral.integral_add hcos_tail hsin_tail]
      _ = Real.cos (a * t) * (∫ u in (0 : ℝ)..Lt - t, kc u) -
            Real.sin (a * t) * (∫ u in (0 : ℝ)..Lt - t, ks u) := by
            rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
            ring
  have hA :
      (∫ u in (0 : ℝ)..t, kc u) + ∫ u in (0 : ℝ)..Lt - t, kc u =
        ∫ u in (0 : ℝ)..Lt, kc u := by
    have htail :
        ∫ u in (0 : ℝ)..Lt - t, kc u = ∫ u in t..Lt, kc u := by
      simpa [kc, a] using integral_periodicKernel_mul_cos_circleFreq_tail ω Lt hLt ht k
    rw [htail]
    exact intervalIntegral.integral_add_adjacent_intervals hkc_int₁ hkc_int₂
  have hB :
      (∫ u in (0 : ℝ)..t, ks u) - ∫ u in (0 : ℝ)..Lt - t, ks u =
        ∫ u in (0 : ℝ)..Lt, ks u := by
    have htail :
        ∫ u in (0 : ℝ)..Lt - t, ks u = -∫ u in t..Lt, ks u := by
      simpa [ks, a] using integral_periodicKernel_mul_sin_circleFreq_tail ω Lt hLt ht k
    calc
      (∫ u in (0 : ℝ)..t, ks u) - ∫ u in (0 : ℝ)..Lt - t, ks u
        = (∫ u in (0 : ℝ)..t, ks u) + ∫ u in t..Lt, ks u := by
            rw [htail]
            ring
      _ = ∫ u in (0 : ℝ)..Lt, ks u := by
            exact intervalIntegral.integral_add_adjacent_intervals hks_int₁ hks_int₂
  calc
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) * Real.cos (a * s)
      = (∫ s in (0 : ℝ)..t, periodicKernel ω Lt (t - s) * Real.cos (a * s)) +
          ∫ s in t..Lt, periodicKernel ω Lt (t - s) * Real.cos (a * s) := hsplit
    _ = (Real.cos (a * t) * (∫ u in (0 : ℝ)..t, kc u) +
          Real.sin (a * t) * (∫ u in (0 : ℝ)..t, ks u)) +
            (Real.cos (a * t) * (∫ u in (0 : ℝ)..Lt - t, kc u) -
              Real.sin (a * t) * (∫ u in (0 : ℝ)..Lt - t, ks u)) := by
            rw [hI₁, hI₂]
    _ = Real.cos (a * t) * (∫ u in (0 : ℝ)..Lt, kc u) +
          Real.sin (a * t) * (∫ u in (0 : ℝ)..Lt, ks u) := by
            rw [← hA, ← hB]
            ring
    _ = Real.cos (a * t) * D⁻¹ + Real.sin (a * t) * 0 := by
            rw [show (∫ u in (0 : ℝ)..Lt, kc u) = D⁻¹ by
              simpa [kc, a, D] using integral_periodicKernel_mul_cos_circleFreq ω Lt hω hLt k]
            rw [show (∫ u in (0 : ℝ)..Lt, ks u) = 0 by
              simpa [ks, a] using integral_periodicKernel_mul_sin_circleFreq ω Lt hω hLt k]
    _ = D⁻¹ * Real.cos (a * t) := by ring
    _ = (ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2)⁻¹ * Real.cos ((2 * Real.pi * k / Lt) * t) := by
          simp [a, D, mul_comm]

private theorem integral_periodicKernel_shift_mul_sin_circleFreq
    (ω Lt : ℝ) (hω : 0 < ω) (hLt : 0 < Lt)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) Lt) (k : ℕ) :
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) * Real.sin ((2 * Real.pi * k / Lt) * s) =
      (ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2)⁻¹ * Real.sin ((2 * Real.pi * k / Lt) * t) := by
  let a : ℝ := 2 * Real.pi * k / Lt
  let D : ℝ := ω ^ 2 + a ^ 2
  let kc : ℝ → ℝ := fun u => periodicKernel ω Lt u * Real.cos (a * u)
  let ks : ℝ → ℝ := fun u => periodicKernel ω Lt u * Real.sin (a * u)
  have hmain_cont :
      Continuous (fun s : ℝ => periodicKernel ω Lt (t - s) * Real.sin (a * s)) := by
    exact ((continuous_periodicKernel ω Lt).comp (continuous_const.sub continuous_id)).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hmain_int₁ :
      IntervalIntegrable (fun s : ℝ => periodicKernel ω Lt (t - s) * Real.sin (a * s))
        volume 0 t := by
    exact hmain_cont.intervalIntegrable 0 t
  have hmain_int₂ :
      IntervalIntegrable (fun s : ℝ => periodicKernel ω Lt (t - s) * Real.sin (a * s))
        volume t Lt := by
    exact hmain_cont.intervalIntegrable t Lt
  have hkc_int₁ : IntervalIntegrable kc volume 0 t := by
    exact (((continuous_periodicKernel ω Lt).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 t)
  have hkc_int₂ : IntervalIntegrable kc volume t Lt := by
    exact (((continuous_periodicKernel ω Lt).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable t Lt)
  have hks_int₁ : IntervalIntegrable ks volume 0 t := by
    exact (((continuous_periodicKernel ω Lt).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 t)
  have hks_int₂ : IntervalIntegrable ks volume t Lt := by
    exact (((continuous_periodicKernel ω Lt).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable t Lt)
  have hkc_tail : IntervalIntegrable kc volume 0 (Lt - t) := by
    exact
      ((continuous_periodicKernel ω Lt).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable 0
        (Lt - t)
  have hks_tail : IntervalIntegrable ks volume 0 (Lt - t) := by
    exact
      ((continuous_periodicKernel ω Lt).mul
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable 0
        (Lt - t)
  have hsplit :
      ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) * Real.sin (a * s) =
        (∫ s in (0 : ℝ)..t, periodicKernel ω Lt (t - s) * Real.sin (a * s)) +
          ∫ s in t..Lt, periodicKernel ω Lt (t - s) * Real.sin (a * s) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hmain_int₁ hmain_int₂]
  have hI₁ :
      ∫ s in (0 : ℝ)..t, periodicKernel ω Lt (t - s) * Real.sin (a * s) =
        Real.sin (a * t) * (∫ u in (0 : ℝ)..t, kc u) -
          Real.cos (a * t) * (∫ u in (0 : ℝ)..t, ks u) := by
    calc
      ∫ s in (0 : ℝ)..t, periodicKernel ω Lt (t - s) * Real.sin (a * s)
        = ∫ u in (0 : ℝ)..t, periodicKernel ω Lt u * Real.sin (a * (t - u)) := by
            simpa [a] using
              (intervalIntegral.integral_comp_sub_left
                (f := fun u : ℝ => periodicKernel ω Lt u * Real.sin (a * (t - u)))
                (a := (0 : ℝ)) (b := t) t)
      _ = ∫ u in (0 : ℝ)..t,
            periodicKernel ω Lt u *
              (Real.sin (a * t) * Real.cos (a * u) -
                Real.cos (a * t) * Real.sin (a * u)) := by
            apply intervalIntegral.integral_congr
            intro u hu
            change periodicKernel ω Lt u * Real.sin (a * (t - u)) =
              periodicKernel ω Lt u *
                (Real.sin (a * t) * Real.cos (a * u) -
                  Real.cos (a * t) * Real.sin (a * u))
            have harg : a * (t - u) = a * t - a * u := by ring
            rw [harg, Real.sin_sub]
      _ = ∫ u in (0 : ℝ)..t, Real.sin (a * t) * kc u - Real.cos (a * t) * ks u := by
            apply intervalIntegral.integral_congr
            intro u hu
            simp [kc, ks]
            ring
      _ = (∫ u in (0 : ℝ)..t, Real.sin (a * t) * kc u) +
            ∫ u in (0 : ℝ)..t, (-Real.cos (a * t)) * ks u := by
            rw [show (fun u : ℝ => Real.sin (a * t) * kc u - Real.cos (a * t) * ks u) =
              fun u : ℝ => Real.sin (a * t) * kc u + (-Real.cos (a * t)) * ks u by
              ext u
              ring]
            have hsin_head :
                IntervalIntegrable (fun u : ℝ => Real.sin (a * t) * kc u) volume 0 t :=
              hkc_int₁.const_mul _
            have hcos_head :
                IntervalIntegrable (fun u : ℝ => (-Real.cos (a * t)) * ks u) volume 0 t :=
              hks_int₁.const_mul _
            rw [intervalIntegral.integral_add hsin_head hcos_head]
      _ = Real.sin (a * t) * (∫ u in (0 : ℝ)..t, kc u) -
            Real.cos (a * t) * (∫ u in (0 : ℝ)..t, ks u) := by
            rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
            ring
  have hI₂ :
      ∫ s in t..Lt, periodicKernel ω Lt (t - s) * Real.sin (a * s) =
        Real.sin (a * t) * (∫ u in (0 : ℝ)..Lt - t, kc u) +
          Real.cos (a * t) * (∫ u in (0 : ℝ)..Lt - t, ks u) := by
    calc
      ∫ s in t..Lt, periodicKernel ω Lt (t - s) * Real.sin (a * s)
        = ∫ u in (0 : ℝ)..Lt - t, periodicKernel ω Lt (-u) * Real.sin (a * (u + t)) := by
            simpa [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              (intervalIntegral.integral_comp_sub_right
                (f := fun u : ℝ => periodicKernel ω Lt (-u) * Real.sin (a * (u + t)))
                (a := t) (b := Lt) t)
      _ = ∫ u in (0 : ℝ)..Lt - t, periodicKernel ω Lt u * Real.sin (a * (u + t)) := by
            apply intervalIntegral.integral_congr
            intro u hu
            change periodicKernel ω Lt (-u) * Real.sin (a * (u + t)) =
              periodicKernel ω Lt u * Real.sin (a * (u + t))
            rw [periodicKernel_neg]
      _ = ∫ u in (0 : ℝ)..Lt - t,
            periodicKernel ω Lt u *
              (Real.sin (a * t) * Real.cos (a * u) +
                Real.cos (a * t) * Real.sin (a * u)) := by
            apply intervalIntegral.integral_congr
            intro u hu
            change periodicKernel ω Lt u * Real.sin (a * (u + t)) =
              periodicKernel ω Lt u *
                (Real.sin (a * t) * Real.cos (a * u) +
                  Real.cos (a * t) * Real.sin (a * u))
            have harg : a * (u + t) = a * t + a * u := by ring
            rw [harg, Real.sin_add]
      _ = ∫ u in (0 : ℝ)..Lt - t, Real.sin (a * t) * kc u + Real.cos (a * t) * ks u := by
            apply intervalIntegral.integral_congr
            intro u hu
            simp [kc, ks]
            ring
      _ = (∫ u in (0 : ℝ)..Lt - t, Real.sin (a * t) * kc u) +
            ∫ u in (0 : ℝ)..Lt - t, Real.cos (a * t) * ks u := by
            rw [intervalIntegral.integral_add (hkc_tail.const_mul _) (hks_tail.const_mul _)]
      _ = Real.sin (a * t) * (∫ u in (0 : ℝ)..Lt - t, kc u) +
            Real.cos (a * t) * (∫ u in (0 : ℝ)..Lt - t, ks u) := by
            rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hA :
      (∫ u in (0 : ℝ)..t, kc u) + ∫ u in (0 : ℝ)..Lt - t, kc u =
        ∫ u in (0 : ℝ)..Lt, kc u := by
    have htail :
        ∫ u in (0 : ℝ)..Lt - t, kc u = ∫ u in t..Lt, kc u := by
      simpa [kc, a] using integral_periodicKernel_mul_cos_circleFreq_tail ω Lt hLt ht k
    rw [htail]
    exact intervalIntegral.integral_add_adjacent_intervals hkc_int₁ hkc_int₂
  have hB :
      -(∫ u in (0 : ℝ)..t, ks u) + ∫ u in (0 : ℝ)..Lt - t, ks u = 0 := by
    have htail :
        ∫ u in (0 : ℝ)..Lt - t, ks u = -∫ u in t..Lt, ks u := by
      simpa [ks, a] using integral_periodicKernel_mul_sin_circleFreq_tail ω Lt hLt ht k
    calc
      -(∫ u in (0 : ℝ)..t, ks u) + ∫ u in (0 : ℝ)..Lt - t, ks u
        = -(∫ u in (0 : ℝ)..t, ks u) + -(∫ u in t..Lt, ks u) := by
            rw [htail]
      _ = -((∫ u in (0 : ℝ)..t, ks u) + ∫ u in t..Lt, ks u) := by
            ring
      _ = -(∫ u in (0 : ℝ)..Lt, ks u) := by
            rw [intervalIntegral.integral_add_adjacent_intervals hks_int₁ hks_int₂]
      _ = 0 := by
            have hks_zero : ∫ u in (0 : ℝ)..Lt, ks u = 0 := by
              simpa [ks, a] using integral_periodicKernel_mul_sin_circleFreq ω Lt hω hLt k
            rw [hks_zero]
            simp
  calc
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) * Real.sin (a * s)
      = (∫ s in (0 : ℝ)..t, periodicKernel ω Lt (t - s) * Real.sin (a * s)) +
          ∫ s in t..Lt, periodicKernel ω Lt (t - s) * Real.sin (a * s) := hsplit
    _ = (Real.sin (a * t) * (∫ u in (0 : ℝ)..t, kc u) -
          Real.cos (a * t) * (∫ u in (0 : ℝ)..t, ks u)) +
            (Real.sin (a * t) * (∫ u in (0 : ℝ)..Lt - t, kc u) +
              Real.cos (a * t) * (∫ u in (0 : ℝ)..Lt - t, ks u)) := by
            rw [hI₁, hI₂]
    _ = Real.sin (a * t) * ((∫ u in (0 : ℝ)..t, kc u) + ∫ u in (0 : ℝ)..Lt - t, kc u) +
          Real.cos (a * t) * (-(∫ u in (0 : ℝ)..t, ks u) +
            ∫ u in (0 : ℝ)..Lt - t, ks u) := by
            ring
    _ = Real.sin (a * t) * (∫ u in (0 : ℝ)..Lt, kc u) + Real.cos (a * t) * 0 := by
            rw [hA, hB]
    _ = Real.sin (a * t) * D⁻¹ + Real.cos (a * t) * 0 := by
            rw [show (∫ u in (0 : ℝ)..Lt, kc u) = D⁻¹ by
              simpa [kc, a, D] using integral_periodicKernel_mul_cos_circleFreq ω Lt hω hLt k]
    _ = D⁻¹ * Real.sin (a * t) := by ring
    _ = (ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2)⁻¹ * Real.sin ((2 * Real.pi * k / Lt) * t) := by
          simp [a, D, mul_comm]

private theorem fourierBasisFun_cos_mode
    (Lt : ℝ) [Fact (0 < Lt)] (k : ℕ) (hk : 0 < k) (t : ℝ) :
    SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k - 1) t =
      Real.sqrt (2 / Lt) * Real.cos ((2 * Real.pi * k / Lt) * t) := by
  have hLt_ne : Lt ≠ 0 := ne_of_gt (Fact.out : 0 < Lt)
  rw [show (2 * k - 1 : ℕ) = 2 * (k - 1) + 1 by omega]
  simp only [SmoothMap_Circle.fourierBasisFun,
    if_pos (show 2 * (k - 1) % 2 = 0 by omega),
    show (2 * (k - 1) / 2 + 1 : ℕ) = k by omega]
  have harg : 2 * Real.pi * (k : ℝ) * t / Lt = (2 * Real.pi * k / Lt) * t := by
    field_simp [hLt_ne]
  rw [harg]

private theorem fourierBasisFun_sin_mode
    (Lt : ℝ) [Fact (0 < Lt)] (k : ℕ) (hk : 0 < k) (t : ℝ) :
    SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k) t =
      Real.sqrt (2 / Lt) * Real.sin ((2 * Real.pi * k / Lt) * t) := by
  have hLt_ne : Lt ≠ 0 := ne_of_gt (Fact.out : 0 < Lt)
  rw [show (2 * k : ℕ) = (2 * k - 1) + 1 by omega]
  simp only [SmoothMap_Circle.fourierBasisFun,
    if_neg (show ¬ ((2 * k - 1) % 2 = 0) by omega),
    show ((2 * k - 1) / 2 + 1 : ℕ) = k by omega]
  have harg : 2 * Real.pi * (k : ℝ) * t / Lt = (2 * Real.pi * k / Lt) * t := by
    field_simp [hLt_ne]
  rw [harg]

private theorem circleEigenvalue_cos_mode
    (Lt : ℝ) [Fact (0 < Lt)] (k : ℕ) (hk : 0 < k) :
    HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (2 * k - 1) =
      (2 * Real.pi * k / Lt) ^ 2 := by
  rw [show (2 * k - 1 : ℕ) = 2 * (k - 1) + 1 by omega]
  simp only [HasLaplacianEigenvalues.eigenvalue, SmoothMap_Circle.fourierFreq]
  have hk' : (((2 * (k - 1) / 2 + 1 : ℕ) : ℝ)) = k := by
    exact_mod_cast (show (2 * (k - 1) / 2 + 1 : ℕ) = k by omega)
  rw [hk']

private theorem circleEigenvalue_sin_mode
    (Lt : ℝ) [Fact (0 < Lt)] (k : ℕ) (hk : 0 < k) :
    HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (2 * k) =
      (2 * Real.pi * k / Lt) ^ 2 := by
  rw [show (2 * k : ℕ) = (2 * k - 1) + 1 by omega]
  simp only [HasLaplacianEigenvalues.eigenvalue, SmoothMap_Circle.fourierFreq,
    show ((2 * k - 1) / 2 + 1 : ℕ) = k by omega]

private theorem integral_periodicKernel_shift_mul_fourierBasis_zero
    (ω Lt : ℝ) [Fact (0 < Lt)] (hω : 0 < ω)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) Lt) :
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) *
        SmoothMap_Circle.fourierBasisFun (L := Lt) 0 s =
      (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) 0 + ω ^ 2)⁻¹ *
        SmoothMap_Circle.fourierBasisFun (L := Lt) 0 t := by
  have hLt : 0 < Lt := Fact.out
  have hscalar :
      ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) = (ω ^ 2)⁻¹ := by
    simpa using integral_periodicKernel_shift_mul_cos_circleFreq ω Lt hω hLt ht 0
  calc
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) *
        SmoothMap_Circle.fourierBasisFun (L := Lt) 0 s
      = ∫ s in (0 : ℝ)..Lt, (1 / Real.sqrt Lt) * periodicKernel ω Lt (t - s) := by
          apply intervalIntegral.integral_congr
          intro s hs
          simp [SmoothMap_Circle.fourierBasisFun]
          ring
    _ = (1 / Real.sqrt Lt) * ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) := by
          rw [intervalIntegral.integral_const_mul]
    _ = (1 / Real.sqrt Lt) * (ω ^ 2)⁻¹ := by rw [hscalar]
    _ = (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) 0 + ω ^ 2)⁻¹ *
          SmoothMap_Circle.fourierBasisFun (L := Lt) 0 t := by
          simp [HasLaplacianEigenvalues.eigenvalue, SmoothMap_Circle.fourierFreq,
            SmoothMap_Circle.fourierBasisFun]
          ring

private theorem integral_periodicKernel_shift_mul_fourierBasis_cos
    (ω Lt : ℝ) [Fact (0 < Lt)] (hω : 0 < ω)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) Lt) (k : ℕ) (hk : 0 < k) :
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) *
        SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k - 1) s =
      (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (2 * k - 1) + ω ^ 2)⁻¹ *
        SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k - 1) t := by
  have hLt : 0 < Lt := Fact.out
  calc
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) *
        SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k - 1) s
      = ∫ s in (0 : ℝ)..Lt,
          Real.sqrt (2 / Lt) *
            (periodicKernel ω Lt (t - s) * Real.cos ((2 * Real.pi * k / Lt) * s)) := by
              apply intervalIntegral.integral_congr
              intro s hs
              change periodicKernel ω Lt (t - s) *
                  SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k - 1) s =
                Real.sqrt (2 / Lt) *
                  (periodicKernel ω Lt (t - s) * Real.cos ((2 * Real.pi * k / Lt) * s))
              rw [fourierBasisFun_cos_mode (Lt := Lt) k hk s]
              ring
    _ = Real.sqrt (2 / Lt) *
          ∫ s in (0 : ℝ)..Lt,
            periodicKernel ω Lt (t - s) * Real.cos ((2 * Real.pi * k / Lt) * s) := by
              rw [intervalIntegral.integral_const_mul]
    _ = Real.sqrt (2 / Lt) *
          ((ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2)⁻¹ *
            Real.cos ((2 * Real.pi * k / Lt) * t)) := by
              rw [integral_periodicKernel_shift_mul_cos_circleFreq ω Lt hω hLt ht k]
    _ = (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (2 * k - 1) + ω ^ 2)⁻¹ *
          SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k - 1) t := by
              rw [circleEigenvalue_cos_mode (Lt := Lt) k hk,
                fourierBasisFun_cos_mode (Lt := Lt) k hk t]
              ring

private theorem integral_periodicKernel_shift_mul_fourierBasis_sin
    (ω Lt : ℝ) [Fact (0 < Lt)] (hω : 0 < ω)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) Lt) (k : ℕ) (hk : 0 < k) :
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) *
        SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k) s =
      (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (2 * k) + ω ^ 2)⁻¹ *
        SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k) t := by
  have hLt : 0 < Lt := Fact.out
  calc
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) *
        SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k) s
      = ∫ s in (0 : ℝ)..Lt,
          Real.sqrt (2 / Lt) *
            (periodicKernel ω Lt (t - s) * Real.sin ((2 * Real.pi * k / Lt) * s)) := by
              apply intervalIntegral.integral_congr
              intro s hs
              change periodicKernel ω Lt (t - s) *
                  SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k) s =
                Real.sqrt (2 / Lt) *
                  (periodicKernel ω Lt (t - s) * Real.sin ((2 * Real.pi * k / Lt) * s))
              rw [fourierBasisFun_sin_mode (Lt := Lt) k hk s]
              ring
    _ = Real.sqrt (2 / Lt) *
          ∫ s in (0 : ℝ)..Lt,
            periodicKernel ω Lt (t - s) * Real.sin ((2 * Real.pi * k / Lt) * s) := by
              rw [intervalIntegral.integral_const_mul]
    _ = Real.sqrt (2 / Lt) *
          ((ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2)⁻¹ *
            Real.sin ((2 * Real.pi * k / Lt) * t)) := by
              rw [integral_periodicKernel_shift_mul_sin_circleFreq ω Lt hω hLt ht k]
    _ = (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (2 * k) + ω ^ 2)⁻¹ *
          SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k) t := by
              rw [circleEigenvalue_sin_mode (Lt := Lt) k hk,
                fourierBasisFun_sin_mode (Lt := Lt) k hk t]
              ring

private theorem integral_periodicKernel_shift_mul_fourierBasisFun
    (ω Lt : ℝ) [Fact (0 < Lt)] (hω : 0 < ω)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) Lt) (n : ℕ) :
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) *
        SmoothMap_Circle.fourierBasisFun (L := Lt) n s =
      (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ *
        SmoothMap_Circle.fourierBasisFun (L := Lt) n t := by
  cases n with
  | zero =>
      simpa using integral_periodicKernel_shift_mul_fourierBasis_zero ω Lt hω ht
  | succ m =>
      rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
      · have hm : m + 1 = 2 * (j + 1) - 1 := by
          omega
        rw [hm]
        simpa using
          integral_periodicKernel_shift_mul_fourierBasis_cos
            ω Lt hω ht (j + 1) (by omega)
      · have hm : m + 1 = 2 * (j + 1) := by
          omega
        rw [hm]
        simpa using
          integral_periodicKernel_shift_mul_fourierBasis_sin
            ω Lt hω ht (j + 1) (by omega)

private theorem smoothCircle_coeff_eq_fourierCoeffReal
    (Lt : ℝ) [Fact (0 < Lt)] (m : ℕ) (f : SmoothMap_Circle Lt ℝ) :
    DyninMityaginSpace.coeff m f = SmoothMap_Circle.fourierCoeffReal (L := Lt) m f := by
  change ((RapidDecaySeq.coeffCLM m).comp
    (SmoothMap_Circle.smoothCircleRapidDecayEquiv (L := Lt)).toContinuousLinearMap) f = _
  simp [RapidDecaySeq.coeffCLM, RapidDecaySeq.coeffLM,
    SmoothMap_Circle.smoothCircleRapidDecayEquiv,
    SmoothMap_Circle.toRapidDecayLM, SmoothMap_Circle.toRapidDecay]

private theorem integral_Icc_eq_intervalIntegral
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (_hf : IntervalIntegrable f MeasureTheory.volume a b) :
    ∫ x in Set.Icc a b, f x = ∫ x in a..b, f x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

private theorem greenFunctionBilinear_continuous_left
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E]
    [HasLaplacianEigenvalues E]
    (mass : ℝ) (hmass : 0 < mass) (h : E) :
    Continuous (fun f => greenFunctionBilinear mass hmass f h) := by
  have hcdiag := greenFunctionBilinear_continuous_diag mass hmass (E := E)
  have hpol : ∀ f, greenFunctionBilinear mass hmass f h =
      (greenFunctionBilinear mass hmass (f + h) (f + h) -
        greenFunctionBilinear mass hmass f f -
        greenFunctionBilinear mass hmass h h) / 2 := by
    intro f
    have : greenFunctionBilinear mass hmass (f + h) (f + h) =
        greenFunctionBilinear mass hmass f f +
          2 * greenFunctionBilinear mass hmass f h +
          greenFunctionBilinear mass hmass h h := by
      rw [greenFunctionBilinear_add_left, greenFunctionBilinear_add_right,
        greenFunctionBilinear_add_right, greenFunctionBilinear_symm mass hmass h f]
      ring
    linarith
  exact (((hcdiag.comp (continuous_id.add continuous_const)).sub hcdiag).sub
    continuous_const).div_const 2 |>.congr (fun f => (hpol f).symm)

private noncomputable def greenCLM_left
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E]
    [HasLaplacianEigenvalues E]
    (mass : ℝ) (hmass : 0 < mass) (h : E) : E →L[ℝ] ℝ :=
  ⟨{ toFun := fun f => greenFunctionBilinear mass hmass f h
     map_add' := fun f₁ f₂ => greenFunctionBilinear_add_left mass hmass f₁ f₂ h
     map_smul' := fun c f => by
      rw [greenFunctionBilinear_smul_left, RingHom.id_apply, smul_eq_mul] },
    greenFunctionBilinear_continuous_left mass hmass h⟩

@[simp] private theorem greenCLM_left_apply
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E]
    [HasLaplacianEigenvalues E]
    (mass : ℝ) (hmass : 0 < mass) (h f : E) :
    greenCLM_left mass hmass h f = greenFunctionBilinear mass hmass f h := rfl

/-- Uniform bilinear version of `torusGreen_uniform_bound`.

The method-of-images estimate from gaussian-field gives a uniform diagonal bound
`G_L(embed f, embed f) ≤ C q(f)^2`. Since the embedded torus covariance is a
symmetric positive semidefinite bilinear form, Mathlib's bilinear-form
Cauchy-Schwarz upgrades this to the cross estimate
`|G_L(embed f, embed g)| ≤ C q(f) q(g)` uniformly in `Lt ≥ 1`. This is the
quantitative continuity input needed for any later density extension from the
proved compact-support finite-rank subset. -/
private theorem asymTorusGreen_uniform_product_seminorm_bound
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (C : ℝ) (_ : 0 < C) (q : Seminorm ℝ (CylinderTestFunction Ls)),
      Continuous q ∧
      ∀ (Lt : ℝ) [Fact (0 < Lt)],
        1 ≤ Lt →
        ∀ f g : CylinderTestFunction Ls,
          |asymTorusContinuumGreen Lt Ls mass hmass
              (cylinderToTorusEmbed Lt Ls f)
              (cylinderToTorusEmbed Lt Ls g)| ≤
            C * q f * q g := by
  obtain ⟨C, hC_pos, q, hq_cont, hdiag⟩ :=
    GaussianField.torusGreen_uniform_bound (Ls := Ls) mass hmass
  refine ⟨C, hC_pos, q, hq_cont, ?_⟩
  intro Lt _ hLt f g
  let B : LinearMap.BilinForm ℝ (CylinderTestFunction Ls) := by
    refine
      { toFun := ?_
        map_add' := ?_
        map_smul' := ?_ }
    · intro f'
      refine
        { toFun := ?_
          map_add' := ?_
          map_smul' := ?_ }
      · intro g'
        exact asymTorusContinuumGreen Lt Ls mass hmass
          (cylinderToTorusEmbed Lt Ls f')
          (cylinderToTorusEmbed Lt Ls g')
      · intro g₁ g₂
        simp [asymTorusContinuumGreen, greenFunctionBilinear_add_right, map_add]
      · intro c g'
        simp [asymTorusContinuumGreen, greenFunctionBilinear_smul_right, map_smul]
    · intro f₁ f₂
      ext g'
      simp [asymTorusContinuumGreen, greenFunctionBilinear_add_left, map_add]
    · intro c f'
      ext g'
      simp [asymTorusContinuumGreen, greenFunctionBilinear_smul_left, map_smul]
  have hB_nonneg : ∀ x : CylinderTestFunction Ls, 0 ≤ B x x := by
    intro x
    dsimp [B]
    simpa [asymTorusContinuumGreen] using
      greenFunctionBilinear_nonneg mass hmass (cylinderToTorusEmbed Lt Ls x)
  have hB_symm : LinearMap.IsSymm B := by
    refine ⟨?_⟩
    intro x y
    dsimp [B]
    simpa [asymTorusContinuumGreen] using
      greenFunctionBilinear_symm mass hmass
        (cylinderToTorusEmbed Lt Ls x) (cylinderToTorusEmbed Lt Ls y)
  have hsq :
      (B f g) ^ 2 ≤ (C * q f * q g) ^ 2 := by
    have hcs := LinearMap.BilinForm.apply_sq_le_of_symm (B := B) hB_nonneg hB_symm f g
    have hdiagf : B f f ≤ C * q f ^ 2 := hdiag Lt hLt f
    have hdiagg : B g g ≤ C * q g ^ 2 := hdiag Lt hLt g
    have hmul :
        (B f f) * (B g g) ≤ (C * q f ^ 2) * (C * q g ^ 2) := by
      exact mul_le_mul hdiagf hdiagg (hB_nonneg g) (by positivity)
    calc
      (B f g) ^ 2 ≤ (B f f) * (B g g) := hcs
      _ ≤ (C * q f ^ 2) * (C * q g ^ 2) := hmul
      _ = (C * q f * q g) ^ 2 := by ring
  have hrhs_nonneg : 0 ≤ C * q f * q g := by
    exact mul_nonneg (mul_nonneg (le_of_lt hC_pos) (apply_nonneg q _)) (apply_nonneg q _)
  change |B f g| ≤ C * q f * q g
  exact abs_le.2 (abs_le_of_sq_le_sq' hsq hrhs_nonneg)

private theorem periodicKernelBilinear_integrand_continuousOn
    (ω Lt : ℝ) [Fact (0 < Lt)]
    (f g : SmoothMap_Circle Lt ℝ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (f p.1 * g p.2) * periodicKernel ω Lt (p.1 - p.2))
      (Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt) := by
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt
  have hf : ContinuousOn (fun p : ℝ × ℝ => f p.1) K := by
    exact (f.continuous.comp continuous_fst).continuousOn
  have hg : ContinuousOn (fun p : ℝ × ℝ => g p.2) K := by
    exact (g.continuous.comp continuous_snd).continuousOn
  have hk : ContinuousOn (fun p : ℝ × ℝ => periodicKernel ω Lt (p.1 - p.2)) K := by
    exact ((continuous_periodicKernel ω Lt).comp
      (continuous_fst.sub continuous_snd)).continuousOn
  simpa [K] using (hf.mul hg).mul hk

private theorem periodicKernelBilinear_integrand_integrable
    (ω Lt : ℝ) [Fact (0 < Lt)]
    (f g : SmoothMap_Circle Lt ℝ) :
    Integrable
      (fun p : ℝ × ℝ => (f p.1 * g p.2) * periodicKernel ω Lt (p.1 - p.2))
      (volume.restrict (Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt)) := by
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt
  have hK_compact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  simpa [K] using
    (periodicKernelBilinear_integrand_continuousOn ω Lt f g).integrableOn_compact hK_compact

private noncomputable def periodicKernelBilinearRightCLM
    (ω Lt : ℝ) [Fact (0 < Lt)] (f : SmoothMap_Circle Lt ℝ) :
    SmoothMap_Circle Lt ℝ →L[ℝ] ℝ := by
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt
  let lm : SmoothMap_Circle Lt ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun g =>
        ∫ p in K, (f p.1 * g p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume
      map_add' := by
        intro g₁ g₂
        have hg₁ := periodicKernelBilinear_integrand_integrable ω Lt f g₁
        have hg₂ := periodicKernelBilinear_integrand_integrable ω Lt f g₂
        have hEq :
            (fun p : ℝ × ℝ =>
              (f p.1 * (g₁ + g₂) p.2) * periodicKernel ω Lt (p.1 - p.2)) =
            fun p =>
              (f p.1 * g₁ p.2) * periodicKernel ω Lt (p.1 - p.2) +
                (f p.1 * g₂ p.2) * periodicKernel ω Lt (p.1 - p.2) := by
          ext p
          simp
          ring
        rw [hEq, MeasureTheory.integral_add hg₁ hg₂]
      map_smul' := by
        intro c g
        have hEq :
            (fun p : ℝ × ℝ =>
              (f p.1 * (c • g) p.2) * periodicKernel ω Lt (p.1 - p.2)) =
            fun p => c * ((f p.1 * g p.2) * periodicKernel ω Lt (p.1 - p.2)) := by
          ext p
          simp
          ring
        rw [hEq, MeasureTheory.integral_const_mul, smul_eq_mul]
        simp }
  refine ⟨lm, ?_⟩
  change Continuous lm
  apply WithSeminorms.continuous_of_isBounded SmoothMap_Circle.smoothCircle_withSeminorms
    (norm_withSeminorms ℝ ℝ)
  intro _
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt
  let A : ℝ × ℝ → ℝ := fun p => f p.1 * periodicKernel ω Lt (p.1 - p.2)
  have hK_compact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hA_cont : ContinuousOn A K := by
    have hf : ContinuousOn (fun p : ℝ × ℝ => f p.1) K := by
      exact (f.continuous.comp continuous_fst).continuousOn
    have hk : ContinuousOn (fun p : ℝ × ℝ => periodicKernel ω Lt (p.1 - p.2)) K := by
      exact ((continuous_periodicKernel ω Lt).comp
        (continuous_fst.sub continuous_snd)).continuousOn
    simpa [A] using hf.mul hk
  obtain ⟨B, hB⟩ := hK_compact.exists_bound_of_continuousOn hA_cont
  have hB_nonneg : 0 ≤ B := by
    have hmem : ((0 : ℝ), (0 : ℝ)) ∈ K := by
      simp [K, le_of_lt (Fact.out : 0 < Lt)]
    exact le_trans (norm_nonneg _) (hB _ hmem)
  refine ⟨{0}, ⟨B * volume.real K, by positivity⟩, fun g => ?_⟩
  simp only [Seminorm.comp_apply, Finset.sup_singleton, NNReal.smul_def,
    Seminorm.smul_apply, NNReal.coe_mk]
  rw [coe_normSeminorm, Real.norm_eq_abs]
  calc
    |∫ p in K, (f p.1 * g p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume|
      = ‖∫ p in K, (f p.1 * g p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ (B * SmoothMap_Circle.sobolevSeminorm 0 g) * volume.real K := by
          apply norm_setIntegral_le_of_norm_le_const hK_compact.measure_lt_top
          intro p hp
          have hp₂ : p.2 ∈ Set.Icc (0 : ℝ) Lt := hp.2
          have hg_bound : ‖g p.2‖ ≤ SmoothMap_Circle.sobolevSeminorm 0 g := by
            simpa [iteratedDeriv_zero] using
              SmoothMap_Circle.norm_iteratedDeriv_le_sobolevSeminorm g 0 hp₂
          have hAp : ‖A p‖ ≤ B := hB p hp
          rw [show f p.1 * g p.2 * periodicKernel ω Lt (p.1 - p.2) = A p * g p.2 by
            dsimp [A]
            ring]
          rw [norm_mul]
          exact mul_le_mul hAp hg_bound (norm_nonneg _) hB_nonneg
    _ = (B * volume.real K) * SmoothMap_Circle.sobolevSeminorm 0 g := by
          ring

@[simp] private theorem periodicKernelBilinearRightCLM_apply
    (ω Lt : ℝ) [Fact (0 < Lt)] (f g : SmoothMap_Circle Lt ℝ) :
    periodicKernelBilinearRightCLM ω Lt f g =
      ∫ p in Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt,
        (f p.1 * g p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume := rfl

private theorem periodicKernelBilinear_fourierBasis_right
    (ω Lt : ℝ) [Fact (0 < Lt)] (hω : 0 < ω)
    (f : SmoothMap_Circle Lt ℝ) (n : ℕ) :
    ∫ p in Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt,
      (f p.1 * (SmoothMap_Circle.fourierBasis (L := Lt) n) p.2) *
        periodicKernel ω Lt (p.1 - p.2) ∂volume =
      (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ *
        SmoothMap_Circle.fourierCoeffReal (L := Lt) n f := by
  let I : Set ℝ := Set.Icc (0 : ℝ) Lt
  let K : Set (ℝ × ℝ) := I ×ˢ I
  let ψ : SmoothMap_Circle Lt ℝ := SmoothMap_Circle.fourierBasis (L := Lt) n
  let H : ℝ → ℝ := fun t => ∫ s in I, periodicKernel ω Lt (t - s) * ψ s
  let G : ℝ × ℝ → ℝ := fun p => (f p.1 * ψ p.2) * periodicKernel ω Lt (p.1 - p.2)
  have hLt : 0 < Lt := Fact.out
  have hG_int : Integrable G ((volume.restrict I).prod (volume.restrict I)) := by
    rw [Measure.prod_restrict I I]
    simpa [I, K, G] using periodicKernelBilinear_integrand_integrable ω Lt f ψ
  have hprod :
      ∫ p in K, G p ∂volume =
        ∫ t, ∫ s, G (t, s) ∂(volume.restrict I) ∂(volume.restrict I) := by
    have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume := rfl
    calc
      ∫ p in K, G p ∂volume
        = ∫ p, G p ∂((volume.restrict I).prod (volume.restrict I)) := by
            rw [Measure.prod_restrict I I]
            simp [K, hvol]
      _ = ∫ t, ∫ s, G (t, s) ∂(volume.restrict I) ∂(volume.restrict I) := by
            exact MeasureTheory.integral_prod G hG_int
  have houter :
      ∫ t, ∫ s, G (t, s) ∂(volume.restrict I) ∂(volume.restrict I) =
        ∫ t, f t * H t ∂(volume.restrict I) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    dsimp [G, H]
    rw [show
      (fun s => (f t * ψ s) * periodicKernel ω Lt (t - s)) =
        fun s => f t * (periodicKernel ω Lt (t - s) * ψ s) by
      ext s
      ring]
    rw [MeasureTheory.integral_const_mul]
  have hH :
      ∀ t ∈ I,
        H t =
          (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ * ψ t := by
    intro t ht
    dsimp [H]
    rw [integral_Icc_eq_intervalIntegral (a := 0) (b := Lt) (le_of_lt hLt)]
    · simpa [ψ, SmoothMap_Circle.fourierBasis_apply] using
        integral_periodicKernel_shift_mul_fourierBasisFun ω Lt hω ht n
    · exact (((continuous_periodicKernel ω Lt).comp
        (continuous_const.sub continuous_id)).mul ψ.continuous).intervalIntegrable _ _
  calc
    ∫ p in Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt,
        (f p.1 * (SmoothMap_Circle.fourierBasis (L := Lt) n) p.2) *
          periodicKernel ω Lt (p.1 - p.2) ∂volume
      = ∫ t, f t * H t ∂(volume.restrict I) := by
          simpa [I, K, ψ, G] using hprod.trans houter
    _ = ∫ t,
          f t *
            ((HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ *
              ψ t) ∂(volume.restrict I) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
            rw [hH t ht]
    _ = (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ *
          ∫ t, f t * ψ t ∂(volume.restrict I) := by
            rw [show
              (fun t =>
                f t *
                  ((HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ *
                    ψ t)) =
                fun t =>
                  (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ *
                    (f t * ψ t) by
              ext t
              ring]
            rw [MeasureTheory.integral_const_mul]
    _ = (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ *
          SmoothMap_Circle.fourierCoeffReal (L := Lt) n f := by
            simp [I, ψ, SmoothMap_Circle.fourierCoeffReal, SmoothMap_Circle.fourierBasis_apply]

private theorem greenFunctionBilinear_basis_right
    (ω Lt : ℝ) [Fact (0 < Lt)] (hω : 0 < ω)
    (f : SmoothMap_Circle Lt ℝ) (n : ℕ) :
    greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω f (DyninMityaginSpace.basis n) =
      (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ *
        DyninMityaginSpace.coeff n f := by
  unfold greenFunctionBilinear
  rw [tsum_eq_single n]
  · have hcoeff :
        DyninMityaginSpace.coeff n (DyninMityaginSpace.basis n : SmoothMap_Circle Lt ℝ) = 1 := by
        simpa using
          DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis (E := SmoothMap_Circle Lt ℝ) n n
    change DyninMityaginSpace.coeff n f *
        DyninMityaginSpace.coeff n (DyninMityaginSpace.basis n : SmoothMap_Circle Lt ℝ) /
          (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2) =
      (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ *
        DyninMityaginSpace.coeff n f
    rw [hcoeff]
    ring
  · intro m hm
    have hzero :
        DyninMityaginSpace.coeff m (DyninMityaginSpace.basis n : SmoothMap_Circle Lt ℝ) = 0 := by
      simpa [hm] using
        DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis (E := SmoothMap_Circle Lt ℝ) m n
    change DyninMityaginSpace.coeff m f *
        DyninMityaginSpace.coeff m (DyninMityaginSpace.basis n : SmoothMap_Circle Lt ℝ) /
          (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) m + ω ^ 2) = 0
    rw [hzero]
    simp

private theorem greenFunctionBilinear_fourierBasis_right
    (ω Lt : ℝ) [Fact (0 < Lt)] (hω : 0 < ω)
    (f : SmoothMap_Circle Lt ℝ) (n : ℕ) :
    greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω
      f (SmoothMap_Circle.fourierBasis (L := Lt) n) =
      (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ *
        SmoothMap_Circle.fourierCoeffReal (L := Lt) n f := by
  rw [← dm_basis_eq_fourierBasis (L := Lt) n]
  rw [greenFunctionBilinear_basis_right ω Lt hω f n,
    smoothCircle_coeff_eq_fourierCoeffReal (Lt := Lt) n f]

private theorem greenFunctionBilinear_fourierBasis_right_eq_periodicKernelBilinear
    (ω Lt : ℝ) [Fact (0 < Lt)] (hω : 0 < ω)
    (f : SmoothMap_Circle Lt ℝ) (n : ℕ) :
    greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω
      f (SmoothMap_Circle.fourierBasis (L := Lt) n) =
    ∫ p in Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt,
      (f p.1 * (SmoothMap_Circle.fourierBasis (L := Lt) n) p.2) *
        periodicKernel ω Lt (p.1 - p.2) ∂volume := by
  rw [greenFunctionBilinear_fourierBasis_right ω Lt hω f n,
    periodicKernelBilinear_fourierBasis_right ω Lt hω f n]

private theorem greenFunctionBilinear_eq_periodicKernel_integralOn_square
    (ω Lt : ℝ) [Fact (0 < Lt)] (hω : 0 < ω)
    (f g : SmoothMap_Circle Lt ℝ) :
    greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω f g =
      ∫ p in Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt,
        (f p.1 * g p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume := by
  let Φ := periodicKernelBilinearRightCLM ω Lt f
  have hgreen :
      greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω f g =
        ∑' n : ℕ,
          DyninMityaginSpace.coeff n g *
            greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω
              f (DyninMityaginSpace.basis n) := by
    calc
      greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω f g
        = greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω g f := by
            rw [greenFunctionBilinear_symm]
      _ = ∑' n : ℕ,
            DyninMityaginSpace.coeff n g *
              greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω
                (DyninMityaginSpace.basis n) f := by
            exact DyninMityaginSpace.expansion (greenCLM_left ω hω f) g
      _ = ∑' n : ℕ,
            DyninMityaginSpace.coeff n g *
              greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω
                f (DyninMityaginSpace.basis n) := by
            apply tsum_congr
            intro n
            rw [greenFunctionBilinear_symm]
  have hkernel :
      ∫ p in Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt,
        (f p.1 * g p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume =
      ∑' n : ℕ, DyninMityaginSpace.coeff n g * Φ (DyninMityaginSpace.basis n) := by
    simpa [Φ] using DyninMityaginSpace.expansion Φ g
  calc
    greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω f g
      = ∑' n : ℕ,
          DyninMityaginSpace.coeff n g *
            greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω
              f (DyninMityaginSpace.basis n) := hgreen
    _ = ∑' n : ℕ, DyninMityaginSpace.coeff n g * Φ (DyninMityaginSpace.basis n) := by
          apply tsum_congr
          intro n
          rw [periodicKernelBilinearRightCLM_apply, dm_basis_eq_fourierBasis (L := Lt) n]
          exact congrArg
            (fun z =>
              DyninMityaginSpace.coeff n g * z)
            (greenFunctionBilinear_fourierBasis_right_eq_periodicKernelBilinear
              ω Lt hω f n)
    _ = ∫ p in Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt,
          (f p.1 * g p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume := by
          symm
          exact hkernel

private theorem periodizeCLM_eq_on_large_symmetric_halfPeriod
    {Lt : ℝ} [Fact (0 < Lt)]
    (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (hLt_large : 2 * T < Lt) :
    ∀ t ∈ Set.Icc (-Lt / 2) (Lt / 2), (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t = h t := by
  intro t ht
  by_cases ht_nonneg : 0 ≤ t
  · have htI : t ∈ Set.Icc (0 : ℝ) (Lt / 2) := ⟨ht_nonneg, ht.2⟩
    exact periodizeCLM_eq_on_large_period
      (L := Lt) h T hT hsupp (by linarith) t htI
  · have ht_neg : t < 0 := lt_of_not_ge ht_nonneg
    have href_supp : ∀ u, T < |u| → schwartzReflection h u = 0 := by
      intro u hu
      simpa [schwartzReflection_apply, abs_neg] using hsupp (-u) (by simpa [abs_neg] using hu)
    have htI : -t ∈ Set.Icc (0 : ℝ) (Lt / 2) := by
      constructor
      · linarith
      · linarith [ht.1]
    have href :=
      periodizeCLM_eq_on_large_period
        (L := Lt) (schwartzReflection h) T hT href_supp (by linarith) (-t) htI
    have hcomm :
        (@periodizeCLM Lt ‹Fact (0 < Lt)› (schwartzReflection h)).toFun (-t) =
          (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t := by
      simpa [circleReflection] using
        congrArg (fun f : SmoothMap_Circle Lt ℝ => f (-t))
          (periodizeCLM_comp_schwartzReflection (L := Lt) h)
    calc
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t
        = (@periodizeCLM Lt ‹Fact (0 < Lt)› (schwartzReflection h)).toFun (-t) := by
            symm
            exact hcomm
      _ = (schwartzReflection h) (-t) := href
      _ = h t := by simp [schwartzReflection_apply]

private theorem periodizeCLM_eq_sub_period_on_upper_strip
    {Lt : ℝ} [Fact (0 < Lt)]
    (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (hLt_large : 2 * T < Lt) :
    ∀ t ∈ Set.Icc (Lt / 2) Lt, (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t = h (t - Lt) := by
  intro t ht
  have hper : (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t =
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun (t - Lt) := by
    simpa [sub_eq_add_neg, add_assoc] using
      ((@periodizeCLM Lt ‹Fact (0 < Lt)› h).periodic' (t - Lt))
  have ht_sub : t - Lt ∈ Set.Icc (-Lt / 2) (Lt / 2) := by
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  calc
    (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t
      = (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun (t - Lt) := hper
    _ = h (t - Lt) :=
      periodizeCLM_eq_on_large_symmetric_halfPeriod h T hT hsupp hLt_large (t - Lt) ht_sub

private theorem periodizeCLM_eq_zero_on_middle_open_strip
    {Lt : ℝ} [Fact (0 < Lt)]
    (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (hLt_large : 4 * T < Lt) :
    ∀ t ∈ Set.Ioo T (Lt - T), (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t = 0 := by
  intro t ht
  by_cases hhalf : t ≤ Lt / 2
  · have htI : t ∈ Set.Icc (0 : ℝ) (Lt / 2) := by
      constructor
      · linarith [hT, ht.1]
      · exact hhalf
    have hEq :
        (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t = h t :=
      periodizeCLM_eq_on_large_period
        (L := Lt) h T hT hsupp (by linarith [hLt_large]) t htI
    have ht_abs : T < |t| := by
      have ht_pos : 0 < t := by
        linarith [hT, ht.1]
      rw [abs_of_pos ht_pos]
      exact ht.1
    simpa [hEq] using hsupp t ht_abs
  · have hhalf_lt : Lt / 2 < t := lt_of_not_ge hhalf
    have htI : t ∈ Set.Icc (Lt / 2) Lt := by
      constructor
      · exact le_of_lt hhalf_lt
      · linarith [ht.2]
    have hEq :
        (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t = h (t - Lt) :=
      periodizeCLM_eq_sub_period_on_upper_strip h T hT hsupp (by linarith [hLt_large]) t htI
    have ht_sub_neg : t - Lt < 0 := by
      linarith [ht.2]
    have ht_abs : T < |t - Lt| := by
      rw [abs_of_neg ht_sub_neg]
      linarith [ht.2]
    simpa [hEq] using hsupp (t - Lt) ht_abs

private theorem intervalIntegral_mul_periodizeCLM_eq_zero_on_middle_strip
    {Lt : ℝ} [Fact (0 < Lt)]
    (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (hLt_large : 4 * T < Lt)
    (φ : ℝ → ℝ) :
    ∫ s in T..(Lt - T), (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun s * φ s = 0 := by
  apply intervalIntegral.integral_zero_ae
  have h_ne : ∀ᵐ s : ℝ ∂volume, s ≠ Lt - T := Measure.ae_ne volume (Lt - T)
  filter_upwards [h_ne] with s hs_ne hs_mem
  have hT_le : T ≤ Lt - T := by
    linarith [hLt_large]
  have hsIoc : s ∈ Set.Ioc T (Lt - T) := by
    simpa [Set.uIoc_of_le hT_le] using hs_mem
  have hsIoo : s ∈ Set.Ioo T (Lt - T) := ⟨hsIoc.1, lt_of_le_of_ne hsIoc.2 hs_ne⟩
  simp [periodizeCLM_eq_zero_on_middle_open_strip h T hT hsupp hLt_large s hsIoo]

private theorem periodicKernel_sub_period_eq
    (ω Lt : ℝ) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) Lt) :
    periodicKernel ω Lt (u - Lt) = periodicKernel ω Lt u := by
  rw [show u - Lt = -(Lt - u) by ring, periodicKernel_neg]
  exact periodicKernel_sub_eq ω Lt hu

private theorem periodizeCLM_intervalIntegral_eq_supportInterval_pos
    (ω Lt : ℝ) [Fact (0 < Lt)]
    (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (hLt_large : 4 * T < Lt)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ s in (0 : ℝ)..Lt,
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun s * periodicKernel ω Lt (t - s) =
    ∫ u in (-T)..T, h u * periodicKernel ω Lt (t - u) := by
  let per : SmoothMap_Circle Lt ℝ := @periodizeCLM Lt ‹Fact (0 < Lt)› h
  let f : ℝ → ℝ := fun s => per.toFun s * periodicKernel ω Lt (t - s)
  let g : ℝ → ℝ := fun u => h u * periodicKernel ω Lt (t - u)
  have hf_cont : Continuous f := by
    dsimp [f]
    exact per.continuous.mul
      ((continuous_periodicKernel ω Lt).comp (continuous_const.sub continuous_id))
  have hg_cont : Continuous g := by
    dsimp [g]
    exact h.continuous.mul
      ((continuous_periodicKernel ω Lt).comp (continuous_const.sub continuous_id))
  have hf_int₁ : IntervalIntegrable f volume (0 : ℝ) T := hf_cont.intervalIntegrable _ _
  have hf_int₂ : IntervalIntegrable f volume T (Lt - T) := hf_cont.intervalIntegrable _ _
  have hf_int₃ : IntervalIntegrable f volume (Lt - T) Lt := hf_cont.intervalIntegrable _ _
  have hg_int₁ : IntervalIntegrable g volume (-T) 0 := hg_cont.intervalIntegrable _ _
  have hg_int₂ : IntervalIntegrable g volume (0 : ℝ) T := hg_cont.intervalIntegrable _ _
  have hsplit_left :
      (∫ s in (0 : ℝ)..(Lt - T), f s) =
        (∫ s in (0 : ℝ)..T, f s) + ∫ s in T..(Lt - T), f s := by
    exact (intervalIntegral.integral_add_adjacent_intervals hf_int₁ hf_int₂).symm
  have hsplit :
      (∫ s in (0 : ℝ)..Lt, f s) =
        (∫ s in (0 : ℝ)..(Lt - T), f s) + ∫ s in (Lt - T)..Lt, f s := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable 0 (Lt - T)) hf_int₃).symm
  have hI₁ :
      ∫ s in (0 : ℝ)..T, f s = ∫ s in (0 : ℝ)..T, g s := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := by
      simpa [Set.uIcc_of_le (le_of_lt hT)] using hs
    have hsI : s ∈ Set.Icc (-T) T := by
      exact ⟨by linarith [hT, hsIcc.1], hsIcc.2⟩
    have hper :
        per.toFun s = h s :=
      periodizeCLM_eq_on_symmetric_large_period
        (L := Lt) h T hT hsupp (by linarith [hLt_large]) s hsI
    simp [f, g, hper]
  have hI_mid_zero : ∫ s in T..(Lt - T), f s = 0 := by
    simpa [f] using
      intervalIntegral_mul_periodizeCLM_eq_zero_on_middle_strip
        h T hT hsupp hLt_large (fun s => periodicKernel ω Lt (t - s))
  have hI₂ :
      ∫ s in (Lt - T)..Lt, f s = ∫ u in (-T)..0, g u := by
    calc
      ∫ s in (Lt - T)..Lt, f s = ∫ u in (-T)..0, f (u + Lt) := by
            have hshift :=
              intervalIntegral.integral_comp_add_right (f := f) (a := -T) (b := 0) Lt
            symm
            convert hshift using 1
            ring
      _ = ∫ u in (-T)..0, g u := by
            apply intervalIntegral.integral_congr
            intro u hu
            have huIcc : u ∈ Set.Icc (-T) 0 := by
              simpa [Set.uIcc_of_le (show (-T : ℝ) ≤ 0 by linarith [hT])] using hu
            have huStrip : u + Lt ∈ Set.Icc (Lt / 2) Lt := by
              constructor
              · linarith [huIcc.1, hLt_large]
              · linarith [huIcc.2]
            have hper :
                per.toFun (u + Lt) = h u := by
              simpa using
                periodizeCLM_eq_sub_period_on_upper_strip
                  h T hT hsupp (by linarith [hLt_large]) (u + Lt) huStrip
            have huKer : t - u ∈ Set.Icc (0 : ℝ) Lt := by
              constructor
              · linarith [ht.1, huIcc.2]
              · linarith [ht.2, huIcc.1, hLt_large]
            have hker :
                periodicKernel ω Lt (t - (u + Lt)) = periodicKernel ω Lt (t - u) := by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                periodicKernel_sub_period_eq ω Lt huKer
            simp [f, g, hper, hker]
  calc
    ∫ s in (0 : ℝ)..Lt, (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun s *
        periodicKernel ω Lt (t - s)
      = ∫ s in (0 : ℝ)..Lt, f s := by simp [f, per]
    _ = (∫ s in (0 : ℝ)..(Lt - T), f s) + ∫ s in (Lt - T)..Lt, f s := hsplit
    _ = ((∫ s in (0 : ℝ)..T, f s) + ∫ s in T..(Lt - T), f s) + ∫ s in (Lt - T)..Lt, f s := by
          rw [hsplit_left]
    _ = (∫ s in (0 : ℝ)..T, f s) + ∫ s in (Lt - T)..Lt, f s := by
          rw [hI_mid_zero]
          ring
    _ = (∫ s in (0 : ℝ)..T, g s) + ∫ u in (-T)..0, g u := by
          rw [hI₁, hI₂]
    _ = ∫ u in (-T)..T, g u := by
          simpa [add_comm] using intervalIntegral.integral_add_adjacent_intervals hg_int₁ hg_int₂
    _ = ∫ u in (-T)..T, h u * periodicKernel ω Lt (t - u) := by
          simp [g]

private theorem periodizeCLM_intervalIntegral_eq_supportInterval_upper
    (ω Lt : ℝ) [Fact (0 < Lt)]
    (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (hLt_large : 4 * T < Lt)
    {t : ℝ} (ht : t ∈ Set.Icc (-T) 0) :
    ∫ s in (0 : ℝ)..Lt,
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun s *
        periodicKernel ω Lt ((t + Lt) - s) =
    ∫ u in (-T)..T, h u * periodicKernel ω Lt (t - u) := by
  let per : SmoothMap_Circle Lt ℝ := @periodizeCLM Lt ‹Fact (0 < Lt)› h
  let f : ℝ → ℝ := fun s => per.toFun s * periodicKernel ω Lt ((t + Lt) - s)
  let g : ℝ → ℝ := fun u => h u * periodicKernel ω Lt (t - u)
  have hf_cont : Continuous f := by
    dsimp [f]
    exact per.continuous.mul ((continuous_periodicKernel ω Lt).comp
      (continuous_const.sub continuous_id))
  have hg_cont : Continuous g := by
    dsimp [g]
    exact h.continuous.mul
      ((continuous_periodicKernel ω Lt).comp (continuous_const.sub continuous_id))
  have hf_int₁ : IntervalIntegrable f volume (0 : ℝ) T := hf_cont.intervalIntegrable _ _
  have hf_int₂ : IntervalIntegrable f volume T (Lt - T) := hf_cont.intervalIntegrable _ _
  have hf_int₃ : IntervalIntegrable f volume (Lt - T) Lt := hf_cont.intervalIntegrable _ _
  have hg_int₁ : IntervalIntegrable g volume (-T) 0 := hg_cont.intervalIntegrable _ _
  have hg_int₂ : IntervalIntegrable g volume (0 : ℝ) T := hg_cont.intervalIntegrable _ _
  have hsplit_left :
      (∫ s in (0 : ℝ)..(Lt - T), f s) =
        (∫ s in (0 : ℝ)..T, f s) + ∫ s in T..(Lt - T), f s := by
    exact (intervalIntegral.integral_add_adjacent_intervals hf_int₁ hf_int₂).symm
  have hsplit :
      (∫ s in (0 : ℝ)..Lt, f s) =
        (∫ s in (0 : ℝ)..(Lt - T), f s) + ∫ s in (Lt - T)..Lt, f s := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable 0 (Lt - T)) hf_int₃).symm
  have hI₁ :
      ∫ s in (0 : ℝ)..T, f s = ∫ s in (0 : ℝ)..T, g s := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := by
      simpa [Set.uIcc_of_le (le_of_lt hT)] using hs
    have hsI : s ∈ Set.Icc (-T) T := by
      exact ⟨by linarith [hT, hsIcc.1], hsIcc.2⟩
    have hper :
        per.toFun s = h s :=
      periodizeCLM_eq_on_symmetric_large_period
        (L := Lt) h T hT hsupp (by linarith [hLt_large]) s hsI
    have hsKer : s - t ∈ Set.Icc (0 : ℝ) Lt := by
      constructor
      · linarith [hsIcc.1, ht.2]
      · linarith [hsI.2, ht.1, hLt_large]
    have hker :
        periodicKernel ω Lt ((t + Lt) - s) = periodicKernel ω Lt (t - s) := by
      calc
        periodicKernel ω Lt ((t + Lt) - s)
          = periodicKernel ω Lt (Lt - (s - t)) := by congr 1; ring
        _ = periodicKernel ω Lt (s - t) := periodicKernel_sub_eq ω Lt hsKer
        _ = periodicKernel ω Lt (t - s) := by
              rw [show s - t = -(t - s) by ring, periodicKernel_neg]
    simp [f, g, hper, hker]
  have hI_mid_zero : ∫ s in T..(Lt - T), f s = 0 := by
    simpa [f] using
      intervalIntegral_mul_periodizeCLM_eq_zero_on_middle_strip
        h T hT hsupp hLt_large (fun s => periodicKernel ω Lt ((t + Lt) - s))
  have hI₂ :
      ∫ s in (Lt - T)..Lt, f s = ∫ u in (-T)..0, g u := by
    calc
      ∫ s in (Lt - T)..Lt, f s = ∫ u in (-T)..0, f (u + Lt) := by
            have hshift :=
              intervalIntegral.integral_comp_add_right (f := f) (a := -T) (b := 0) Lt
            symm
            convert hshift using 1
            ring
      _ = ∫ u in (-T)..0, g u := by
            apply intervalIntegral.integral_congr
            intro u hu
            have huIcc : u ∈ Set.Icc (-T) 0 := by
              simpa [Set.uIcc_of_le (show (-T : ℝ) ≤ 0 by linarith [hT])] using hu
            have huStrip : u + Lt ∈ Set.Icc (Lt / 2) Lt := by
              constructor
              · linarith [huIcc.1, hLt_large]
              · linarith [huIcc.2]
            have hper :
                per.toFun (u + Lt) = h u := by
              simpa using
                periodizeCLM_eq_sub_period_on_upper_strip
                  h T hT hsupp (by linarith [hLt_large]) (u + Lt) huStrip
            simp [f, g, hper]
  calc
    ∫ s in (0 : ℝ)..Lt,
        (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun s *
          periodicKernel ω Lt ((t + Lt) - s)
      = ∫ s in (0 : ℝ)..Lt, f s := by simp [f, per]
    _ = (∫ s in (0 : ℝ)..(Lt - T), f s) + ∫ s in (Lt - T)..Lt, f s := hsplit
    _ = ((∫ s in (0 : ℝ)..T, f s) + ∫ s in T..(Lt - T), f s) + ∫ s in (Lt - T)..Lt, f s := by
          rw [hsplit_left]
    _ = (∫ s in (0 : ℝ)..T, f s) + ∫ s in (Lt - T)..Lt, f s := by
          rw [hI_mid_zero]
          ring
    _ = (∫ s in (0 : ℝ)..T, g s) + ∫ u in (-T)..0, g u := by
          rw [hI₁, hI₂]
    _ = ∫ u in (-T)..T, g u := by
          simpa [add_comm] using intervalIntegral.integral_add_adjacent_intervals hg_int₁ hg_int₂
    _ = ∫ u in (-T)..T, h u * periodicKernel ω Lt (t - u) := by
          simp [g]

private theorem greenFunctionBilinear_eq_periodicKernel_integralOn_compactDiffBox
    (ω Lt : ℝ) [Fact (0 < Lt)] (hω : 0 < ω)
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ) (hT : 0 < T)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0)
    (hLt_large : 4 * T < Lt) :
    greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h₁)
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h₂) =
    ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
      (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume := by
  let per₁ : SmoothMap_Circle Lt ℝ := @periodizeCLM Lt ‹Fact (0 < Lt)› h₁
  let per₂ : SmoothMap_Circle Lt ℝ := @periodizeCLM Lt ‹Fact (0 < Lt)› h₂
  let I₀ : Set ℝ := Set.Icc (0 : ℝ) Lt
  let I : Set ℝ := Set.Icc (-T) T
  let K : Set (ℝ × ℝ) := I ×ˢ I
  let G₀ : ℝ × ℝ → ℝ := fun p =>
    (per₁ p.1 * per₂ p.2) * periodicKernel ω Lt (p.1 - p.2)
  let F : ℝ → ℝ := fun t =>
    ∫ s in (0 : ℝ)..Lt, per₂ s * periodicKernel ω Lt (t - s)
  let H : ℝ → ℝ := fun t => per₁ t * F t
  let Fbox : ℝ → ℝ := fun t =>
    ∫ s in (-T)..T, h₂ s * periodicKernel ω Lt (t - s)
  let J : ℝ → ℝ := fun t => h₁ t * Fbox t
  have hLt_pos : 0 < Lt := Fact.out
  have hG₀_int : Integrable G₀ ((volume.restrict I₀).prod (volume.restrict I₀)) := by
    rw [Measure.prod_restrict I₀ I₀]
    simpa [I₀, G₀, per₁, per₂] using
      periodicKernelBilinear_integrand_integrable ω Lt per₁ per₂
  have hprod :
      ∫ p in I₀ ×ˢ I₀, G₀ p ∂volume =
        ∫ t, ∫ s, G₀ (t, s) ∂(volume.restrict I₀) ∂(volume.restrict I₀) := by
    have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume := rfl
    calc
      ∫ p in I₀ ×ˢ I₀, G₀ p ∂volume
        = ∫ p, G₀ p ∂((volume.restrict I₀).prod (volume.restrict I₀)) := by
            rw [Measure.prod_restrict I₀ I₀]
            simp [I₀, hvol]
      _ = ∫ t, ∫ s, G₀ (t, s) ∂(volume.restrict I₀) ∂(volume.restrict I₀) := by
            exact MeasureTheory.integral_prod G₀ hG₀_int
  have hparam_cont :
      Continuous (Function.uncurry (fun t s : ℝ =>
        per₂ s * periodicKernel ω Lt (t - s))) := by
    simpa using
      ((per₂.continuous.comp continuous_snd).mul
        ((continuous_periodicKernel ω Lt).comp (continuous_fst.sub continuous_snd)))
  have hF_cont : Continuous F := by
    simpa [F] using
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := volume) (f := fun t s : ℝ => per₂ s * periodicKernel ω Lt (t - s))
        hparam_cont (0 : ℝ) Lt
  have hH_cont : Continuous H := by
    simpa [H] using per₁.continuous.mul hF_cont
  have houter_sq :
      ∫ p in I₀ ×ˢ I₀, G₀ p ∂volume = ∫ t in (0 : ℝ)..Lt, H t := by
    calc
      ∫ p in I₀ ×ˢ I₀, G₀ p ∂volume
        = ∫ t, ∫ s, G₀ (t, s) ∂(volume.restrict I₀) ∂(volume.restrict I₀) := hprod
      _ = ∫ t, H t ∂(volume.restrict I₀) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
            dsimp [H, F, G₀]
            rw [integral_Icc_eq_intervalIntegral (a := 0) (b := Lt) (le_of_lt hLt_pos)]
            · rw [show
                (fun s => (per₁ t * per₂ s) * periodicKernel ω Lt (t - s)) =
                  fun s => per₁ t * (per₂ s * periodicKernel ω Lt (t - s)) by
                ext s
                ring]
              rw [intervalIntegral.integral_const_mul]
            · simpa [mul_assoc] using
                (((per₂.continuous).mul
                  ((continuous_periodicKernel ω Lt).comp
                    (continuous_const.sub continuous_id))).intervalIntegrable
                  (μ := volume) (0 : ℝ) Lt).const_mul (per₁ t)
      _ = ∫ t in I₀, H t ∂volume := by
            simp [I₀]
      _ = ∫ t in (0 : ℝ)..Lt, H t := by
            simpa [I₀] using
              integral_Icc_eq_intervalIntegral (a := 0) (b := Lt) (le_of_lt hLt_pos)
                (hH_cont.intervalIntegrable _ _)
  have hH_int₁ : IntervalIntegrable H volume (0 : ℝ) T := hH_cont.intervalIntegrable _ _
  have hH_int₂ : IntervalIntegrable H volume T (Lt - T) := hH_cont.intervalIntegrable _ _
  have hH_int₃ : IntervalIntegrable H volume (Lt - T) Lt := hH_cont.intervalIntegrable _ _
  have hH_split_left :
      (∫ t in (0 : ℝ)..(Lt - T), H t) =
        (∫ t in (0 : ℝ)..T, H t) + ∫ t in T..(Lt - T), H t := by
    exact (intervalIntegral.integral_add_adjacent_intervals hH_int₁ hH_int₂).symm
  have hH_split :
      (∫ t in (0 : ℝ)..Lt, H t) =
        (∫ t in (0 : ℝ)..(Lt - T), H t) + ∫ t in (Lt - T)..Lt, H t := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hH_cont.intervalIntegrable 0 (Lt - T)) hH_int₃).symm
  have houter_pos :
      ∫ t in (0 : ℝ)..T, H t = ∫ t in (0 : ℝ)..T, J t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := by
      simpa [Set.uIcc_of_le (le_of_lt hT)] using ht
    have htI : t ∈ Set.Icc (-T) T := by
      exact ⟨by linarith [hT, htIcc.1], htIcc.2⟩
    have hper :
        per₁ t = h₁ t :=
      periodizeCLM_eq_on_symmetric_large_period
        (L := Lt) h₁ T hT hsupp₁ (by linarith [hLt_large]) t htI
    have hinner :
        ∫ s in (0 : ℝ)..Lt, per₂ s * periodicKernel ω Lt (t - s) =
          ∫ u in (-T)..T, h₂ u * periodicKernel ω Lt (t - u) := by
      simpa [per₂] using
        periodizeCLM_intervalIntegral_eq_supportInterval_pos
          ω Lt h₂ T hT hsupp₂ hLt_large htIcc
    dsimp [H, J, F, Fbox]
    rw [hper, hinner]
  have houter_mid_zero : ∫ t in T..(Lt - T), H t = 0 := by
    simpa [H, F, per₁] using
      intervalIntegral_mul_periodizeCLM_eq_zero_on_middle_strip
        h₁ T hT hsupp₁ hLt_large F
  have houter_upper :
      ∫ t in (Lt - T)..Lt, H t = ∫ u in (-T)..0, J u := by
    calc
      ∫ t in (Lt - T)..Lt, H t = ∫ u in (-T)..0, H (u + Lt) := by
            have hshift :=
              intervalIntegral.integral_comp_add_right (f := H) (a := -T) (b := 0) Lt
            symm
            convert hshift using 1
            ring
      _ = ∫ u in (-T)..0, J u := by
            apply intervalIntegral.integral_congr
            intro u hu
            have huIcc : u ∈ Set.Icc (-T) 0 := by
              simpa [Set.uIcc_of_le (show (-T : ℝ) ≤ 0 by linarith [hT])] using hu
            have huStrip : u + Lt ∈ Set.Icc (Lt / 2) Lt := by
              constructor
              · linarith [huIcc.1, hLt_large]
              · linarith [huIcc.2]
            have hper :
                per₁ (u + Lt) = h₁ u := by
              simpa using
                periodizeCLM_eq_sub_period_on_upper_strip
                  h₁ T hT hsupp₁ (by linarith [hLt_large]) (u + Lt) huStrip
            have hinner :
                ∫ s in (0 : ℝ)..Lt, per₂ s * periodicKernel ω Lt ((u + Lt) - s) =
                  ∫ u_1 in (-T)..T, h₂ u_1 * periodicKernel ω Lt (u - u_1) := by
              simpa [per₂] using
                periodizeCLM_intervalIntegral_eq_supportInterval_upper
                  ω Lt h₂ T hT hsupp₂ hLt_large huIcc
            dsimp [H, J, F, Fbox]
            rw [hper, hinner]
  have hbox_param_cont :
      Continuous (Function.uncurry (fun t s : ℝ =>
        h₂ s * periodicKernel ω Lt (t - s))) := by
    simpa using
      ((h₂.continuous.comp continuous_snd).mul
        ((continuous_periodicKernel ω Lt).comp (continuous_fst.sub continuous_snd)))
  have hFbox_cont : Continuous Fbox := by
    simpa [Fbox] using
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := volume) (f := fun t s : ℝ => h₂ s * periodicKernel ω Lt (t - s))
        hbox_param_cont (-T) T
  have hJ_cont : Continuous J := by
    simpa [J] using h₁.continuous.mul hFbox_cont
  have hJ_int₁ : IntervalIntegrable J volume (-T) 0 := hJ_cont.intervalIntegrable _ _
  have hJ_int₂ : IntervalIntegrable J volume (0 : ℝ) T := hJ_cont.intervalIntegrable _ _
  have hinterval :
      ∫ t in (0 : ℝ)..Lt, H t = ∫ t in (-T)..T, J t := by
    calc
      ∫ t in (0 : ℝ)..Lt, H t
        = (∫ t in (0 : ℝ)..(Lt - T), H t) + ∫ t in (Lt - T)..Lt, H t := hH_split
      _ = ((∫ t in (0 : ℝ)..T, H t) + ∫ t in T..(Lt - T), H t) +
            ∫ t in (Lt - T)..Lt, H t := by
              rw [hH_split_left]
      _ = (∫ t in (0 : ℝ)..T, H t) + ∫ t in (Lt - T)..Lt, H t := by
            rw [houter_mid_zero]
            ring
      _ = (∫ t in (0 : ℝ)..T, J t) + ∫ u in (-T)..0, J u := by
            rw [houter_pos, houter_upper]
      _ = ∫ u in (-T)..T, J u := by
            simpa [add_comm] using
              intervalIntegral.integral_add_adjacent_intervals hJ_int₁ hJ_int₂
  have hG_cont : ContinuousOn
      (fun p : ℝ × ℝ =>
        (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2)) K := by
    have hh₁ : ContinuousOn (fun p : ℝ × ℝ => h₁ p.1) K := by
      exact (h₁.continuous.comp continuous_fst).continuousOn
    have hh₂ : ContinuousOn (fun p : ℝ × ℝ => h₂ p.2) K := by
      exact (h₂.continuous.comp continuous_snd).continuousOn
    have hk : ContinuousOn (fun p : ℝ × ℝ => periodicKernel ω Lt (p.1 - p.2)) K := by
      exact ((continuous_periodicKernel ω Lt).comp (continuous_fst.sub continuous_snd)).continuousOn
    simpa using (hh₁.mul hh₂).mul hk
  have hG_int :
      Integrable
        (fun p : ℝ × ℝ =>
          (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2))
        ((volume.restrict I).prod (volume.restrict I)) := by
    have hK_compact : IsCompact K := by
      simpa [K, I] using
        (isCompact_Icc.prod isCompact_Icc : IsCompact (Set.Icc (-T) T ×ˢ Set.Icc (-T) T))
    have hG_int_on :
        IntegrableOn
          (fun p : ℝ × ℝ =>
            (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2))
          K volume :=
      hG_cont.integrableOn_compact hK_compact
    rw [IntegrableOn] at hG_int_on
    rw [Measure.prod_restrict I I]
    have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume := rfl
    simpa [K, hvol] using hG_int_on
  have hbox :
      ∫ t in (-T)..T, J t =
        ∫ p in K, (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume := by
    calc
      ∫ t in (-T)..T, J t
        = ∫ t in I, J t ∂volume := by
            symm
            exact integral_Icc_eq_intervalIntegral (a := -T) (b := T) (by linarith [hT])
              (hJ_cont.intervalIntegrable _ _)
      _ = ∫ t, J t ∂(volume.restrict I) := by
            simp [I]
      _ = ∫ t, ∫ s,
            (h₁ t * h₂ s) * periodicKernel ω Lt (t - s)
              ∂(volume.restrict I) ∂(volume.restrict I) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
              dsimp [J, Fbox]
              rw [integral_Icc_eq_intervalIntegral (a := -T) (b := T) (by linarith [hT])]
              · symm
                rw [← intervalIntegral.integral_const_mul]
                apply intervalIntegral.integral_congr
                intro s hs
                ring
              · simpa [mul_assoc] using
                  (((h₂.continuous).mul
                    ((continuous_periodicKernel ω Lt).comp
                      (continuous_const.sub continuous_id))).intervalIntegrable
                    (μ := volume) (-T) T).const_mul (h₁ t)
      _ = ∫ p,
            ((fun p : ℝ × ℝ =>
              (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2)) p)
            ∂((volume.restrict I).prod (volume.restrict I)) := by
              symm
              exact MeasureTheory.integral_prod
                (fun p : ℝ × ℝ =>
                  (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2))
                hG_int
      _ = ∫ p in K, (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume := by
            rw [Measure.prod_restrict I I]
            have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume := rfl
            simp [K, hvol]
  calc
    greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω per₁ per₂
      = ∫ p in I₀ ×ˢ I₀, G₀ p ∂volume := by
          simpa [I₀, G₀, per₁, per₂] using
            greenFunctionBilinear_eq_periodicKernel_integralOn_square ω Lt hω per₁ per₂
    _ = ∫ t in (0 : ℝ)..Lt, H t := houter_sq
    _ = ∫ t in (-T)..T, J t := hinterval
    _ = ∫ p in K, (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume := hbox
    _ = ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume := by
            simp [K, I]

private theorem periodizedSchwartz_mul_periodicKernel_integralOn_compactDiffBox_eq
    (ω Lt : ℝ) [Fact (0 < Lt)]
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ) (hT : 0 < T)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0)
    (hLt_large : 4 * T < Lt) :
    ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
      (((@periodizeCLM Lt ‹Fact (0 < Lt)› h₁).toFun p.1 *
          (@periodizeCLM Lt ‹Fact (0 < Lt)› h₂).toFun p.2) *
        periodicKernel ω Lt (p.1 - p.2)) ∂volume =
    ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
      (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume := by
  have hK_meas :
      MeasurableSet (Set.Icc (-T) T ×ˢ Set.Icc (-T) T : Set (ℝ × ℝ)) :=
    measurableSet_Icc.prod measurableSet_Icc
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem hK_meas] with p hp
  have hper₁ :
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h₁).toFun p.1 = h₁ p.1 :=
    periodizeCLM_eq_on_symmetric_large_period
      (L := Lt) h₁ T hT hsupp₁ (by linarith [hLt_large]) p.1 hp.1
  have hper₂ :
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h₂).toFun p.2 = h₂ p.2 :=
    periodizeCLM_eq_on_symmetric_large_period
      (L := Lt) h₂ T hT hsupp₂ (by linarith [hLt_large]) p.2 hp.2
  simp [hper₁, hper₂]

private theorem freeKernel_le_of_mass_le
    (ω mass : ℝ) (hmass : 0 < mass) (hω : mass ≤ ω) (t : ℝ) :
    freeKernel ω t ≤ freeKernel mass t := by
  unfold freeKernel
  have hnum :
      Real.exp (-ω * |t|) ≤ Real.exp (-mass * |t|) := by
    apply (Real.exp_le_exp).2
    nlinarith [abs_nonneg t]
  have hinv :
      (2 * ω : ℝ)⁻¹ ≤ (2 * mass : ℝ)⁻¹ := by
    have hmass2_pos : 0 < (2 * mass : ℝ) := by positivity
    have hden_le : (2 * mass : ℝ) ≤ 2 * ω := by linarith
    simpa [one_div] using one_div_le_one_div_of_le hmass2_pos hden_le
  have hω_pos : 0 < ω := lt_of_lt_of_le hmass hω
  calc
    Real.exp (-ω * |t|) / (2 * ω)
      ≤ Real.exp (-mass * |t|) / (2 * ω) := by
          exact div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ (2 * ω : ℝ))
    _ = Real.exp (-mass * |t|) * (2 * ω : ℝ)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ Real.exp (-mass * |t|) * (2 * mass : ℝ)⁻¹ := by
          exact mul_le_mul_of_nonneg_left hinv (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-mass * |t|) / (2 * mass) := by rw [div_eq_mul_inv]

private theorem massGapEnvelope_le_fixed_constant
    (mass : ℝ) (hmass : 0 < mass) {Lt : ℝ} (hLt : 1 ≤ Lt) :
    Real.exp (-mass * Lt / 2) / (mass * (1 - Real.exp (-mass * Lt))) ≤
      1 / (mass * (1 - Real.exp (-mass))) := by
  have hnum :
      Real.exp (-mass * Lt / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hmass_exp_lt : Real.exp (-mass) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hLt_exp_lt : Real.exp (-mass * Lt) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hden_base_pos : 0 < mass * (1 - Real.exp (-mass)) := by
    exact mul_pos hmass (sub_pos.mpr hmass_exp_lt)
  have hden_pos : 0 < mass * (1 - Real.exp (-mass * Lt)) := by
    exact mul_pos hmass (sub_pos.mpr hLt_exp_lt)
  have hLt_exp_le : Real.exp (-mass * Lt) ≤ Real.exp (-mass) := by
    apply (Real.exp_le_exp).2
    nlinarith
  have hden_le :
      mass * (1 - Real.exp (-mass)) ≤ mass * (1 - Real.exp (-mass * Lt)) := by
    apply mul_le_mul_of_nonneg_left
    · linarith
    · exact hmass.le
  calc
    Real.exp (-mass * Lt / 2) / (mass * (1 - Real.exp (-mass * Lt)))
      ≤ 1 / (mass * (1 - Real.exp (-mass * Lt))) := by
          exact div_le_div_of_nonneg_right hnum hden_pos.le
    _ ≤ 1 / (mass * (1 - Real.exp (-mass))) := by
          exact one_div_le_one_div_of_le hden_base_pos hden_le

omit hLs in
/-- A compact-box majorant for the periodized temporal integrals, uniform in the spatial mode once
`ω_a ≥ mass`. This is the quantitative input needed for Tannery on the spatial `tsum`. -/
private theorem periodizedSchwartz_mul_resolventFreq_integral_norm_le_massGapMajorant
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ) (hT : 0 < T)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0)
    (mass : ℝ) (hmass : 0 < mass)
    (Lt : ℝ) [Fact (0 < Lt)]
    (hLt_large : 4 * T + 1 ≤ Lt)
    (a : ℕ) :
    |∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
        ((@periodizeCLM Lt ‹Fact (0 < Lt)› h₁).toFun p.1 *
          (@periodizeCLM Lt ‹Fact (0 < Lt)› h₂).toFun p.2) *
        periodicKernel (resolventFreq Ls mass a) Lt (p.1 - p.2) ∂volume| ≤
      ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
        |h₁ p.1 * h₂ p.2| *
          (freeKernel mass (p.1 - p.2) + 1 / (mass * (1 - Real.exp (-mass)))) ∂volume := by
  let K : Set (ℝ × ℝ) := Set.Icc (-T) T ×ˢ Set.Icc (-T) T
  let ω : ℝ := resolventFreq Ls mass a
  let F : ℝ × ℝ → ℝ := fun p =>
    ((@periodizeCLM Lt ‹Fact (0 < Lt)› h₁).toFun p.1 *
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h₂).toFun p.2) *
      periodicKernel ω Lt (p.1 - p.2)
  let G : ℝ × ℝ → ℝ := fun p =>
    |h₁ p.1 * h₂ p.2| *
      (freeKernel mass (p.1 - p.2) + 1 / (mass * (1 - Real.exp (-mass))))
  have hLt_pos : 0 < Lt := Fact.out
  have hK_compact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hω_ge : mass ≤ ω := resolventFreq_mass_le Ls mass hmass.le a
  have hF_cont : ContinuousOn F K := by
    have hper₁ : ContinuousOn
        (fun p : ℝ × ℝ => (@periodizeCLM Lt ‹Fact (0 < Lt)› h₁).toFun p.1) K := by
      exact ((@periodizeCLM Lt ‹Fact (0 < Lt)› h₁).continuous.comp continuous_fst).continuousOn
    have hper₂ : ContinuousOn
        (fun p : ℝ × ℝ => (@periodizeCLM Lt ‹Fact (0 < Lt)› h₂).toFun p.2) K := by
      exact ((@periodizeCLM Lt ‹Fact (0 < Lt)› h₂).continuous.comp continuous_snd).continuousOn
    have hk : ContinuousOn (fun p : ℝ × ℝ => periodicKernel ω Lt (p.1 - p.2)) K := by
      exact ((continuous_periodicKernel ω Lt).comp (continuous_fst.sub continuous_snd)).continuousOn
    simpa [F] using (hper₁.mul hper₂).mul hk
  have hG_cont : ContinuousOn G K := by
    have hh : ContinuousOn (fun p : ℝ × ℝ => |h₁ p.1 * h₂ p.2|) K := by
      exact ((h₁.continuous.comp continuous_fst).continuousOn.mul
        (h₂.continuous.comp continuous_snd).continuousOn).abs
    have hfree : ContinuousOn (fun p : ℝ × ℝ => freeKernel mass (p.1 - p.2)) K := by
      exact ((continuous_freeKernel mass).comp (continuous_fst.sub continuous_snd)).continuousOn
    have hconst : ContinuousOn
        (fun _ : ℝ × ℝ => 1 / (mass * (1 - Real.exp (-mass)))) K := by
      exact continuous_const.continuousOn
    have hk : ContinuousOn
        (fun p : ℝ × ℝ =>
          freeKernel mass (p.1 - p.2) + 1 / (mass * (1 - Real.exp (-mass)))) K := by
      exact hfree.add hconst
    simpa [G] using hh.mul hk
  have hF_int : Integrable F (volume.restrict K) := by
    simpa [K] using hF_cont.integrableOn_compact hK_compact
  have hG_int : Integrable G (volume.restrict K) := by
    simpa [K] using hG_cont.integrableOn_compact hK_compact
  have hFG_le : ∀ p ∈ K, |F p| ≤ G p := by
    rintro p hp
    rcases p with ⟨t, s⟩
    have ht_mem : t ∈ Set.Icc (-T) T := hp.1
    have hs_mem : s ∈ Set.Icc (-T) T := hp.2
    have ht_abs : |t| ≤ T := by
      simpa [Set.mem_Icc, abs_le] using ht_mem
    have hs_abs : |s| ≤ T := by
      simpa [Set.mem_Icc, abs_le] using hs_mem
    have hper₁ :
        (@periodizeCLM Lt ‹Fact (0 < Lt)› h₁).toFun t = h₁ t :=
      periodizeCLM_eq_on_symmetric_large_period
        (L := Lt) h₁ T hT hsupp₁ (by linarith [hLt_large]) t ht_mem
    have hper₂ :
        (@periodizeCLM Lt ‹Fact (0 < Lt)› h₂).toFun s = h₂ s :=
      periodizeCLM_eq_on_symmetric_large_period
        (L := Lt) h₂ T hT hsupp₂ (by linarith [hLt_large]) s hs_mem
    have hdiff_le : |t - s| ≤ 2 * T := by
      calc
        |t - s| ≤ |t| + |s| := by
            simpa using (abs_sub_le t 0 s)
        _ ≤ T + T := add_le_add ht_abs hs_abs
        _ = 2 * T := by ring
    have hdiff_lt : |t - s| < Lt / 2 := by
      have hhalf : 2 * T < Lt / 2 := by
        linarith [hLt_large]
      exact lt_of_le_of_lt hdiff_le hhalf
    have henv :
        |periodicKernel ω Lt (t - s) - freeKernel ω (t - s)| ≤
          1 / (mass * (1 - Real.exp (-mass))) := by
      refine
        (abs_sub_free_le_uniform_mass_gap ω mass hmass hω_ge
          (t - s) Lt hLt_pos hdiff_lt).trans ?_
      refine massGapEnvelope_le_fixed_constant mass hmass ?_
      linarith [hLt_large]
    have hfree :
        freeKernel ω (t - s) ≤ freeKernel mass (t - s) :=
      freeKernel_le_of_mass_le ω mass hmass hω_ge (t - s)
    have hk_abs :
        |periodicKernel ω Lt (t - s)| ≤
          freeKernel mass (t - s) + 1 / (mass * (1 - Real.exp (-mass))) := by
      have htriangle :
          |periodicKernel ω Lt (t - s)| ≤
            |periodicKernel ω Lt (t - s) - freeKernel ω (t - s)| +
              |freeKernel ω (t - s)| := by
        simpa using
          (abs_sub_le (periodicKernel ω Lt (t - s)) (freeKernel ω (t - s)) 0)
      have hfree_nonneg : 0 ≤ freeKernel ω (t - s) := by
        unfold freeKernel
        have hω_pos : 0 < ω := lt_of_lt_of_le hmass hω_ge
        positivity
      calc
        |periodicKernel ω Lt (t - s)|
          ≤ |periodicKernel ω Lt (t - s) - freeKernel ω (t - s)| +
              |freeKernel ω (t - s)| := htriangle
        _ ≤ 1 / (mass * (1 - Real.exp (-mass))) + freeKernel ω (t - s) := by
              rw [abs_of_nonneg hfree_nonneg]
              linarith
        _ ≤ 1 / (mass * (1 - Real.exp (-mass))) + freeKernel mass (t - s) := by
              linarith
        _ = freeKernel mass (t - s) + 1 / (mass * (1 - Real.exp (-mass))) := by ring
    calc
      |F (t, s)| = |h₁ t * h₂ s| * |periodicKernel ω Lt (t - s)| := by
        simp [F, hper₁, hper₂, abs_mul]
      _ ≤ |h₁ t * h₂ s| *
            (freeKernel mass (t - s) + 1 / (mass * (1 - Real.exp (-mass)))) := by
              exact mul_le_mul_of_nonneg_left hk_abs (abs_nonneg _)
      _ = G (t, s) := by
            simp [G]
  have hmono :
      ∫ p, |F p| ∂(volume.restrict K) ≤ ∫ p, G p ∂(volume.restrict K) := by
    refine integral_mono_ae hF_int.norm hG_int ?_
    filter_upwards [ae_restrict_mem hK_meas] with p hp
    exact hFG_le p hp
  calc
    |∫ p in K, F p ∂volume|
      = ‖∫ p, F p ∂(volume.restrict K)‖ := by
          simp [K, Real.norm_eq_abs]
    _ ≤ ∫ p, |F p| ∂(volume.restrict K) := by
          simpa [Real.norm_eq_abs] using
            (norm_integral_le_integral_norm (μ := volume.restrict K) F)
    _ ≤ ∫ p, G p ∂(volume.restrict K) := hmono
    _ = ∫ p in K, G p ∂volume := by
          simp [K]
    _ = ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          |h₁ p.1 * h₂ p.2| *
            (freeKernel mass (p.1 - p.2) + 1 / (mass * (1 - Real.exp (-mass)))) ∂volume := by
          simp [K, G]

/-- Under the remaining one-dimensional temporal bridge from circle Green forms to the explicit
periodic kernel, the pure compact-support torus-to-cylinder covariance convergence follows by
Tannery's theorem over the spatial modes. This is the exact Glimm-Jaffe / Simon modewise argument,
with the unresolved content isolated to the 1D periodic Green identity. -/
private theorem asymTorusGreen_tendsto_physicalCylinderGreen_pure_of_eventually_temporalBridge
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ) (hT : 0 < T)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0)
    (Lt : ℕ → ℝ) (hLt : ∀ k, Fact (0 < Lt k))
    (hLt_tend : Tendsto Lt atTop atTop)
    (htemporal :
      ∀ᶠ k in atTop, ∀ a : ℕ,
        greenFunctionBilinear (E := SmoothMap_Circle (Lt k) ℝ)
          (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a)
          (@periodizeCLM (Lt k) (hLt k) h₁)
          (@periodizeCLM (Lt k) (hLt k) h₂) =
        ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
            (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
            periodicKernel (resolventFreq Ls mass a) (Lt k) (p.1 - p.2) ∂volume) :
    Tendsto
      (fun k =>
        @asymTorusContinuumGreen (Lt k) Ls (hLt k) _ mass hmass
          (@cylinderToTorusEmbed (Lt k) Ls (hLt k) _
            (NuclearTensorProduct.pure g₁ h₁))
          (@cylinderToTorusEmbed (Lt k) Ls (hLt k) _
            (NuclearTensorProduct.pure g₂ h₂)))
      atTop
      (nhds (physicalCylinderGreen_pure (Ls := Ls) mass hmass g₁ g₂ h₁ h₂)) := by
  let K : Set (ℝ × ℝ) := Set.Icc (-T) T ×ˢ Set.Icc (-T) T
  let F : ℕ → ℕ → ℝ := fun k a =>
    (DyninMityaginSpace.coeff a g₁ * DyninMityaginSpace.coeff a g₂) *
      (∫ p in K,
        ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
          (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
          periodicKernel (resolventFreq Ls mass a) (Lt k) (p.1 - p.2) ∂volume)
  let G : ℕ → ℝ := fun a =>
    (DyninMityaginSpace.coeff a g₁ * DyninMityaginSpace.coeff a g₂) *
      (∫ p in K,
        (h₁ p.1 * h₂ p.2) * freeKernel (resolventFreq Ls mass a) (p.1 - p.2) ∂volume)
  let Cmaj : ℝ :=
    ∫ p in K,
      |h₁ p.1 * h₂ p.2| *
        (freeKernel mass (p.1 - p.2) + 1 / (mass * (1 - Real.exp (-mass)))) ∂volume
  let bound : ℕ → ℝ := fun a =>
    Cmaj * |DyninMityaginSpace.coeff a g₁ * DyninMityaginSpace.coeff a g₂|
  have hCmaj_nonneg : 0 ≤ Cmaj := by
    dsimp [Cmaj]
    apply integral_nonneg
    intro p
    have hconst_nonneg : 0 ≤ 1 / (mass * (1 - Real.exp (-mass))) := by
      have hmass_exp_lt : Real.exp (-mass) < 1 := by
        rw [Real.exp_lt_one_iff]
        nlinarith
      have hden_pos : 0 < mass * (1 - Real.exp (-mass)) := by
        exact mul_pos hmass (sub_pos.mpr hmass_exp_lt)
      exact one_div_nonneg.mpr hden_pos.le
    have hfree_nonneg : 0 ≤ freeKernel mass (p.1 - p.2) := by
      unfold freeKernel
      positivity
    exact mul_nonneg (abs_nonneg _) (add_nonneg hfree_nonneg hconst_nonneg)
  have hbound_summable : Summable bound := by
    dsimp [bound]
    exact ((l2InnerProduct_summable g₁ g₂).abs.mul_left Cmaj)
  have hpointwise : ∀ a : ℕ, Tendsto (fun k => F k a) atTop (nhds (G a)) := by
    intro a
    dsimp [F, G]
    simpa [K, mul_assoc, mul_left_comm, mul_comm] using
      Filter.Tendsto.const_mul
        (DyninMityaginSpace.coeff a g₁ * DyninMityaginSpace.coeff a g₂)
        (periodizedSchwartz_mul_periodicKernel_tendsto_freeKernel_integralOn_compactDiffBox
          (h₁ := h₁) (h₂ := h₂) T hT hsupp₁ hsupp₂
          (ω := resolventFreq Ls mass a) (mass := mass) hmass
          (resolventFreq_mass_le Ls mass hmass.le a) Lt hLt hLt_tend)
  have hlarge : ∀ᶠ k in atTop, 4 * T + 1 ≤ Lt k :=
    (Filter.tendsto_atTop.mp hLt_tend) (4 * T + 1)
  have hbound_eventually : ∀ᶠ k in atTop, ∀ a : ℕ, |F k a| ≤ bound a := by
    filter_upwards [hlarge] with k hk a
    letI : Fact (0 < Lt k) := hLt k
    have htemp_bd :=
      periodizedSchwartz_mul_resolventFreq_integral_norm_le_massGapMajorant
        (Ls := Ls) (h₁ := h₁) (h₂ := h₂) T hT hsupp₁ hsupp₂ mass hmass
        (Lt := Lt k) hk a
    calc
      |F k a|
        = |DyninMityaginSpace.coeff a g₁ * DyninMityaginSpace.coeff a g₂| *
            |∫ p in K,
              ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
                (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
                periodicKernel (resolventFreq Ls mass a) (Lt k) (p.1 - p.2) ∂volume| := by
                dsimp [F]
                rw [abs_mul]
      _ ≤ |DyninMityaginSpace.coeff a g₁ * DyninMityaginSpace.coeff a g₂| * Cmaj := by
            exact mul_le_mul_of_nonneg_left htemp_bd (abs_nonneg _)
      _ = bound a := by
            simp [bound, Cmaj, mul_comm]
  have hsum_tend :
      Tendsto (fun k => ∑' a : ℕ, F k a) atTop (nhds (∑' a : ℕ, G a)) := by
    apply tendsto_tsum_of_dominated_convergence (bound := bound)
    · exact hbound_summable
    · exact hpointwise
    · exact hbound_eventually
  have htorus_eventually :
      ∀ᶠ k in atTop,
        @asymTorusContinuumGreen (Lt k) Ls (hLt k) _ mass hmass
            (@cylinderToTorusEmbed (Lt k) Ls (hLt k) _
              (NuclearTensorProduct.pure g₁ h₁))
            (@cylinderToTorusEmbed (Lt k) Ls (hLt k) _
              (NuclearTensorProduct.pure g₂ h₂)) =
          ∑' a : ℕ, F k a := by
    filter_upwards [htemporal] with k hk
    rw [asymTorusContinuumGreen_embed_pure_eq_tsum_temporalGreen
      (Ls := Ls) (Lt := Lt k) (mass := mass) (hmass := hmass)
      (g₁ := g₁) (g₂ := g₂) (h₁ := h₁) (h₂ := h₂)]
    apply tsum_congr
    intro a
    rw [hk a]
  have hmain :
      Tendsto
        (fun k =>
          @asymTorusContinuumGreen (Lt k) Ls (hLt k) _ mass hmass
            (@cylinderToTorusEmbed (Lt k) Ls (hLt k) _
              (NuclearTensorProduct.pure g₁ h₁))
            (@cylinderToTorusEmbed (Lt k) Ls (hLt k) _
              (NuclearTensorProduct.pure g₂ h₂)))
        atTop
        (nhds (∑' a : ℕ, G a)) := by
    have hsum_eventually :
        (fun k => ∑' a : ℕ, F k a) =ᶠ[atTop]
          (fun k =>
            @asymTorusContinuumGreen (Lt k) Ls (hLt k) _ mass hmass
              (@cylinderToTorusEmbed (Lt k) Ls (hLt k) _
                (NuclearTensorProduct.pure g₁ h₁))
              (@cylinderToTorusEmbed (Lt k) Ls (hLt k) _
                (NuclearTensorProduct.pure g₂ h₂))) := by
      filter_upwards [htorus_eventually] with k hk
      exact hk.symm
    exact hsum_tend.congr' hsum_eventually
  have htarget :
      physicalCylinderGreen_pure (Ls := Ls) mass hmass g₁ g₂ h₁ h₂ =
        ∑' a : ℕ, G a := by
    dsimp [G, K]
    exact physicalCylinderGreen_pure_eq_tsum_freeKernel_integralOn_compactDiffBox
      (Ls := Ls) mass hmass g₁ g₂ h₁ h₂ T hsupp₁ hsupp₂
  simpa [htarget] using hmain

/-- Compactly supported pure tensors satisfy torus-to-cylinder covariance convergence once the
temporal bridge is supplied by the compact-box periodic-kernel identity proved above. -/
private theorem asymTorusGreen_tendsto_physicalCylinderGreen_pure
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ) (hT : 0 < T)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0)
    (Lt : ℕ → ℝ) (hLt : ∀ k, Fact (0 < Lt k))
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto
      (fun k =>
        @asymTorusContinuumGreen (Lt k) Ls (hLt k) _ mass hmass
          (@cylinderToTorusEmbed (Lt k) Ls (hLt k) _
            (NuclearTensorProduct.pure g₁ h₁))
          (@cylinderToTorusEmbed (Lt k) Ls (hLt k) _
            (NuclearTensorProduct.pure g₂ h₂)))
      atTop
      (nhds (physicalCylinderGreen_pure (Ls := Ls) mass hmass g₁ g₂ h₁ h₂)) := by
  have hlarge : ∀ᶠ k in atTop, 4 * T + 1 ≤ Lt k :=
    (Filter.tendsto_atTop.mp hLt_tend) (4 * T + 1)
  have htemporal :
      ∀ᶠ k in atTop, ∀ a : ℕ,
        greenFunctionBilinear (E := SmoothMap_Circle (Lt k) ℝ)
          (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a)
          (@periodizeCLM (Lt k) (hLt k) h₁)
          (@periodizeCLM (Lt k) (hLt k) h₂) =
        ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
            (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
            periodicKernel (resolventFreq Ls mass a) (Lt k) (p.1 - p.2) ∂volume := by
    filter_upwards [hlarge] with k hk a
    letI : Fact (0 < Lt k) := hLt k
    have hk' : 4 * T < Lt k := by
      linarith
    calc
      greenFunctionBilinear (E := SmoothMap_Circle (Lt k) ℝ)
          (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a)
          (@periodizeCLM (Lt k) (hLt k) h₁)
          (@periodizeCLM (Lt k) (hLt k) h₂)
        =
          ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
            (h₁ p.1 * h₂ p.2) *
              periodicKernel (resolventFreq Ls mass a) (Lt k) (p.1 - p.2) ∂volume := by
            exact greenFunctionBilinear_eq_periodicKernel_integralOn_compactDiffBox
              (ω := resolventFreq Ls mass a) (Lt := Lt k)
              (hω := resolventFreq_pos Ls mass hmass a)
              (h₁ := h₁) (h₂ := h₂) T hT hsupp₁ hsupp₂ hk'
      _ =
          ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
            ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
              (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
              periodicKernel (resolventFreq Ls mass a) (Lt k) (p.1 - p.2) ∂volume := by
            symm
            exact periodizedSchwartz_mul_periodicKernel_integralOn_compactDiffBox_eq
              (ω := resolventFreq Ls mass a) (Lt := Lt k)
              (h₁ := h₁) (h₂ := h₂) T hT hsupp₁ hsupp₂ hk'
  exact asymTorusGreen_tendsto_physicalCylinderGreen_pure_of_eventually_temporalBridge
    (Ls := Ls) mass hmass g₁ g₂ h₁ h₂ T hT hsupp₁ hsupp₂ Lt hLt hLt_tend htemporal

/-- Bilinearity upgrades compact-support pure convergence to finite sums of compactly supported pure
tensors, with the target given by the physically normalized pure-cylinder form termwise. This
isolates the remaining work to the genuine density/normalization extension from finite-rank compact
support to arbitrary cylinder test functions. -/
private theorem asymTorusGreen_tendsto_physicalCylinderGreen_finset_sum_of_pure
    (mass : ℝ) (hmass : 0 < mass)
    {ι₁ ι₂ : Type*}
    (s₁ : Finset ι₁) (s₂ : Finset ι₂)
    (a : ι₁ → ℝ) (b : ι₂ → ℝ)
    (g₁ : ι₁ → SmoothMap_Circle Ls ℝ)
    (h₁ : ι₁ → SchwartzMap ℝ ℝ)
    (g₂ : ι₂ → SmoothMap_Circle Ls ℝ)
    (h₂ : ι₂ → SchwartzMap ℝ ℝ)
    (T : ℝ) (hT : 0 < T)
    (hsupp₁ : ∀ i t, T < |t| → h₁ i t = 0)
    (hsupp₂ : ∀ j t, T < |t| → h₂ j t = 0)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto (fun n =>
      @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
        (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
          (∑ i ∈ s₁, a i • NuclearTensorProduct.pure (g₁ i) (h₁ i)))
        (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
          (∑ j ∈ s₂, b j • NuclearTensorProduct.pure (g₂ j) (h₂ j))))
      atTop
      (nhds
        (physicalCylinderGreen (Ls := Ls) mass hmass
          (∑ i ∈ s₁, a i • NuclearTensorProduct.pure (g₁ i) (h₁ i))
          (∑ j ∈ s₂, b j • NuclearTensorProduct.pure (g₂ j) (h₂ j)))) := by
  classical
  set f : CylinderTestFunction Ls :=
    ∑ i ∈ s₁, a i • NuclearTensorProduct.pure (g₁ i) (h₁ i)
  set g : CylinderTestFunction Ls :=
    ∑ j ∈ s₂, b j • NuclearTensorProduct.pure (g₂ j) (h₂ j)
  have hsum :
      Tendsto
        (fun n =>
          ∑ i ∈ s₁, ∑ j ∈ s₂,
            a i * b j *
              @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
                (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
                  (NuclearTensorProduct.pure (g₁ i) (h₁ i)))
                (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
                  (NuclearTensorProduct.pure (g₂ j) (h₂ j))))
        atTop
        (nhds
          (∑ i ∈ s₁, ∑ j ∈ s₂,
            a i * b j *
              physicalCylinderGreen_pure (Ls := Ls) mass hmass
                (g₁ i) (g₂ j) (h₁ i) (h₂ j))) := by
    apply tendsto_finset_sum
    intro i hi
    apply tendsto_finset_sum
    intro j hj
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Filter.Tendsto.const_mul (a i * b j)
        (asymTorusGreen_tendsto_physicalCylinderGreen_pure
          (Ls := Ls) mass hmass (g₁ i) (g₂ j) (h₁ i) (h₂ j) T hT
          (hsupp₁ i) (hsupp₂ j) Lt hLt hLt_tend)
  have hleft :
      (fun n =>
        @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
          (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _ f)
          (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _ g)) =
      (fun n =>
        ∑ i ∈ s₁, ∑ j ∈ s₂,
          a i * b j *
            @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
              (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
                (NuclearTensorProduct.pure (g₁ i) (h₁ i)))
              (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
                (NuclearTensorProduct.pure (g₂ j) (h₂ j)))) := by
    funext n
    simpa [f, g, asymTorusContinuumGreen, mul_assoc, mul_left_comm, mul_comm] using
      (GaussianField.greenFunctionBilinear_finset_sum
        (E := AsymTorusTestFunction (Lt n) Ls) mass hmass s₁ s₂ a b
        (fun i =>
          @cylinderToTorusEmbed (Lt n) Ls (hLt n) _
            (NuclearTensorProduct.pure (g₁ i) (h₁ i)))
        (fun j =>
          @cylinderToTorusEmbed (Lt n) Ls (hLt n) _
            (NuclearTensorProduct.pure (g₂ j) (h₂ j))))
  have hright :
      physicalCylinderGreen (Ls := Ls) mass hmass f g =
        ∑ i ∈ s₁, ∑ j ∈ s₂,
          a i * b j *
            physicalCylinderGreen_pure (Ls := Ls) mass hmass
              (g₁ i) (g₂ j) (h₁ i) (h₂ j) := by
    calc
      physicalCylinderGreen (Ls := Ls) mass hmass f g =
          ∑ i ∈ s₁, ∑ j ∈ s₂,
            a i * b j *
              physicalCylinderGreen (Ls := Ls) mass hmass
                (NuclearTensorProduct.pure (g₁ i) (h₁ i))
                (NuclearTensorProduct.pure (g₂ j) (h₂ j)) := by
            simpa [f, g] using
              (physicalCylinderGreen_finset_sum (Ls := Ls) mass hmass s₁ s₂ a b
                (fun i => NuclearTensorProduct.pure (g₁ i) (h₁ i))
                (fun j => NuclearTensorProduct.pure (g₂ j) (h₂ j)))
      _ = ∑ i ∈ s₁, ∑ j ∈ s₂,
            a i * b j *
              physicalCylinderGreen_pure (Ls := Ls) mass hmass
                (g₁ i) (g₂ j) (h₁ i) (h₂ j) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [physicalCylinderGreen_apply_pure_eq]
  rw [hleft, hright]
  exact hsum

private theorem physicalCylinderGreen_symm
    (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction Ls) :
    physicalCylinderGreen (Ls := Ls) mass hmass f g =
      physicalCylinderGreen (Ls := Ls) mass hmass g f := by
  simpa [physicalCylinderGreen] using
    (cylinderGreen_symm (L := Ls) mass hmass
      (cylinderTwoPiRescale Ls f)
      (cylinderTwoPiRescale Ls g))

private theorem physicalCylinderGreen_nonneg
    (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction Ls) :
    0 ≤ physicalCylinderGreen (Ls := Ls) mass hmass f f := by
  simpa [physicalCylinderGreen] using
    (cylinderGreen_nonneg Ls mass hmass (cylinderTwoPiRescale Ls f))

private theorem physicalCylinderGreen_sub_left
    (mass : ℝ) (hmass : 0 < mass)
    (f g h : CylinderTestFunction Ls) :
    physicalCylinderGreen (Ls := Ls) mass hmass (f - g) h =
      physicalCylinderGreen (Ls := Ls) mass hmass f h -
        physicalCylinderGreen (Ls := Ls) mass hmass g h := by
  simpa [physicalCylinderGreen, sub_eq_add_neg, smul_eq_mul, map_sub, map_add, map_neg,
    map_smul, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using
    (cylinderGreen_bilinear (L := Ls) mass hmass (-1 : ℝ)
      (cylinderTwoPiRescale Ls g)
      (cylinderTwoPiRescale Ls f)
      (cylinderTwoPiRescale Ls h))

private theorem physicalCylinderGreen_sub_right
    (mass : ℝ) (hmass : 0 < mass)
    (f g h : CylinderTestFunction Ls) :
    physicalCylinderGreen (Ls := Ls) mass hmass h (f - g) =
      physicalCylinderGreen (Ls := Ls) mass hmass h f -
        physicalCylinderGreen (Ls := Ls) mass hmass h g := by
  rw [physicalCylinderGreen_symm (Ls := Ls) mass hmass h (f - g),
    physicalCylinderGreen_symm (Ls := Ls) mass hmass h f,
    physicalCylinderGreen_symm (Ls := Ls) mass hmass h g,
    physicalCylinderGreen_sub_left (Ls := Ls) mass hmass f g h]

private theorem asymTorusContinuumGreen_embed_symm
    (Lt : ℝ) [hLt : Fact (0 < Lt)]
    (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction Ls) :
    asymTorusContinuumGreen Lt Ls mass hmass
      (cylinderToTorusEmbed Lt Ls f)
      (cylinderToTorusEmbed Lt Ls g) =
    asymTorusContinuumGreen Lt Ls mass hmass
      (cylinderToTorusEmbed Lt Ls g)
      (cylinderToTorusEmbed Lt Ls f) := by
  simpa [asymTorusContinuumGreen] using
    (greenFunctionBilinear_symm mass hmass
      (cylinderToTorusEmbed Lt Ls f)
      (cylinderToTorusEmbed Lt Ls g))

private theorem asymTorusContinuumGreen_embed_sub_left
    (Lt : ℝ) [hLt : Fact (0 < Lt)]
    (mass : ℝ) (hmass : 0 < mass)
    (f g h : CylinderTestFunction Ls) :
    asymTorusContinuumGreen Lt Ls mass hmass
      (cylinderToTorusEmbed Lt Ls (f - g))
      (cylinderToTorusEmbed Lt Ls h) =
    asymTorusContinuumGreen Lt Ls mass hmass
      (cylinderToTorusEmbed Lt Ls f)
      (cylinderToTorusEmbed Lt Ls h) -
        asymTorusContinuumGreen Lt Ls mass hmass
          (cylinderToTorusEmbed Lt Ls g)
          (cylinderToTorusEmbed Lt Ls h) := by
  simpa [asymTorusContinuumGreen, map_sub] using
    (greenFunctionBilinear_sub_left mass hmass
      (cylinderToTorusEmbed Lt Ls f)
      (cylinderToTorusEmbed Lt Ls g)
      (cylinderToTorusEmbed Lt Ls h))

private theorem asymTorusContinuumGreen_embed_sub_right
    (Lt : ℝ) [hLt : Fact (0 < Lt)]
    (mass : ℝ) (hmass : 0 < mass)
    (f g h : CylinderTestFunction Ls) :
    asymTorusContinuumGreen Lt Ls mass hmass
      (cylinderToTorusEmbed Lt Ls h)
      (cylinderToTorusEmbed Lt Ls (f - g)) =
    asymTorusContinuumGreen Lt Ls mass hmass
      (cylinderToTorusEmbed Lt Ls h)
      (cylinderToTorusEmbed Lt Ls f) -
        asymTorusContinuumGreen Lt Ls mass hmass
          (cylinderToTorusEmbed Lt Ls h)
          (cylinderToTorusEmbed Lt Ls g) := by
  rw [asymTorusContinuumGreen_embed_symm (Ls := Ls) Lt mass hmass h (f - g),
    asymTorusContinuumGreen_embed_symm (Ls := Ls) Lt mass hmass h f,
    asymTorusContinuumGreen_embed_symm (Ls := Ls) Lt mass hmass h g,
    asymTorusContinuumGreen_embed_sub_left (Ls := Ls) Lt mass hmass f g h]
-- This finite-rank approximation proof expands several bilinear estimates and
-- needs a larger heartbeat budget than the default elaborator limit.
set_option maxHeartbeats 800000 in
/-- Extend the compact-support finite-rank convergence theorem to arbitrary cylinder test functions
by approximating both arguments in a seminorm that simultaneously controls the torus-side uniform
bound and the cylinder-side limiting bilinear form. -/
theorem asymTorusGreen_tendsto_physicalCylinderGreen
    (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction Ls)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto (fun n =>
      @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
        (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _ f)
        (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _ g))
      atTop (nhds (physicalCylinderGreen (Ls := Ls) mass hmass f g)) := by
  obtain ⟨C, hC_pos, qt, hqt_cont, hqt_bound⟩ :=
    asymTorusGreen_uniform_product_seminorm_bound (Ls := Ls) mass hmass
  obtain ⟨qp, hqp_cont, hqp_bound⟩ :=
    physicalCylinderGreen_product_seminorm_bound (Ls := Ls) mass hmass
  set qsum : Seminorm ℝ (CylinderTestFunction Ls) := qt + qp
  have hqsum_cont : Continuous qsum := by
    dsimp [qsum]
    exact hqt_cont.add hqp_cont
  have hqt_le_qsum : ∀ u : CylinderTestFunction Ls, qt u ≤ qsum u := by
    intro u
    dsimp [qsum]
    linarith [apply_nonneg qp u]
  have hqp_le_qsum : ∀ u : CylinderTestFunction Ls, qp u ≤ qsum u := by
    intro u
    dsimp [qsum]
    linarith [apply_nonneg qt u]
  let A : ℕ → CylinderTestFunction Ls → CylinderTestFunction Ls → ℝ :=
    fun n u v =>
      @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
        (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _ u)
        (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _ v)
  let P : CylinderTestFunction Ls → CylinderTestFunction Ls → ℝ :=
    physicalCylinderGreen (Ls := Ls) mass hmass
  rw [Metric.tendsto_nhds]
  intro ε hε
  set Qf : ℝ := qsum f
  set Qg : ℝ := qsum g
  have hQf_nonneg : 0 ≤ Qf := by
    dsimp [Qf]
    exact apply_nonneg qsum f
  have hQg_nonneg : 0 ≤ Qg := by
    dsimp [Qg]
    exact apply_nonneg qsum g
  set M : ℝ := 4 * (C + 1) * (Qf + Qg + 1)
  have hM_pos : 0 < M := by
    dsimp [M]
    nlinarith [hC_pos, hQf_nonneg, hQg_nonneg]
  set δ : ℝ := min 1 (ε / M)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (div_pos hε hM_pos)
  have hδ_le_one : δ ≤ 1 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ_le_eps : δ ≤ ε / M := by
    dsimp [δ]
    exact min_le_right _ _
  obtain ⟨sf, Nf, hf_small0⟩ :=
    exists_compactSupport_basisApprox (Ls := Ls) qsum hqsum_cont f hδ_pos
  obtain ⟨sg, Ng, hg_small0⟩ :=
    exists_compactSupport_basisApprox (Ls := Ls) qsum hqsum_cont g hδ_pos
  set f₀ : CylinderTestFunction Ls := basisCutoffPartial (Ls := Ls) f sf Nf
  set g₀ : CylinderTestFunction Ls := basisCutoffPartial (Ls := Ls) g sg Ng
  have hf_small : qsum (f - f₀) < δ := by
    simpa [f₀] using hf_small0
  have hg_small : qsum (g - g₀) < δ := by
    simpa [g₀] using hg_small0
  have hf_small_sym : qsum (f₀ - f) < δ := by
    have hneg : f₀ - f = -(f - f₀) := by
      abel
    rw [hneg, map_neg_eq_map]
    exact hf_small
  have hg_small_sym : qsum (g₀ - g) < δ := by
    have hneg : g₀ - g = -(g - g₀) := by
      abel
    rw [hneg, map_neg_eq_map]
    exact hg_small
  have hqsum_f₀ : qsum f₀ ≤ Qf + δ := by
    have hdecomp : (f₀ - f) + f = f₀ := by
      abel
    calc
      qsum f₀ = qsum ((f₀ - f) + f) := by
        exact congrArg qsum hdecomp.symm
      _ ≤ qsum (f₀ - f) + qsum f := qsum.add_le' _ _
      _ ≤ δ + qsum f := by
        have hsmall : qsum (f₀ - f) ≤ δ := le_of_lt hf_small_sym
        linarith
      _ = Qf + δ := by
        simp [Qf, add_comm]
  have hqsum_g₀ : qsum g₀ ≤ Qg + δ := by
    have hdecomp : (g₀ - g) + g = g₀ := by
      abel
    calc
      qsum g₀ = qsum ((g₀ - g) + g) := by
        exact congrArg qsum hdecomp.symm
      _ ≤ qsum (g₀ - g) + qsum g := qsum.add_le' _ _
      _ ≤ δ + qsum g := by
        have hsmall : qsum (g₀ - g) ≤ δ := le_of_lt hg_small_sym
        linarith
      _ = Qg + δ := by
        simp [Qg, add_comm]
  have hqt_f₀ : qt f₀ ≤ Qf + 1 := by
    have hqt_f₀' : qt f₀ ≤ Qf + δ := le_trans (hqt_le_qsum f₀) hqsum_f₀
    nlinarith
  have hqp_f₀ : qp f₀ ≤ Qf + 1 := by
    have hqp_f₀' : qp f₀ ≤ Qf + δ := le_trans (hqp_le_qsum f₀) hqsum_f₀
    nlinarith
  set T : ℝ := 2 * (((max Nf Ng : ℕ) : ℝ) + 1)
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hsupp_f₀ :
      ∀ m t, T < |t| →
        schwartzCutoffCLM Nf (cylinderBasisTemporal m) t = 0 := by
    intro m t ht
    apply schwartzCutoffCLM_eq_zero_of_two_mul_lt_abs
    have hNf_le : (Nf : ℝ) ≤ (max Nf Ng : ℕ) := by
      exact_mod_cast Nat.le_max_left Nf Ng
    dsimp [T] at ht ⊢
    linarith
  have hsupp_g₀ :
      ∀ m t, T < |t| →
        schwartzCutoffCLM Ng (cylinderBasisTemporal m) t = 0 := by
    intro m t ht
    apply schwartzCutoffCLM_eq_zero_of_two_mul_lt_abs
    have hNg_le : (Ng : ℝ) ≤ (max Nf Ng : ℕ) := by
      exact_mod_cast Nat.le_max_right Nf Ng
    dsimp [T] at ht ⊢
    linarith
  have hmain :
      Tendsto (fun n => A n f₀ g₀) atTop (nhds (P f₀ g₀)) := by
    simpa [A, P, f₀, g₀, basisCutoffPartial] using
      (asymTorusGreen_tendsto_physicalCylinderGreen_finset_sum_of_pure
        (Ls := Ls) mass hmass
        (s₁ := sf) (s₂ := sg)
        (a := fun m => DyninMityaginSpace.coeff m f)
        (b := fun m => DyninMityaginSpace.coeff m g)
        (g₁ := fun m => cylinderBasisSpatial (Ls := Ls) m)
        (h₁ := fun m => schwartzCutoffCLM Nf (cylinderBasisTemporal m))
        (g₂ := fun m => cylinderBasisSpatial (Ls := Ls) m)
        (h₂ := fun m => schwartzCutoffCLM Ng (cylinderBasisTemporal m))
        T hT hsupp_f₀ hsupp_g₀ Lt hLt hLt_tend)
  have hLt_ge_one : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Lt n :=
    (tendsto_atTop.1 hLt_tend) 1
  have hmain_ev :
      ∀ᶠ n : ℕ in atTop, dist (A n f₀ g₀) (P f₀ g₀) < ε / 2 := by
    exact (Metric.tendsto_nhds.mp hmain) (ε / 2) (by linarith)
  filter_upwards [hLt_ge_one, hmain_ev] with n hnLt hnmain
  have hdist1 : dist (A n f g) (A n f₀ g) = |A n (f - f₀) g| := by
    rw [Real.dist_eq, ← asymTorusContinuumGreen_embed_sub_left
      (Ls := Ls) (Lt := Lt n) (hLt := hLt n) mass hmass f f₀ g]
  have hdist2 : dist (A n f₀ g) (A n f₀ g₀) = |A n f₀ (g - g₀)| := by
    rw [Real.dist_eq, ← asymTorusContinuumGreen_embed_sub_right
      (Ls := Ls) (Lt := Lt n) (hLt := hLt n) mass hmass g g₀ f₀]
  have hdist4 : dist (P f₀ g₀) (P f₀ g) = |P f₀ (g₀ - g)| := by
    rw [Real.dist_eq, ← physicalCylinderGreen_sub_right
      (Ls := Ls) mass hmass g₀ g f₀]
  have hdist5 : dist (P f₀ g) (P f g) = |P (f₀ - f) g| := by
    rw [Real.dist_eq, ← physicalCylinderGreen_sub_left
      (Ls := Ls) mass hmass f₀ f g]
  have hbound1 : dist (A n f g) (A n f₀ g) ≤ C * δ * Qg := by
    rw [hdist1]
    have hA : |A n (f - f₀) g| ≤ C * qt (f - f₀) * qt g :=
      hqt_bound (Lt n) hnLt (f - f₀) g
    have hfdiff : qt (f - f₀) ≤ δ := by
      exact le_trans (hqt_le_qsum (f - f₀)) (le_of_lt hf_small)
    have hgq : qt g ≤ Qg := by
      calc
        qt g ≤ qsum g := hqt_le_qsum g
        _ = Qg := by simp [Qg]
    have hmul₁ : C * qt (f - f₀) ≤ C * δ := by
      exact mul_le_mul_of_nonneg_left hfdiff hC_pos.le
    have hmul₂ : C * qt (f - f₀) * qt g ≤ C * δ * qt g := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hmul₁ (apply_nonneg qt g)
    have hmul₃ : C * δ * qt g ≤ C * δ * Qg := by
      have hCδ_nonneg : 0 ≤ C * δ := by positivity
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hgq hCδ_nonneg
    exact le_trans hA (le_trans hmul₂ hmul₃)
  have hbound2 : dist (A n f₀ g) (A n f₀ g₀) ≤ C * (Qf + 1) * δ := by
    rw [hdist2]
    have hA : |A n f₀ (g - g₀)| ≤ C * qt f₀ * qt (g - g₀) :=
      hqt_bound (Lt n) hnLt f₀ (g - g₀)
    have hgdiff : qt (g - g₀) ≤ δ := by
      exact le_trans (hqt_le_qsum (g - g₀)) (le_of_lt hg_small)
    have hmul₁ : C * qt f₀ * qt (g - g₀) ≤ C * qt f₀ * δ := by
      have hCqt_nonneg : 0 ≤ C * qt f₀ := by positivity
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hgdiff hCqt_nonneg
    have hmul₂ : C * qt f₀ ≤ C * (Qf + 1) := by
      exact mul_le_mul_of_nonneg_left hqt_f₀ hC_pos.le
    have hmul₃ : C * qt f₀ * δ ≤ C * (Qf + 1) * δ := by
      have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hmul₂ hδ_nonneg
    exact le_trans hA (le_trans hmul₁ hmul₃)
  have hbound4 : dist (P f₀ g₀) (P f₀ g) ≤ (Qf + 1) * δ := by
    rw [hdist4]
    have hA : |P f₀ (g₀ - g)| ≤ qp f₀ * qp (g₀ - g) :=
      hqp_bound f₀ (g₀ - g)
    have hgdiff : qp (g₀ - g) ≤ δ := by
      exact le_trans (hqp_le_qsum (g₀ - g)) (le_of_lt hg_small_sym)
    have hmul₁ : qp f₀ * qp (g₀ - g) ≤ qp f₀ * δ := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hgdiff (apply_nonneg qp f₀)
    have hmul₂ : qp f₀ * δ ≤ (Qf + 1) * δ := by
      have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hqp_f₀ hδ_nonneg
    exact le_trans hA (le_trans hmul₁ hmul₂)
  have hbound5 : dist (P f₀ g) (P f g) ≤ δ * Qg := by
    rw [hdist5]
    have hA : |P (f₀ - f) g| ≤ qp (f₀ - f) * qp g :=
      hqp_bound (f₀ - f) g
    have hfdiff : qp (f₀ - f) ≤ δ := by
      exact le_trans (hqp_le_qsum (f₀ - f)) (le_of_lt hf_small_sym)
    have hgq : qp g ≤ Qg := by
      calc
        qp g ≤ qsum g := hqp_le_qsum g
        _ = Qg := by simp [Qg]
    have hmul₁ : qp (f₀ - f) * qp g ≤ δ * qp g := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hfdiff (apply_nonneg qp g)
    have hmul₂ : δ * qp g ≤ δ * Qg := by
      have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hgq hδ_nonneg
    exact le_trans hA (le_trans hmul₁ hmul₂)
  let d1 : ℝ := dist (A n f g) (A n f₀ g)
  let d2 : ℝ := dist (A n f₀ g) (A n f₀ g₀)
  let d3 : ℝ := dist (A n f₀ g₀) (P f₀ g₀)
  let d4 : ℝ := dist (P f₀ g₀) (P f₀ g)
  let d5 : ℝ := dist (P f₀ g) (P f g)
  let a1 : ℝ := C * δ * Qg
  let a2 : ℝ := C * (Qf + 1) * δ
  let a4 : ℝ := (Qf + 1) * δ
  let a5 : ℝ := δ * Qg
  have hd1 : d1 ≤ a1 := by simpa [d1, a1] using hbound1
  have hd2 : d2 ≤ a2 := by simpa [d2, a2] using hbound2
  have hd4 : d4 ≤ a4 := by simpa [d4, a4] using hbound4
  have hd5 : d5 ≤ a5 := by simpa [d5, a5] using hbound5
  have htri : dist (A n f g) (P f g) ≤ d1 + d2 + d3 + d4 + d5 := by
    calc
      dist (A n f g) (P f g)
        ≤ dist (A n f g) (A n f₀ g) + dist (A n f₀ g) (P f g) := dist_triangle _ _ _
      _ ≤ dist (A n f g) (A n f₀ g) +
            (dist (A n f₀ g) (A n f₀ g₀) + dist (A n f₀ g₀) (P f g)) := by
              gcongr
              exact dist_triangle _ _ _
      _ ≤ dist (A n f g) (A n f₀ g) +
            (dist (A n f₀ g) (A n f₀ g₀) +
              (dist (A n f₀ g₀) (P f₀ g₀) + dist (P f₀ g₀) (P f g))) := by
              gcongr
              exact dist_triangle _ _ _
      _ ≤ dist (A n f g) (A n f₀ g) +
            (dist (A n f₀ g) (A n f₀ g₀) +
              (dist (A n f₀ g₀) (P f₀ g₀) +
                (dist (P f₀ g₀) (P f₀ g) + dist (P f₀ g) (P f g)))) := by
              gcongr
              exact dist_triangle _ _ _
      _ = d1 + d2 + d3 + d4 + d5 := by
              simp [d1, d2, d3, d4, d5, add_assoc]
  have hcross :
      a1 + a2 + a4 + a5 ≤ ε / 4 := by
    set B : ℝ := (C + 1) * (Qf + Qg + 1)
    have hδ_le_eps' : δ ≤ ε / (4 * (C + 1) * (Qf + Qg + 1)) := by
      simpa [M] using hδ_le_eps
    have hB_pos : 0 < B := by
      dsimp [B]
      nlinarith [hC_pos, hQf_nonneg, hQg_nonneg]
    have hδ_le_B : δ ≤ ε / (4 * B) := by
      simpa [B, mul_assoc, mul_left_comm, mul_comm] using hδ_le_eps'
    have hmul : B * δ ≤ B * (ε / (4 * B)) := by
      exact mul_le_mul_of_nonneg_left hδ_le_B hB_pos.le
    have hcancel : B * (ε / (4 * B)) = ε / 4 := by
      field_simp [hB_pos.ne']
    calc
      a1 + a2 + a4 + a5 = B * δ := by
        dsimp [a1, a2, a4, a5, B]
        ring
      _ ≤ B * (ε / (4 * B)) := hmul
      _ = ε / 4 := hcancel
  have hsum_le : d1 + d2 + d3 + d4 + d5 ≤ a1 + a2 + a4 + a5 + d3 := by
    have h12 : d1 + d2 ≤ a1 + a2 := add_le_add hd1 hd2
    have h45 : d4 + d5 ≤ a4 + a5 := add_le_add hd4 hd5
    calc
      d1 + d2 + d3 + d4 + d5 = (d1 + d2) + d3 + (d4 + d5) := by ring
      _ ≤ (a1 + a2) + d3 + (a4 + a5) := by
          gcongr
      _ = a1 + a2 + a4 + a5 + d3 := by ring
  have hbig : dist (A n f g) (P f g) ≤ a1 + a2 + a4 + a5 + d3 := by
    exact le_trans htri hsum_le
  calc
    dist (A n f g) (P f g) ≤ a1 + a2 + a4 + a5 + d3 := hbig
    _ ≤ ε / 4 + d3 := by
      nlinarith [hcross]
    _ < ε := by
      linarith

/-! ## Covariance of the IR limit

The main payoff: combining the Green's function convergence with the
weak convergence of measures to identify the covariance of the IR limit. -/

/-- **The IR limit measure has the correct physically normalized cylinder covariance.**

If the sequence of pulled-back torus measures `ν_{Lt_n}` converges
weakly to a measure ν on cylinder configurations, and each torus
measure is Gaussian with the correct torus covariance, then ν has
covariance equal to `physicalCylinderGreen`.

**Proof strategy** (characteristic function method, same as
`torusLimit_covariance_eq`):
0. `cylinderPullbackGFF_secondMoment_eq_torus`: along the approximating sequence,
   cylinder second moments equal torus second moments on `cylinderToTorusEmbed f`.
1. Each torus measure is Gaussian: `E[e^{iω(g)}] = exp(-½ ⟨Tg,Tg⟩)` with
   `T = cylinderMassOperator`, and `⟨Tg,Tg⟩ = G_{Lt}(g,g)` for `g = embed f`
   (`second_moment_eq_covariance` + covariance = `greenFunctionBilinear`).
2. The Green's function converges: `G_{Lt}(embed f, embed f) → G_phys(f,f)`
   (`asymTorusGreen_tendsto_physicalCylinderGreen`).
3. Weak convergence: `∫ cos(ω(f)) dν_{Lt} → ∫ cos(ω(f)) dν`
4. Combining: `exp(-½ ∫(ωf)² dν) = exp(-½ G_phys(f,f))`
5. By injectivity of exp: `∫ (ωf)² dν = G_phys(f,f)` -/
theorem cylinderIRLimit_covariance_eq
    (mass : ℝ) (hmass : 0 < mass)
    (ν : Measure (Configuration (CylinderTestFunction Ls)))
    [IsProbabilityMeasure ν]
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop)
    (μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls)))
    (hμ_prob : ∀ n, IsProbabilityMeasure (μ n))
    (hμ_gauss : ∀ n (g : AsymTorusTestFunction (Lt n) Ls),
      ∫ ω : Configuration (AsymTorusTestFunction (Lt n) Ls), Real.exp (ω g) ∂(μ n) =
        Real.exp ((1 / 2) * ∫ ω, (ω g) ^ 2 ∂(μ n)))
    (hμ_cov : ∀ n (g : AsymTorusTestFunction (Lt n) Ls),
      ∫ ω : Configuration (AsymTorusTestFunction (Lt n) Ls), (ω g) ^ 2 ∂(μ n) =
        asymTorusContinuumGreen (Lt n) Ls mass hmass g g)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (f : CylinderTestFunction Ls),
      Tendsto (fun n =>
        ∫ ω, Complex.exp (Complex.I * ↑(ω f))
          ∂(cylinderPullbackMeasure (Lt (φ n)) Ls
            (μ (φ n))))
        atTop (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν)))
    (f : CylinderTestFunction Ls) :
    ∫ ω : Configuration (CylinderTestFunction Ls), (ω f) ^ 2 ∂ν =
      physicalCylinderGreen (Ls := Ls) mass hmass f f := by
  set eval_f : Configuration (CylinderTestFunction Ls) → ℝ := fun ω => ω f
  set G : ℝ := physicalCylinderGreen (Ls := Ls) mass hmass f f
  have h_eval_meas : Measurable eval_f := configuration_eval_measurable f
  let νseq : ℕ → Measure (Configuration (CylinderTestFunction Ls)) :=
    fun n => cylinderPullbackMeasure (Lt (φ n)) Ls (μ (φ n))
  have hνseq_prob : ∀ n, IsProbabilityMeasure (νseq n) := by
    intro n
    dsimp [νseq]
    have hmeas : Measurable (cylinderPullback (Lt (φ n)) Ls) :=
      configuration_measurable_of_eval_measurable _
        (fun g => configuration_eval_measurable _)
    exact Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have hνseq_gauss : ∀ n (g : CylinderTestFunction Ls),
      ∫ ω : Configuration (CylinderTestFunction Ls), Real.exp (ω g) ∂(νseq n) =
        Real.exp ((1 / 2) * ∫ ω, (ω g) ^ 2 ∂(νseq n)) := by
    intro n g
    dsimp [νseq]
    haveI := hμ_prob (φ n)
    exact cylinderPullback_isGaussian_of_torusGaussian Ls
      (Lt := Lt (φ n)) (μ := μ (φ n)) (hμ_gauss := hμ_gauss (φ n)) g
  have hνseq_cov : ∀ n,
      ∫ ω : Configuration (CylinderTestFunction Ls), (ω f) ^ 2 ∂(νseq n) =
        asymTorusContinuumGreen (Lt (φ n)) Ls mass hmass
          (cylinderToTorusEmbed (Lt (φ n)) Ls f)
          (cylinderToTorusEmbed (Lt (φ n)) Ls f) := by
    intro n
    dsimp [νseq]
    exact cylinderPullback_secondMoment_eq_asymTorusGreen Ls
      (Lt := Lt (φ n)) (μ := μ (φ n)) mass hmass
      (hμ_cov := hμ_cov (φ n)) f
  have h_push_gauss : ∀ n,
      (νseq n).map eval_f =
        ProbabilityTheory.gaussianReal 0
          (∫ ω : Configuration (CylinderTestFunction Ls), (ω f) ^ 2 ∂(νseq n)).toNNReal := by
    intro n
    haveI := hνseq_prob n
    exact GaussianField.eval_map_eq_gaussianReal (μ := νseq n) (hνseq_gauss n) f
  have hG_nonneg : 0 ≤ G := by
    simpa [G] using physicalCylinderGreen_nonneg (Ls := Ls) mass hmass f
  have h_cov_tend :
      Tendsto (fun n =>
        ∫ ω : Configuration (CylinderTestFunction Ls), (ω f) ^ 2 ∂(νseq n))
      atTop (nhds G) := by
    have hsub : Tendsto (fun n =>
        asymTorusContinuumGreen (Lt (φ n)) Ls mass hmass
          (cylinderToTorusEmbed (Lt (φ n)) Ls f)
          (cylinderToTorusEmbed (Lt (φ n)) Ls f))
        atTop (nhds G) := by
      simpa [G] using
        (asymTorusGreen_tendsto_physicalCylinderGreen
          (Ls := Ls) mass hmass f f
          (fun n => Lt (φ n)) (fun n => hLt (φ n))
          (hLt_tend.comp hφ.tendsto_atTop))
    simpa [hνseq_cov] using hsub
  have h_push_char_eq : charFun (ν.map eval_f) =
      charFun (ProbabilityTheory.gaussianReal 0 G.toNNReal) := by
    ext t
    have hcf_seq : Tendsto (fun n => charFun ((νseq n).map eval_f) t)
        atTop (nhds (charFun (ν.map eval_f) t)) := by
      have h := hconv (t • f)
      have h_eq_n : ∀ n,
          charFun ((νseq n).map eval_f) t =
            ∫ ω, Complex.exp (Complex.I * ↑(ω (t • f))) ∂(νseq n) := by
        intro n
        haveI := hνseq_prob n
        haveI : IsProbabilityMeasure ((νseq n).map eval_f) :=
          Measure.isProbabilityMeasure_map h_eval_meas.aemeasurable
        rw [charFun_apply_real, integral_map h_eval_meas.aemeasurable]
        · congr 1
          funext ω
          simp [eval_f, map_smul]
          congr 1
          ring
        · change AEStronglyMeasurable
            (fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I))
            (Measure.map eval_f (νseq n))
          exact ((by fun_prop :
            Continuous fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I)).aestronglyMeasurable)
      have h_eq_lim :
          charFun (ν.map eval_f) t =
            ∫ ω, Complex.exp (Complex.I * ↑(ω (t • f))) ∂ν := by
        haveI : IsProbabilityMeasure (ν.map eval_f) :=
          Measure.isProbabilityMeasure_map h_eval_meas.aemeasurable
        rw [charFun_apply_real, integral_map h_eval_meas.aemeasurable]
        · congr 1
          funext ω
          simp [eval_f, map_smul]
          congr 1
          ring
        · change AEStronglyMeasurable
            (fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I))
            (Measure.map eval_f ν)
          exact ((by fun_prop :
            Continuous fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I)).aestronglyMeasurable)
      have h' : Tendsto (fun n =>
          charFun ((νseq n).map eval_f) t)
          atTop (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω (t • f))) ∂ν)) := by
        simpa [h_eq_n] using h
      simpa [h_eq_lim] using h'
    have hcf_target : Tendsto (fun n => charFun ((νseq n).map eval_f) t) atTop
        (nhds (charFun (ProbabilityTheory.gaussianReal 0 G.toNNReal) t)) := by
      have h_eq_n : ∀ n,
          charFun ((νseq n).map eval_f) t =
            Complex.exp (-(∫ ω : Configuration (CylinderTestFunction Ls), (ω f) ^ 2 ∂(νseq n))
              * t ^ 2 / 2) := by
        intro n
        rw [h_push_gauss n, charFun_gaussianReal]
        congr 1
        rw [Real.coe_toNNReal _
          (integral_nonneg (fun _ : Configuration (CylinderTestFunction Ls) => sq_nonneg _))]
        push_cast
        ring
      have h_eq_lim :
          charFun (ProbabilityTheory.gaussianReal 0 G.toNNReal) t =
            Complex.exp (-G * t ^ 2 / 2) := by
        rw [charFun_gaussianReal]
        congr 1
        push_cast
        rw [Real.coe_toNNReal _ hG_nonneg]
        ring
      have h_tend_exp : Tendsto (fun n =>
          Complex.exp (-(∫ ω : Configuration (CylinderTestFunction Ls), (ω f) ^ 2 ∂(νseq n))
            * t ^ 2 / 2)) atTop
          (nhds (Complex.exp (-G * t ^ 2 / 2))) := by
        have hcont : Continuous (fun x : ℝ => Complex.exp (-x * t ^ 2 / 2)) := by
          fun_prop
        exact hcont.continuousAt.tendsto.comp h_cov_tend
      simpa [h_eq_n, h_eq_lim] using h_tend_exp
    exact tendsto_nhds_unique hcf_seq hcf_target
  have h_push_eq : ν.map eval_f = ProbabilityTheory.gaussianReal 0 G.toNNReal :=
    Measure.ext_of_charFun h_push_char_eq
  have h_second_push : ∫ x, x ^ 2 ∂(ν.map eval_f) = G := by
    rw [h_push_eq]
    have h_mean : ∫ x, x ∂(ProbabilityTheory.gaussianReal (0 : ℝ) G.toNNReal) = 0 :=
      integral_id_gaussianReal
    have h_var := variance_of_integral_eq_zero
      (measurable_id.aemeasurable
        (μ := ProbabilityTheory.gaussianReal (0 : ℝ) G.toNNReal)) h_mean
    simp only [id] at h_var
    rw [← h_var]
    have h_var_id :
        Var[id; ProbabilityTheory.gaussianReal (0 : ℝ) G.toNNReal] = (G.toNNReal : ℝ) := by
      exact variance_fun_id_gaussianReal (μ := 0) (v := G.toNNReal)
    rw [h_var_id]
    exact Real.coe_toNNReal _ hG_nonneg
  have h_second_map :
      ∫ ω : Configuration (CylinderTestFunction Ls), (ω f) ^ 2 ∂ν =
        ∫ x, x ^ 2 ∂(ν.map eval_f) := by
    exact (integral_map h_eval_meas.aemeasurable
      (continuous_pow 2).aestronglyMeasurable).symm
  rw [h_second_map, h_second_push]

end Pphi2

end
