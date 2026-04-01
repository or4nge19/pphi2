/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas

# Covariance Infrastructure: Spectral Representations and Pullback Measures

Spectral decompositions of the torus and cylinder Green's functions, pullback
measure identities, and basis approximation machinery. These are the
definitions and structural identities used by `CovarianceConvergenceProof.lean`
to prove the torus → cylinder covariance convergence.

## Main results

- `asymTorusContinuumGreen_pure_eq_tsum` — torus Green's function on pure
  tensors as a double series over spatial and temporal modes
- `cylinderGreen_pure_eq_tsum` — cylinder Green's function spectral
  decomposition (and variants with explicit kernel integrals)
- `cylinderPullbackGFF_secondMoment_eq_torus` — pullback second moment
  equals torus second moment via `cylinderPullbackMeasure_integral_sq`
- `cylinderPullback_isGaussian_of_torusGaussian` — pullback of a Gaussian
  torus measure is Gaussian on the cylinder

The convergence proofs using these identities are in
`CovarianceConvergenceProof.lean`.

## References

- Glimm-Jaffe, *Quantum Physics*, §19.1 (infinite volume limit)
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII
-/

import Pphi2.IRLimit.CylinderOS
import Pphi2.AsymTorus.AsymTorusEmbedding
import Pphi2.GeneralResults.PeriodicResolvent1D
import Pphi2.GeneralResults.ResolventFourierAnalysis
import Pphi2.GeneralResults.SchwartzCutoff
import Pphi2.TorusContinuumLimit.MeasureUniqueness
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory Filter ProbabilityTheory Complex PeriodicResolvent1D

variable (Ls : ℝ) [hLs : Fact (0 < Ls)]

/-! ## Green's function convergence

The key analytical fact: the asymmetric torus Green's function of
embedded cylinder test functions converges to the cylinder Green's
function as the temporal period Lt → ∞.

### Proof sketch (not yet formalized)

For pure tensors `f = g ⊗ h` where `g ∈ C∞(S¹_{Ls})` and `h ∈ 𝓢(ℝ)`:

1. `cylinderToTorusEmbed` maps `g ⊗ h ↦ (periodize h) ⊗ g` (periodize
   temporal factor, swap order).

2. The torus Green's function in the spatial Fourier basis is:
     `G_{Lt,Ls}(f,f) = (1/Ls) Σ_n |ĉ_n(g)|² · ∫∫ h̃_n(t) h̃_n(t')
        · cosh(ω_n(Lt/2-|t-t'|)) / (2ω_n sinh(ω_n Lt/2)) dt dt'`
   where `h̃_n` is the periodization of h restricted to mode n.

3. As Lt → ∞, `periodize(h)` converges to `h` on any compact set
   (the wrap-around terms decay like `e^{-m Lt}`), and the 1D periodic
   Green's function converges to the non-periodic one:
     `cosh(ω(Lt/2-|t|))/(2ω sinh(ωLt/2)) → e^{-ω|t|}/(2ω)`

4. Dominated convergence: the uniform bound from `torusGreen_uniform_bound`
   provides the dominating function. The series over spatial modes n
   converges uniformly because `ω_n → ∞` and Schwartz coefficients
   decay rapidly.

5. The limit equals `cylinderGreen Ls mass f g` by the spectral
   representation of the cylinder covariance. -/

private theorem resolventMultiplier_l2Inner_eq_mathlibResolventKernel_integralOn_compactDiffBox
    (ω : ℝ) (hω : 0 < ω)
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0) :
    l2InnerProduct (resolventMultiplierCLM hω h₁)
      (resolventMultiplierCLM hω h₂) =
    ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
      (h₁ p.1 * h₂ p.2) * mathlibResolventKernelReal ω (p.1 - p.2) ∂volume := by
  let I : Set ℝ := Set.Icc (-T) T
  let K : Set (ℝ × ℝ) := I ×ˢ I
  let F : ℝ → ℝ := fun t => ∫ s, mathlibResolventKernelReal ω (t - s) * h₂ s
  let G : ℝ × ℝ → ℝ := fun p =>
    (h₁ p.1 * h₂ p.2) * mathlibResolventKernelReal ω (p.1 - p.2)
  have houter :
      ∫ t, h₁ t * F t = ∫ t in I, h₁ t * F t := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ I
    · simp [I, ht]
    · have hTlt : T < |t| := by
        apply lt_of_not_ge
        intro ht'
        apply ht
        simpa [I, Set.mem_Icc, abs_le] using ht'
      have hz : h₁ t = 0 := hsupp₁ t hTlt
      simp [I, ht, hz]
  have hinner :
      ∀ t, F t = ∫ s in I, mathlibResolventKernelReal ω (t - s) * h₂ s := by
    intro t
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with s
    by_cases hs : s ∈ I
    · simp [I, hs]
    · have hTlt : T < |s| := by
        apply lt_of_not_ge
        intro hs'
        apply hs
        simpa [I, Set.mem_Icc, abs_le] using hs'
      have hz : h₂ s = 0 := hsupp₂ s hTlt
      simp [I, hs, hz]
  have hiter :
      ∫ t in I, h₁ t * F t =
        ∫ t in I, ∫ s in I, (h₁ t * h₂ s) * mathlibResolventKernelReal ω (t - s) ∂volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [hinner t, ← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    ring
  have hK_compact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hG_cont : ContinuousOn G K := by
    have hh₁ : ContinuousOn (fun p : ℝ × ℝ => h₁ p.1) K := by
      exact (h₁.continuous.comp continuous_fst).continuousOn
    have hh₂ : ContinuousOn (fun p : ℝ × ℝ => h₂ p.2) K := by
      exact (h₂.continuous.comp continuous_snd).continuousOn
    have hk : ContinuousOn (fun p : ℝ × ℝ => mathlibResolventKernelReal ω (p.1 - p.2)) K := by
      exact ((continuous_mathlibResolventKernelReal ω).comp
        (continuous_fst.sub continuous_snd)).continuousOn
    simpa [G] using (hh₁.mul hh₂).mul hk
  have hG_int :
      Integrable G ((volume.restrict I).prod (volume.restrict I)) := by
    rw [Measure.prod_restrict I I]
    simpa [K] using hG_cont.integrableOn_compact hK_compact
  calc
    l2InnerProduct (resolventMultiplierCLM hω h₁)
        (resolventMultiplierCLM hω h₂)
      = ∫ t, h₁ t * F t := by
          simpa [F] using
            resolventMultiplier_l2Inner_eq_mathlibResolventKernel_integral ω hω h₁ h₂
    _ = ∫ t in I, h₁ t * F t := houter
    _ = ∫ t in I, ∫ s in I, (h₁ t * h₂ s) * mathlibResolventKernelReal ω (t - s) ∂volume := hiter
    _ = ∫ p, G p ∂((volume.restrict I).prod (volume.restrict I)) := by
          simpa [G] using (MeasureTheory.integral_prod G hG_int).symm
    _ = ∫ p in K, G p ∂volume := by
          rw [Measure.prod_restrict I I]
          have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume := rfl
          simp [K, hvol]
    _ = ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          (h₁ p.1 * h₂ p.2) * mathlibResolventKernelReal ω (p.1 - p.2) ∂volume := by
          simp [I, K, G]

private theorem resolventMultiplier_l2Inner_eq_scaledFreeKernel_integralOn_compactDiffBox
    (ω : ℝ) (hω : 0 < ω)
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0) :
    l2InnerProduct (resolventMultiplierCLM hω h₁)
      (resolventMultiplierCLM hω h₂) =
    ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
      (h₁ p.1 * h₂ p.2) *
        (((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (p.1 - p.2)) ∂volume := by
  rw [resolventMultiplier_l2Inner_eq_mathlibResolventKernel_integralOn_compactDiffBox
    (ω := ω) (hω := hω) (h₁ := h₁) (h₂ := h₂) (T := T) hsupp₁ hsupp₂]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with p
  rw [show
    mathlibResolventKernelReal ω (p.1 - p.2) =
      ((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (p.1 - p.2) by
    simpa [mathlibResolventKernelReal] using
      PeriodicResolvent1D.mathlibResolventKernel_eq_scaled_freeKernel ω hω (p.1 - p.2)]

private theorem physicalResolventMultiplier_l2Inner_eq_freeKernel_integralOn_compactDiffBox
    (ω : ℝ) (hω : 0 < ω)
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0) :
    l2InnerProduct (physicalResolventMultiplierCLM ω hω h₁)
      (physicalResolventMultiplierCLM ω hω h₂) =
    ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
      (h₁ p.1 * h₂ p.2) * freeKernel ω (p.1 - p.2) ∂volume := by
  let c : ℝ := (2 * Real.pi : ℝ)⁻¹
  let ω' : ℝ := ω / (2 * Real.pi)
  let K : Set (ℝ × ℝ) := Set.Icc (-T) T ×ˢ Set.Icc (-T) T
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
    _ = c ^ 2 * ∫ p in K,
          (h₁ p.1 * h₂ p.2) *
            (((2 * Real.pi) ^ 2) * freeKernel ω (p.1 - p.2)) ∂volume := by
            simpa [c, ω', hfreq, K] using
              resolventMultiplier_l2Inner_eq_scaledFreeKernel_integralOn_compactDiffBox
                (ω := ω') (hω := hω') (h₁ := h₁) (h₂ := h₂)
                (T := T) hsupp₁ hsupp₂
    _ = ∫ p in K, (h₁ p.1 * h₂ p.2) * freeKernel ω (p.1 - p.2) ∂volume := by
          rw [← integral_const_mul]
          apply MeasureTheory.integral_congr_ae
          filter_upwards with p
          rw [show c ^ 2 *
            ((h₁ p.1 * h₂ p.2) * (((2 * Real.pi) ^ 2) * freeKernel ω (p.1 - p.2))) =
              (h₁ p.1 * h₂ p.2) * (c ^ 2 * (((2 * Real.pi) ^ 2) * freeKernel ω (p.1 - p.2))) by
            ring]
          rw [inv_two_pi_sq_mul_two_pi_sq]
    _ = ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          (h₁ p.1 * h₂ p.2) * freeKernel ω (p.1 - p.2) ∂volume := by
          simp [K]

private theorem resolventMultiplier_l2Inner_eq_comp_apply
    (ω : ℝ) (hω : 0 < ω) (h₁ h₂ : SchwartzMap ℝ ℝ) :
    l2InnerProduct (resolventMultiplierCLM hω h₁)
      (resolventMultiplierCLM hω h₂) =
    ∫ t, h₁ t * resolventMultiplierCLM hω (resolventMultiplierCLM hω h₂) t := by
  rw [resolventMultiplier_l2Inner_eq_inverseSymbol_integral]
  congr with t
  rw [congrArg (fun f : SchwartzMap ℝ ℝ => f t)
    (resolventMultiplierCLM_comp_apply_eq_inverseSymbol ω hω h₂)]

/-- The asymmetric torus Green form on pure tensors is the expected double mode sum. -/
theorem asymTorusContinuumGreen_pure_eq_tsum
    (Lt : ℝ) [hLt : Fact (0 < Lt)]
    (mass : ℝ) (hmass : 0 < mass)
    (fₜ gₜ : SmoothMap_Circle Lt ℝ)
    (fₓ gₓ : SmoothMap_Circle Ls ℝ) :
    asymTorusContinuumGreen Lt Ls mass hmass
      (NuclearTensorProduct.pure fₜ fₓ)
      (NuclearTensorProduct.pure gₜ gₓ) =
    ∑' p : ℕ × ℕ,
      DyninMityaginSpace.coeff p.1 fₜ *
        DyninMityaginSpace.coeff p.1 gₜ *
        DyninMityaginSpace.coeff p.2 fₓ *
        DyninMityaginSpace.coeff p.2 gₓ /
        (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) p.1 +
          HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) p.2 +
          mass ^ 2) := by
  change ∑' m, DyninMityaginSpace.coeff m (NuclearTensorProduct.pure fₜ fₓ) *
        DyninMityaginSpace.coeff m (NuclearTensorProduct.pure gₜ gₓ) /
        (HasLaplacianEigenvalues.eigenvalue
          (E := NuclearTensorProduct (SmoothMap_Circle Lt ℝ) (SmoothMap_Circle Ls ℝ)) m +
          mass ^ 2) =
      ∑' p : ℕ × ℕ,
        DyninMityaginSpace.coeff p.1 fₜ *
          DyninMityaginSpace.coeff p.1 gₜ *
          DyninMityaginSpace.coeff p.2 fₓ *
          DyninMityaginSpace.coeff p.2 gₓ /
          (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) p.1 +
            HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) p.2 +
            mass ^ 2)
  have h_term : ∀ m : ℕ,
      DyninMityaginSpace.coeff m (NuclearTensorProduct.pure fₜ fₓ) *
        DyninMityaginSpace.coeff m (NuclearTensorProduct.pure gₜ gₓ) /
        (HasLaplacianEigenvalues.eigenvalue
          (E := NuclearTensorProduct (SmoothMap_Circle Lt ℝ) (SmoothMap_Circle Ls ℝ)) m +
          mass ^ 2) =
      DyninMityaginSpace.coeff (Nat.unpair m).1 fₜ *
        DyninMityaginSpace.coeff (Nat.unpair m).1 gₜ *
        DyninMityaginSpace.coeff (Nat.unpair m).2 fₓ *
        DyninMityaginSpace.coeff (Nat.unpair m).2 gₓ /
        (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (Nat.unpair m).1 +
          HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) (Nat.unpair m).2 +
          mass ^ 2) := by
    intro m
    change (NuclearTensorProduct.pure fₜ fₓ).val m *
        (NuclearTensorProduct.pure gₜ gₓ).val m /
        (HasLaplacianEigenvalues.eigenvalue
          (E := NuclearTensorProduct (SmoothMap_Circle Lt ℝ) (SmoothMap_Circle Ls ℝ)) m +
          mass ^ 2) =
      DyninMityaginSpace.coeff (Nat.unpair m).1 fₜ *
        DyninMityaginSpace.coeff (Nat.unpair m).1 gₜ *
        DyninMityaginSpace.coeff (Nat.unpair m).2 fₓ *
        DyninMityaginSpace.coeff (Nat.unpair m).2 gₓ /
        (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (Nat.unpair m).1 +
          HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) (Nat.unpair m).2 +
          mass ^ 2)
    have ev_ntp := fun (n : ℕ) =>
      show HasLaplacianEigenvalues.eigenvalue
        (E := NuclearTensorProduct (SmoothMap_Circle Lt ℝ) (SmoothMap_Circle Ls ℝ)) n =
        HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (Nat.unpair n).1 +
          HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) (Nat.unpair n).2 from
        rfl
    simp only [NuclearTensorProduct.pure_val, ev_ntp]
    ring
  simp_rw [h_term, ← Nat.pairEquiv_symm_apply]
  exact Nat.pairEquiv.symm.tsum_eq
    (fun p : ℕ × ℕ =>
      DyninMityaginSpace.coeff p.1 fₜ *
        DyninMityaginSpace.coeff p.1 gₜ *
        DyninMityaginSpace.coeff p.2 fₓ *
        DyninMityaginSpace.coeff p.2 gₓ /
        (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) p.1 +
          HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) p.2 +
          mass ^ 2))

/-- For pure cylinder tensors, the torus Green form of the embedded test functions is exactly
the asymmetric-torus spectral sum with periodized temporal factor. -/
theorem asymTorusContinuumGreen_embed_pure_eq_tsum
    (Lt : ℝ) [hLt : Fact (0 < Lt)]
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ) :
    asymTorusContinuumGreen Lt Ls mass hmass
      (cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g₁ h₁))
      (cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g₂ h₂)) =
    ∑' p : ℕ × ℕ,
      DyninMityaginSpace.coeff p.1 (periodizeCLM Lt h₁) *
        DyninMityaginSpace.coeff p.1 (periodizeCLM Lt h₂) *
        DyninMityaginSpace.coeff p.2 g₁ *
        DyninMityaginSpace.coeff p.2 g₂ /
        (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) p.1 +
          HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) p.2 +
          mass ^ 2) := by
  rw [cylinderToTorusEmbed_pure, cylinderToTorusEmbed_pure]
  simpa using
    asymTorusContinuumGreen_pure_eq_tsum (Ls := Ls) (Lt := Lt) mass hmass
      (periodizeCLM Lt h₁) (periodizeCLM Lt h₂) g₁ g₂

/-- The embedded pure torus covariance decomposes into a spatial mode sum whose temporal factor is
the one-dimensional circle Green form with mass `ω_a = resolventFreq Ls mass a`. This is the torus
counterpart of `cylinderGreen_pure_eq_tsum_l2Inner` and isolates the remaining genuinely 1D bridge
to the explicit periodic kernel. -/
private theorem asymTorusContinuumGreen_embed_pure_eq_tsum_temporalGreen
    (Lt : ℝ) [hLt : Fact (0 < Lt)]
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ) :
    asymTorusContinuumGreen Lt Ls mass hmass
      (cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g₁ h₁))
      (cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g₂ h₂)) =
    ∑' a : ℕ,
      DyninMityaginSpace.coeff a g₁ *
        DyninMityaginSpace.coeff a g₂ *
        greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ)
          (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a)
          (periodizeCLM Lt h₁) (periodizeCLM Lt h₂) := by
  let ht₁ : SmoothMap_Circle Lt ℝ := periodizeCLM Lt h₁
  let ht₂ : SmoothMap_Circle Lt ℝ := periodizeCLM Lt h₂
  let raw : ℕ → ℕ → ℝ := fun b a =>
    DyninMityaginSpace.coeff b ht₁ *
      DyninMityaginSpace.coeff b ht₂ *
      (DyninMityaginSpace.coeff a g₁ *
          DyninMityaginSpace.coeff a g₂ /
        (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) b +
          resolventFreq Ls mass a ^ 2))
  have hraw_eq :
      asymTorusContinuumGreen Lt Ls mass hmass
        (cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g₁ h₁))
        (cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g₂ h₂)) =
      ∑' p : ℕ × ℕ, Function.uncurry raw p := by
    rw [asymTorusContinuumGreen_embed_pure_eq_tsum (Ls := Ls) (Lt := Lt)
      (mass := mass) (hmass := hmass) (g₁ := g₁) (g₂ := g₂) (h₁ := h₁) (h₂ := h₂)]
    apply tsum_congr
    rintro ⟨b, a⟩
    simp only [raw, ht₁, ht₂, Function.uncurry_apply_pair]
    have hden :
        HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) b +
          HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) a + mass ^ 2 =
        HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) b +
          resolventFreq Ls mass a ^ 2 := by
      rw [resolventFreq_sq (L := Ls) mass a]
      simp [HasLaplacianEigenvalues.eigenvalue, add_left_comm, add_comm]
    rw [hden]
    ring_nf
  have hraw_nat :
      Summable (fun m : ℕ => Function.uncurry raw (Nat.pairEquiv.symm m)) := by
    let f : AsymTorusTestFunction Lt Ls :=
      cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g₁ h₁)
    let g : AsymTorusTestFunction Lt Ls :=
      cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g₂ h₂)
    have hsum :
        Summable (fun m : ℕ =>
          DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m g /
            (HasLaplacianEigenvalues.eigenvalue
              (E := AsymTorusTestFunction Lt Ls) m + mass ^ 2)) := by
      refine
        (greenFunctionBilinear_summable (E := AsymTorusTestFunction Lt Ls) mass hmass f g).congr ?_
      intro m
      symm
      exact greenFunctionBilinear_eq_heatKernel
        (E := AsymTorusTestFunction Lt Ls) mass hmass f g m
    refine hsum.congr ?_
    intro m
    have ev_ntp :
        HasLaplacianEigenvalues.eigenvalue
          (E := AsymTorusTestFunction Lt Ls) m =
        HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (Nat.unpair m).1 +
          HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) (Nat.unpair m).2 := rfl
    have hden :
        HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (Nat.unpair m).1 +
          HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) (Nat.unpair m).2 +
          mass ^ 2 =
        HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (Nat.unpair m).1 +
          resolventFreq Ls mass (Nat.unpair m).2 ^ 2 := by
      rw [resolventFreq_sq (L := Ls) mass (Nat.unpair m).2]
      simp [HasLaplacianEigenvalues.eigenvalue, add_left_comm, add_comm]
    simp only [f, g, Nat.pairEquiv_symm_apply, cylinderToTorusEmbed_pure, ev_ntp]
    rw [hden]
    change (NuclearTensorProduct.pure ht₁ g₁).val m *
        (NuclearTensorProduct.pure ht₂ g₂).val m *
        (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (Nat.unpair m).1 +
          resolventFreq Ls mass (Nat.unpair m).2 ^ 2)⁻¹ =
      Function.uncurry raw (Nat.unpair m)
    simp [raw, ht₁, ht₂, Function.uncurry, NuclearTensorProduct.pure_val]
    ring_nf
  have hraw_summable : Summable (Function.uncurry raw) :=
    Nat.pairEquiv.symm.summable_iff.mp hraw_nat
  calc
    asymTorusContinuumGreen Lt Ls mass hmass
        (cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g₁ h₁))
        (cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g₂ h₂))
      = ∑' p : ℕ × ℕ, Function.uncurry raw p := hraw_eq
    _ = ∑' b : ℕ, ∑' a : ℕ, raw b a := by
          exact hraw_summable.tsum_prod_uncurry (fun b => hraw_summable.prod_factor b)
    _ = ∑' a : ℕ, ∑' b : ℕ, raw b a := by
          symm
          exact hraw_summable.tsum_comm
    _ = ∑' a : ℕ,
          DyninMityaginSpace.coeff a g₁ *
            DyninMityaginSpace.coeff a g₂ *
            greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ)
              (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a)
              (periodizeCLM Lt h₁) (periodizeCLM Lt h₂) := by
          apply tsum_congr
          intro a
          let c : ℝ := DyninMityaginSpace.coeff a g₁ * DyninMityaginSpace.coeff a g₂
          let temp : ℕ → ℝ := fun b =>
            DyninMityaginSpace.coeff b ht₁ *
              DyninMityaginSpace.coeff b ht₂ /
              (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) b +
                resolventFreq Ls mass a ^ 2)
          have htemp_summable : Summable temp := by
            refine
              (greenFunctionBilinear_summable (E := SmoothMap_Circle Lt ℝ)
                (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a) ht₁ ht₂).congr ?_
            intro b
            symm
            exact greenFunctionBilinear_eq_heatKernel
              (E := SmoothMap_Circle Lt ℝ) (resolventFreq Ls mass a)
              (resolventFreq_pos Ls mass hmass a) ht₁ ht₂ b
          have htemp_eq :
              greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ)
                (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a) ht₁ ht₂ =
              ∑' b : ℕ, temp b := by
            unfold greenFunctionBilinear
            apply tsum_congr
            intro b
            exact greenFunctionBilinear_eq_heatKernel
              (E := SmoothMap_Circle Lt ℝ) (resolventFreq Ls mass a)
              (resolventFreq_pos Ls mass hmass a) ht₁ ht₂ b
          calc
            (∑' b : ℕ, raw b a)
              = ∑' b : ℕ, c * temp b := by
                  apply tsum_congr
                  intro b
                  simp [raw, c, temp]
                  ring_nf
            _ = c * ∑' b : ℕ, temp b := by
                  exact htemp_summable.tsum_mul_left c
            _ = c * greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ)
                  (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a) ht₁ ht₂ := by
                  rw [htemp_eq]
            _ = DyninMityaginSpace.coeff a g₁ *
                  DyninMityaginSpace.coeff a g₂ *
                  greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ)
                    (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a) ht₁ ht₂ := by
                  simp [c]

/-- The cylinder Green form on pure tensors expands as a double sum of spatial coefficients
and transformed temporal coefficients. This isolates the remaining bridge to the explicit
free resolvent kernel in the pure-tensor case. -/
theorem cylinderGreen_pure_eq_tsum
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ) :
    cylinderGreen Ls mass hmass
      (NuclearTensorProduct.pure g₁ h₁)
      (NuclearTensorProduct.pure g₂ h₂) =
    ∑' p : ℕ × ℕ,
      (DyninMityaginSpace.coeff p.1 g₁ *
          DyninMityaginSpace.coeff p.2
            (resolventMultiplierCLM (resolventFreq_pos Ls mass hmass p.1) h₁)) *
        (DyninMityaginSpace.coeff p.1 g₂ *
          DyninMityaginSpace.coeff p.2
            (resolventMultiplierCLM (resolventFreq_pos Ls mass hmass p.1) h₂)) := by
  rw [cylinderMassOperator_inner, ell2_inner_eq_tsum]
  have h_term : ∀ m : ℕ,
      @inner ℝ ℝ _
          (((cylinderMassOperator Ls mass hmass
              (NuclearTensorProduct.pure g₁ h₁)) : ell2') m)
          (((cylinderMassOperator Ls mass hmass
              (NuclearTensorProduct.pure g₂ h₂)) : ell2') m) =
      (DyninMityaginSpace.coeff (Nat.unpair m).1 g₁ *
          DyninMityaginSpace.coeff (Nat.unpair m).2
            (resolventMultiplierCLM
              (resolventFreq_pos Ls mass hmass (Nat.unpair m).1) h₁)) *
        (DyninMityaginSpace.coeff (Nat.unpair m).1 g₂ *
          DyninMityaginSpace.coeff (Nat.unpair m).2
            (resolventMultiplierCLM
              (resolventFreq_pos Ls mass hmass (Nat.unpair m).1) h₂)) := by
    intro m
    rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
    rw [cylinderMassOperator_formula, cylinderMassOperator_formula]
    simp only [ntpSliceSchwartz_pure, map_smul, smul_eq_mul]
    ring
  simp_rw [h_term, ← Nat.pairEquiv_symm_apply]
  exact Nat.pairEquiv.symm.tsum_eq
    (fun p : ℕ × ℕ =>
      (DyninMityaginSpace.coeff p.1 g₁ *
          DyninMityaginSpace.coeff p.2
            (resolventMultiplierCLM (resolventFreq_pos Ls mass hmass p.1) h₁)) *
        (DyninMityaginSpace.coeff p.1 g₂ *
          DyninMityaginSpace.coeff p.2
            (resolventMultiplierCLM (resolventFreq_pos Ls mass hmass p.1) h₂)))

/-- The pure-tensor cylinder Green form decomposes into a spatial mode sum whose temporal factor
is the `l2InnerProduct` of the corresponding resolvent-transformed Schwartz functions. -/
theorem cylinderGreen_pure_eq_tsum_l2Inner
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ) :
    cylinderGreen Ls mass hmass
      (NuclearTensorProduct.pure g₁ h₁)
      (NuclearTensorProduct.pure g₂ h₂) =
    ∑' a : ℕ,
      DyninMityaginSpace.coeff a g₁ *
        DyninMityaginSpace.coeff a g₂ *
        l2InnerProduct
          (resolventMultiplierCLM (resolventFreq_pos Ls mass hmass a) h₁)
          (resolventMultiplierCLM (resolventFreq_pos Ls mass hmass a) h₂) := by
  let pure₁ : CylinderTestFunction Ls := NuclearTensorProduct.pure g₁ h₁
  let pure₂ : CylinderTestFunction Ls := NuclearTensorProduct.pure g₂ h₂
  let fpair : ℕ × ℕ → ℝ := fun p =>
    (DyninMityaginSpace.coeff p.1 g₁ *
        DyninMityaginSpace.coeff p.2
          (resolventMultiplierCLM (resolventFreq_pos Ls mass hmass p.1) h₁)) *
      (DyninMityaginSpace.coeff p.1 g₂ *
        DyninMityaginSpace.coeff p.2
          (resolventMultiplierCLM (resolventFreq_pos Ls mass hmass p.1) h₂))
  have hpair_eq :
      cylinderGreen Ls mass hmass pure₁ pure₂ = ∑' p : ℕ × ℕ, fpair p := by
    simpa [pure₁, pure₂, fpair] using
      cylinderGreen_pure_eq_tsum (Ls := Ls) mass hmass g₁ g₂ h₁ h₂
  have hpair_summable : Summable fpair := by
    let x : ell2' := cylinderMassOperator Ls mass hmass pure₁
    let y : ell2' := cylinderMassOperator Ls mass hmass pure₂
    have hxy : Summable (fun m : ℕ => @inner ℝ _ _ (x m) (y m)) := by
      simpa [x, y] using lp.summable_inner x y
    have hpair_nat :
        Summable (fun m : ℕ => fpair (Nat.pairEquiv.symm m)) := by
      refine hxy.congr ?_
      intro m
      simp only [fpair, x, y, pure₁, pure₂, cylinderMassOperator_formula,
        ntpSliceSchwartz_pure, Nat.pairEquiv_symm_apply, map_smul, smul_eq_mul]
      rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
      ring
    exact Nat.pairEquiv.symm.summable_iff.mp hpair_nat
  calc
    cylinderGreen Ls mass hmass pure₁ pure₂ = ∑' p : ℕ × ℕ, fpair p := hpair_eq
    _ = ∑' a : ℕ, ∑' b : ℕ, fpair (a, b) := hpair_summable.tsum_prod
    _ = ∑' a : ℕ,
          DyninMityaginSpace.coeff a g₁ *
            DyninMityaginSpace.coeff a g₂ *
            l2InnerProduct
              (resolventMultiplierCLM (resolventFreq_pos Ls mass hmass a) h₁)
              (resolventMultiplierCLM (resolventFreq_pos Ls mass hmass a) h₂) := by
          apply tsum_congr
          intro a
          let c : ℝ := DyninMityaginSpace.coeff a g₁ * DyninMityaginSpace.coeff a g₂
          let A : SchwartzMap ℝ ℝ :=
            resolventMultiplierCLM (resolventFreq_pos Ls mass hmass a) h₁
          let B : SchwartzMap ℝ ℝ :=
            resolventMultiplierCLM (resolventFreq_pos Ls mass hmass a) h₂
          have hAB : Summable (fun b : ℕ =>
              DyninMityaginSpace.coeff b A * DyninMityaginSpace.coeff b B) :=
            l2InnerProduct_summable A B
          calc
            (∑' b : ℕ, fpair (a, b))
              = ∑' b : ℕ, c * (DyninMityaginSpace.coeff b A * DyninMityaginSpace.coeff b B) := by
                  apply tsum_congr
                  intro b
                  simp [fpair, c, A, B]
                  ring
            _ = c * ∑' b : ℕ, DyninMityaginSpace.coeff b A * DyninMityaginSpace.coeff b B := by
                  exact hAB.tsum_mul_left c
            _ = c * l2InnerProduct A B := by
                  rfl
            _ = DyninMityaginSpace.coeff a g₁ *
                  DyninMityaginSpace.coeff a g₂ *
                  l2InnerProduct A B := by
                  simp [c]

/-- The pure-tensor cylinder Green form decomposes into a spatial mode sum whose temporal factor
is the bilinear form induced by the Mathlib-normalized inverse-symbol resolvent kernel. -/
theorem cylinderGreen_pure_eq_tsum_mathlibResolventKernel_integral
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ) :
    cylinderGreen Ls mass hmass
      (NuclearTensorProduct.pure g₁ h₁)
      (NuclearTensorProduct.pure g₂ h₂) =
    ∑' a : ℕ,
      DyninMityaginSpace.coeff a g₁ *
        DyninMityaginSpace.coeff a g₂ *
        (∫ t, h₁ t *
          (∫ s,
            mathlibResolventKernelReal (resolventFreq Ls mass a) (t - s) * h₂ s)) := by
  rw [cylinderGreen_pure_eq_tsum_l2Inner]
  apply tsum_congr
  intro a
  rw [resolventMultiplier_l2Inner_eq_mathlibResolventKernel_integral
    (ω := resolventFreq Ls mass a)
    (hω := resolventFreq_pos Ls mass hmass a)]

/-- For temporally compactly supported pure tensors, the cylinder Green form is a spatial mode sum
of compact-box bilinear integrals against the Mathlib-normalized inverse-symbol kernel. This is the
box-integral cylinder analogue of
`periodizedSchwartz_mul_resolventFreq_tendsto_free_integralOn_compactDiffBox`. -/
theorem cylinderGreen_pure_eq_tsum_mathlibResolventKernel_integralOn_compactDiffBox
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0) :
    cylinderGreen Ls mass hmass
      (NuclearTensorProduct.pure g₁ h₁)
      (NuclearTensorProduct.pure g₂ h₂) =
    ∑' a : ℕ,
      DyninMityaginSpace.coeff a g₁ *
        DyninMityaginSpace.coeff a g₂ *
        (∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          (h₁ p.1 * h₂ p.2) *
            mathlibResolventKernelReal (resolventFreq Ls mass a) (p.1 - p.2) ∂volume) := by
  rw [cylinderGreen_pure_eq_tsum_l2Inner]
  apply tsum_congr
  intro a
  rw [resolventMultiplier_l2Inner_eq_mathlibResolventKernel_integralOn_compactDiffBox
    (ω := resolventFreq Ls mass a)
    (hω := resolventFreq_pos Ls mass hmass a)
    (h₁ := h₁) (h₂ := h₂)
    (T := T) (hsupp₁ := hsupp₁) (hsupp₂ := hsupp₂)]

/-- Rewriting the cylinder temporal kernel using the physical free resolvent makes the Fourier
normalization discrepancy explicit: each mode involves a factor `(2π)²` and the rescaled frequency
`2π · ω_n`. -/
theorem cylinderGreen_pure_eq_tsum_scaledFreeKernel_integral
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ) :
    cylinderGreen Ls mass hmass
      (NuclearTensorProduct.pure g₁ h₁)
      (NuclearTensorProduct.pure g₂ h₂) =
    ∑' a : ℕ,
      DyninMityaginSpace.coeff a g₁ *
        DyninMityaginSpace.coeff a g₂ *
        (∫ t, h₁ t *
          (∫ s,
            (((2 * Real.pi) ^ 2) *
              freeKernel (2 * Real.pi * resolventFreq Ls mass a) (t - s)) * h₂ s)) := by
  rw [cylinderGreen_pure_eq_tsum_l2Inner]
  apply tsum_congr
  intro a
  rw [resolventMultiplier_l2Inner_eq_scaledFreeKernel_integral
    (ω := resolventFreq Ls mass a)
    (hω := resolventFreq_pos Ls mass hmass a)]

/-- Compact-support version of `cylinderGreen_pure_eq_tsum_scaledFreeKernel_integral`.

This puts the cylinder-side pure-tensor covariance in the same compact-box integral format as the
torus-side Lt→∞ theorem, while exposing the exact normalization mismatch. -/
theorem cylinderGreen_pure_eq_tsum_scaledFreeKernel_integralOn_compactDiffBox
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0) :
    cylinderGreen Ls mass hmass
      (NuclearTensorProduct.pure g₁ h₁)
      (NuclearTensorProduct.pure g₂ h₂) =
    ∑' a : ℕ,
      DyninMityaginSpace.coeff a g₁ *
        DyninMityaginSpace.coeff a g₂ *
        (∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          (h₁ p.1 * h₂ p.2) *
            (((2 * Real.pi) ^ 2) *
              freeKernel (2 * Real.pi * resolventFreq Ls mass a) (p.1 - p.2)) ∂volume) := by
  rw [cylinderGreen_pure_eq_tsum_l2Inner]
  apply tsum_congr
  intro a
  rw [resolventMultiplier_l2Inner_eq_scaledFreeKernel_integralOn_compactDiffBox
    (ω := resolventFreq Ls mass a)
    (hω := resolventFreq_pos Ls mass hmass a)
    (h₁ := h₁) (h₂ := h₂)
    (T := T) (hsupp₁ := hsupp₁) (hsupp₂ := hsupp₂)]

/-- The physically normalized pure-cylinder bilinear form obtained by replacing the temporal
resolvent multiplier with the locally corrected version `physicalResolventMultiplierCLM`. -/
private def physicalCylinderGreen_pure
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ) : ℝ :=
  ∑' a : ℕ,
    DyninMityaginSpace.coeff a g₁ *
      DyninMityaginSpace.coeff a g₂ *
      l2InnerProduct
        (physicalResolventMultiplierCLM
          (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a) h₁)
        (physicalResolventMultiplierCLM
          (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a) h₂)

/-- The corrected pure-cylinder bilinear form has the expected physical free-kernel expansion. -/
private theorem physicalCylinderGreen_pure_eq_tsum_freeKernel_integral
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ) :
    physicalCylinderGreen_pure (Ls := Ls) mass hmass g₁ g₂ h₁ h₂ =
    ∑' a : ℕ,
      DyninMityaginSpace.coeff a g₁ *
        DyninMityaginSpace.coeff a g₂ *
        (∫ t, h₁ t * (∫ s,
          freeKernel (resolventFreq Ls mass a) (t - s) * h₂ s)) := by
  unfold physicalCylinderGreen_pure
  apply tsum_congr
  intro a
  rw [physicalResolventMultiplier_l2Inner_eq_freeKernel_integral
    (ω := resolventFreq Ls mass a)
    (hω := resolventFreq_pos Ls mass hmass a)]

/-- Compact-support version of `physicalCylinderGreen_pure_eq_tsum_freeKernel_integral`. -/
private theorem physicalCylinderGreen_pure_eq_tsum_freeKernel_integralOn_compactDiffBox
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0) :
    physicalCylinderGreen_pure (Ls := Ls) mass hmass g₁ g₂ h₁ h₂ =
    ∑' a : ℕ,
      DyninMityaginSpace.coeff a g₁ *
        DyninMityaginSpace.coeff a g₂ *
        (∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          (h₁ p.1 * h₂ p.2) *
            freeKernel (resolventFreq Ls mass a) (p.1 - p.2) ∂volume) := by
  unfold physicalCylinderGreen_pure
  apply tsum_congr
  intro a
  rw [physicalResolventMultiplier_l2Inner_eq_freeKernel_integralOn_compactDiffBox
    (ω := resolventFreq Ls mass a)
    (hω := resolventFreq_pos Ls mass hmass a)
    (h₁ := h₁) (h₂ := h₂)
    (T := T) (hsupp₁ := hsupp₁) (hsupp₂ := hsupp₂)]

/-- Rescale the temporal Schwartz factor by `h(t) ↦ √(2π) h(2π t)`. -/
private def cylinderTwoPiRescale :
    CylinderTestFunction Ls →L[ℝ] CylinderTestFunction Ls :=
  nuclearTensorProduct_mapCLM
    (ContinuousLinearMap.id ℝ (SmoothMap_Circle Ls ℝ))
    schwartzTwoPiRescaleCLM

@[simp] private theorem cylinderTwoPiRescale_pure
    (g : SmoothMap_Circle Ls ℝ) (h : SchwartzMap ℝ ℝ) :
    cylinderTwoPiRescale Ls (NuclearTensorProduct.pure g h) =
      NuclearTensorProduct.pure g (schwartzTwoPiRescaleCLM h) := by
  rw [show cylinderTwoPiRescale Ls = nuclearTensorProduct_mapCLM
      (ContinuousLinearMap.id ℝ (SmoothMap_Circle Ls ℝ))
      schwartzTwoPiRescaleCLM from rfl,
    nuclearTensorProduct_mapCLM_pure, ContinuousLinearMap.id_apply]

/-- Global physically normalized cylinder covariance, obtained by pulling back `cylinderGreen`
along the explicit temporal normalization rescaling. -/
private def physicalCylinderGreen
    (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction Ls) : ℝ :=
  cylinderGreen Ls mass hmass
    (cylinderTwoPiRescale Ls f)
    (cylinderTwoPiRescale Ls g)

private theorem physicalCylinderGreen_apply_pure_eq
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ) :
    physicalCylinderGreen (Ls := Ls) mass hmass
      (NuclearTensorProduct.pure g₁ h₁)
      (NuclearTensorProduct.pure g₂ h₂) =
    physicalCylinderGreen_pure (Ls := Ls) mass hmass g₁ g₂ h₁ h₂ := by
  unfold physicalCylinderGreen physicalCylinderGreen_pure
  rw [cylinderTwoPiRescale_pure, cylinderTwoPiRescale_pure,
    cylinderGreen_pure_eq_tsum_l2Inner]
  apply tsum_congr
  intro a
  rw [resolventMultiplier_l2Inner_eq_physical_after_twoPiRescale
    (ω := resolventFreq Ls mass a)
    (hω := resolventFreq_pos Ls mass hmass a)]

/-- The cylinder Green form distributes over finite sums in the first argument. -/
theorem cylinderGreen_finset_sum_left
    {ι : Type*}
    (mass : ℝ) (hmass : 0 < mass) (s : Finset ι)
    (a : ι → ℝ) (f : ι → CylinderTestFunction Ls) (g : CylinderTestFunction Ls) :
    cylinderGreen Ls mass hmass (∑ i ∈ s, a i • f i) g =
      ∑ i ∈ s, a i * cylinderGreen Ls mass hmass (f i) g := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp [cylinderGreen]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, cylinderGreen_bilinear, ih, Finset.sum_insert hi]

/-- The cylinder Green form distributes over finite sums in both arguments. -/
theorem cylinderGreen_finset_sum
    {ι₁ ι₂ : Type*}
    (mass : ℝ) (hmass : 0 < mass) (s₁ : Finset ι₁) (s₂ : Finset ι₂)
    (a : ι₁ → ℝ) (b : ι₂ → ℝ)
    (f : ι₁ → CylinderTestFunction Ls) (g : ι₂ → CylinderTestFunction Ls) :
    cylinderGreen Ls mass hmass (∑ i ∈ s₁, a i • f i) (∑ j ∈ s₂, b j • g j) =
      ∑ i ∈ s₁, ∑ j ∈ s₂, a i * b j * cylinderGreen Ls mass hmass (f i) (g j) := by
  classical
  rw [cylinderGreen_finset_sum_left (Ls := Ls) mass hmass s₁ a f]
  congr 1
  ext i
  rw [cylinderGreen_symm, cylinderGreen_finset_sum_left (Ls := Ls) mass hmass s₂ b g]
  rw [Finset.mul_sum]
  congr 1
  ext j
  rw [cylinderGreen_symm]
  ring

private theorem physicalCylinderGreen_finset_sum
    (mass : ℝ) (hmass : 0 < mass)
    {ι₁ ι₂ : Type*}
    (s₁ : Finset ι₁) (s₂ : Finset ι₂)
    (a : ι₁ → ℝ) (b : ι₂ → ℝ)
    (f : ι₁ → CylinderTestFunction Ls) (g : ι₂ → CylinderTestFunction Ls) :
    physicalCylinderGreen (Ls := Ls) mass hmass
      (∑ i ∈ s₁, a i • f i) (∑ j ∈ s₂, b j • g j) =
    ∑ i ∈ s₁, ∑ j ∈ s₂, a i * b j * physicalCylinderGreen (Ls := Ls) mass hmass (f i) (g j) := by
  unfold physicalCylinderGreen
  simpa [map_sum, map_smul, mul_assoc, mul_left_comm, mul_comm] using
    (cylinderGreen_finset_sum (Ls := Ls) mass hmass s₁ s₂ a b
      (fun i => cylinderTwoPiRescale Ls (f i))
      (fun j => cylinderTwoPiRescale Ls (g j)))

/-- Once torus-to-cylinder covariance convergence is known for pure tensors, bilinearity
upgrades it to finite sums of pure tensors. This isolates the remaining extension step
to passing from finite-rank tensors to general cylinder test functions. -/
theorem asymTorusGreen_tendsto_cylinderGreen_finset_sum_of_pure
    (mass : ℝ) (hmass : 0 < mass)
    {ι₁ ι₂ : Type*}
    (s₁ : Finset ι₁) (s₂ : Finset ι₂)
    (a : ι₁ → ℝ) (b : ι₂ → ℝ)
    (g₁ : ι₁ → SmoothMap_Circle Ls ℝ)
    (h₁ : ι₁ → SchwartzMap ℝ ℝ)
    (g₂ : ι₂ → SmoothMap_Circle Ls ℝ)
    (h₂ : ι₂ → SchwartzMap ℝ ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hpure : ∀ i j,
      Tendsto (fun n =>
        @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
          (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
            (NuclearTensorProduct.pure (g₁ i) (h₁ i)))
          (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
            (NuclearTensorProduct.pure (g₂ j) (h₂ j))))
        atTop
        (nhds (cylinderGreen Ls mass hmass
          (NuclearTensorProduct.pure (g₁ i) (h₁ i))
          (NuclearTensorProduct.pure (g₂ j) (h₂ j))))) :
    Tendsto (fun n =>
      @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
        (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
          (∑ i ∈ s₁, a i • NuclearTensorProduct.pure (g₁ i) (h₁ i)))
        (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
          (∑ j ∈ s₂, b j • NuclearTensorProduct.pure (g₂ j) (h₂ j))))
      atTop
      (nhds (cylinderGreen Ls mass hmass
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
              cylinderGreen Ls mass hmass
                (NuclearTensorProduct.pure (g₁ i) (h₁ i))
                (NuclearTensorProduct.pure (g₂ j) (h₂ j)))) := by
    apply tendsto_finset_sum
    intro i hi
    apply tendsto_finset_sum
    intro j hj
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Filter.Tendsto.const_mul (a i * b j) (hpure i j)
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
      cylinderGreen Ls mass hmass f g =
        ∑ i ∈ s₁, ∑ j ∈ s₂,
          a i * b j *
            cylinderGreen Ls mass hmass
              (NuclearTensorProduct.pure (g₁ i) (h₁ i))
              (NuclearTensorProduct.pure (g₂ j) (h₂ j)) := by
    simpa [f, g, mul_assoc, mul_left_comm, mul_comm] using
      (cylinderGreen_finset_sum (Ls := Ls) mass hmass s₁ s₂ a b
        (fun i => NuclearTensorProduct.pure (g₁ i) (h₁ i))
        (fun j => NuclearTensorProduct.pure (g₂ j) (h₂ j)))
  rw [hleft, hright]
  exact hsum

private theorem physicalCylinderGreen_product_seminorm_bound
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ q : Seminorm ℝ (CylinderTestFunction Ls),
      Continuous q ∧
      ∀ f g : CylinderTestFunction Ls,
        |physicalCylinderGreen (Ls := Ls) mass hmass f g| ≤ q f * q g := by
  let Tphys : CylinderTestFunction Ls →L[ℝ] ell2' :=
    (GaussianField.cylinderMassOperator Ls mass hmass).comp (cylinderTwoPiRescale Ls)
  let q : Seminorm ℝ (CylinderTestFunction Ls) :=
    (normSeminorm ℝ ell2').comp Tphys.toLinearMap
  refine ⟨q, ((norm_withSeminorms ℝ ell2').continuous_seminorm 0).comp Tphys.continuous, ?_⟩
  intro f g
  simpa [physicalCylinderGreen, q, Tphys, cylinderGreen] using
    abs_real_inner_le_norm (Tphys f) (Tphys g)

private def cylinderBasisSpatial (m : ℕ) : SmoothMap_Circle Ls ℝ :=
  DyninMityaginSpace.basis (E := SmoothMap_Circle Ls ℝ) (Nat.unpair m).1

private def cylinderBasisTemporal (m : ℕ) : SchwartzMap ℝ ℝ :=
  DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) (Nat.unpair m).2

private theorem cylinderBasis_eq_pure (m : ℕ) :
    (DyninMityaginSpace.basis (E := CylinderTestFunction Ls) m) =
      NuclearTensorProduct.pure
        (cylinderBasisSpatial (Ls := Ls) m)
        (cylinderBasisTemporal m) := by
  simpa [cylinderBasisSpatial, cylinderBasisTemporal] using
    (NuclearTensorProduct.basisVec_eq_pure
      (E₁ := SmoothMap_Circle Ls ℝ) (E₂ := SchwartzMap ℝ ℝ)
      (fun n m => by simp [DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis])
      (fun n m => by simp [DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis]) m)

private def basisPurePartial
    (f : CylinderTestFunction Ls) (s : Finset ℕ) : CylinderTestFunction Ls :=
  ∑ m ∈ s, DyninMityaginSpace.coeff m f •
    NuclearTensorProduct.pure
      (cylinderBasisSpatial (Ls := Ls) m)
      (cylinderBasisTemporal m)

private def basisCutoffPartial
    (f : CylinderTestFunction Ls) (s : Finset ℕ) (N : ℕ) : CylinderTestFunction Ls :=
  ∑ m ∈ s, DyninMityaginSpace.coeff m f •
    NuclearTensorProduct.pure
      (cylinderBasisSpatial (Ls := Ls) m)
      (schwartzCutoffCLM N (cylinderBasisTemporal m))

private theorem basisPurePartial_tendsto
    (f : CylinderTestFunction Ls) :
    Tendsto (fun s : Finset ℕ => basisPurePartial (Ls := Ls) f s) atTop (nhds f) := by
  have hsum :
      Tendsto
        (fun s : Finset ℕ =>
          ∑ m ∈ s, DyninMityaginSpace.coeff m f •
            (DyninMityaginSpace.basis (E := CylinderTestFunction Ls) m))
        atTop (nhds f) := by
    simpa [HasSum, SummationFilter.unconditional_filter] using
      (DyninMityaginSpace.hasSum_basis (E := CylinderTestFunction Ls) f)
  simpa [basisPurePartial, cylinderBasis_eq_pure] using hsum

private theorem basisCutoffPartial_tendsto
    (f : CylinderTestFunction Ls) (s : Finset ℕ) :
    Tendsto (fun N => basisCutoffPartial (Ls := Ls) f s N) atTop
      (nhds (basisPurePartial (Ls := Ls) f s)) := by
  unfold basisCutoffPartial basisPurePartial
  apply tendsto_finset_sum
  intro m hm
  have htemp :
      Tendsto
        (fun N => schwartzCutoffCLM N (cylinderBasisTemporal m))
        atTop
        (nhds (cylinderBasisTemporal m)) :=
    schwartzCutoffCLM_tendsto _
  have hpure :
      Tendsto
        (fun N =>
          NuclearTensorProduct.pure
            (cylinderBasisSpatial (Ls := Ls) m)
            (schwartzCutoffCLM N (cylinderBasisTemporal m)))
        atTop
        (nhds
          (NuclearTensorProduct.pure
            (cylinderBasisSpatial (Ls := Ls) m)
            (cylinderBasisTemporal m))) := by
    exact
      (NuclearTensorProduct.pureCLM_right
        (E₁ := SmoothMap_Circle Ls ℝ) (E₂ := SchwartzMap ℝ ℝ)
        (cylinderBasisSpatial (Ls := Ls) m)).continuous.continuousAt.tendsto.comp htemp
  simpa using hpure.const_smul (DyninMityaginSpace.coeff m f)

private theorem exists_compactSupport_basisApprox
    (q : Seminorm ℝ (CylinderTestFunction Ls)) (hq : Continuous q)
    (f : CylinderTestFunction Ls) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ℕ, ∃ N : ℕ,
      q (f - basisCutoffPartial (Ls := Ls) f s N) < ε := by
  have hpure_tend := basisPurePartial_tendsto (Ls := Ls) f
  have hq0 : q (0 : CylinderTestFunction Ls) = 0 := map_zero q
  have hpure_zero :
      Tendsto (fun s : Finset ℕ => basisPurePartial (Ls := Ls) f s - f) atTop (nhds 0) := by
    simpa using
      (hpure_tend.sub
        (tendsto_const_nhds : Tendsto (fun _ : Finset ℕ => f) atTop (nhds f)))
  have hq_pure :
      Tendsto
        (fun s : Finset ℕ => q (basisPurePartial (Ls := Ls) f s - f))
        atTop (nhds 0) := by
    simpa [hq0] using
      ((hq.continuousAt : ContinuousAt q 0).tendsto.comp hpure_zero)
  have hε2 : 0 < ε / 2 := by linarith
  have hpure_ev :
      ∀ᶠ s : Finset ℕ in atTop, q (basisPurePartial (Ls := Ls) f s - f) < ε / 2 := by
    have hdist :
        ∀ᶠ s : Finset ℕ in atTop,
          dist (q (basisPurePartial (Ls := Ls) f s - f)) 0 < ε / 2 := by
      simpa [hq0] using (Metric.tendsto_nhds.mp hq_pure) (ε / 2) hε2
    filter_upwards [hdist] with s hs
    simpa [Real.dist_eq, hq0, sub_zero, abs_of_nonneg (apply_nonneg q _)] using hs
  rw [Filter.eventually_atTop] at hpure_ev
  obtain ⟨s, hs⟩ := hpure_ev
  have hcut_tend := basisCutoffPartial_tendsto (Ls := Ls) f s
  have hcut_zero :
      Tendsto
        (fun N => basisCutoffPartial (Ls := Ls) f s N - basisPurePartial (Ls := Ls) f s)
        atTop (nhds 0) := by
    simpa using
      (hcut_tend.sub
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => basisPurePartial (Ls := Ls) f s) atTop
            (nhds (basisPurePartial (Ls := Ls) f s))))
  have hq_cut :
      Tendsto
        (fun N => q (basisCutoffPartial (Ls := Ls) f s N -
          basisPurePartial (Ls := Ls) f s))
        atTop (nhds 0) := by
    simpa [hq0] using
      ((hq.continuousAt : ContinuousAt q 0).tendsto.comp hcut_zero)
  have hq_cut_ev :
      ∀ᶠ N : ℕ in atTop,
        q (basisCutoffPartial (Ls := Ls) f s N - basisPurePartial (Ls := Ls) f s) < ε / 2 := by
    have hdist :
        ∀ᶠ N : ℕ in atTop,
          dist (q (basisCutoffPartial (Ls := Ls) f s N - basisPurePartial (Ls := Ls) f s))
            0 < ε / 2 := by
      simpa [hq0] using (Metric.tendsto_nhds.mp hq_cut) (ε / 2) hε2
    filter_upwards [hdist] with N hN
    simpa [Real.dist_eq, hq0, sub_zero, abs_of_nonneg (apply_nonneg q _)] using hN
  rw [Filter.eventually_atTop] at hq_cut_ev
  obtain ⟨N, hN⟩ := hq_cut_ev
  refine ⟨s, N, ?_⟩
  have hs' : q (basisPurePartial (Ls := Ls) f s - f) < ε / 2 := hs s le_rfl
  have hN' :
      q (basisCutoffPartial (Ls := Ls) f s N - basisPurePartial (Ls := Ls) f s) < ε / 2 :=
    hN N le_rfl
  have hsym₁ :
      q (f - basisPurePartial (Ls := Ls) f s) < ε / 2 := by
    have hneg :
        f - basisPurePartial (Ls := Ls) f s =
          -(basisPurePartial (Ls := Ls) f s - f) := by
      abel
    rw [hneg, map_neg_eq_map]
    exact hs'
  have hsym₂ :
      q (basisPurePartial (Ls := Ls) f s - basisCutoffPartial (Ls := Ls) f s N) < ε / 2 := by
    have hneg :
        basisPurePartial (Ls := Ls) f s - basisCutoffPartial (Ls := Ls) f s N =
          -(basisCutoffPartial (Ls := Ls) f s N - basisPurePartial (Ls := Ls) f s) := by
      abel
    rw [hneg, map_neg_eq_map]
    exact hN'
  calc
    q (f - basisCutoffPartial (Ls := Ls) f s N)
      = q ((f - basisPurePartial (Ls := Ls) f s) +
          (basisPurePartial (Ls := Ls) f s - basisCutoffPartial (Ls := Ls) f s N)) := by
            congr 1
            abel
    _ ≤ q (f - basisPurePartial (Ls := Ls) f s) +
        q (basisPurePartial (Ls := Ls) f s - basisCutoffPartial (Ls := Ls) f s N) :=
          map_add_le_add q _ _
    _ < ε := by linarith

/-- Second moments for the pulled-back cylinder GFF equal torus second moments on embedded
test functions (`Pphi2.IRLimit.CylinderEmbedding.cylinderPullbackMeasure_integral_sq`). -/
theorem cylinderPullbackGFF_secondMoment_eq_torus
    (Lt : ℝ) [hLt : Fact (0 < Lt)]
    (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction Ls) :
    ∫ ω, (ω f) ^ 2 ∂(cylinderPullbackMeasure Lt Ls
        (GaussianField.measure (GaussianField.cylinderMassOperator Ls mass hmass))) =
    ∫ ω, (ω (cylinderToTorusEmbed Lt Ls f)) ^ 2 ∂
        (GaussianField.measure (GaussianField.cylinderMassOperator Ls mass hmass)) :=
  cylinderPullbackMeasure_integral_sq Lt Ls _ f

/-- The free cylinder Gaussian has centered Gaussian 1D marginals with variance
`cylinderGreen Ls mass hmass f f`. -/
theorem cylinderFreeMeasure_eval_map_eq_gaussianReal
    (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction Ls) :
    (GaussianField.measure (GaussianField.cylinderMassOperator Ls mass hmass)).map
      (fun ω : Configuration (CylinderTestFunction Ls) => ω f) =
    ProbabilityTheory.gaussianReal 0 (cylinderGreen Ls mass hmass f f).toNNReal := by
  simpa [cylinderGreen] using
    (GaussianField.pairing_is_gaussian
      (GaussianField.cylinderMassOperator Ls mass hmass) f)

/-- The free cylinder Gaussian reproduces `cylinderGreen` as its second moment on the
diagonal. This is the cylinder analogue of the covariance identities used in the torus
continuum limit. -/
theorem cylinderFreeMeasure_secondMoment_eq_cylinderGreen
    (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction Ls) :
    ∫ ω, (ω f) ^ 2 ∂(GaussianField.measure
        (GaussianField.cylinderMassOperator Ls mass hmass)) =
    cylinderGreen Ls mass hmass f f := by
  rw [GaussianField.second_moment_eq_covariance
      (GaussianField.cylinderMassOperator Ls mass hmass) f]
  simp [cylinderGreen]

/-- If a torus measure is Gaussian in the MGF sense, then its cylinder pullback is also
Gaussian. -/
theorem cylinderPullback_isGaussian_of_torusGaussian
    (Lt : ℝ) [hLt : Fact (0 < Lt)]
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (hμ_gauss : ∀ g : AsymTorusTestFunction Lt Ls,
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), Real.exp (ω g) ∂μ =
        Real.exp ((1 / 2) * ∫ ω, (ω g) ^ 2 ∂μ))
    (f : CylinderTestFunction Ls) :
    ∫ ω : Configuration (CylinderTestFunction Ls), Real.exp (ω f) ∂
        (cylinderPullbackMeasure Lt Ls μ) =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂(cylinderPullbackMeasure Lt Ls μ)) := by
  unfold cylinderPullbackMeasure
  have hmeas : Measurable (cylinderPullback Lt Ls) :=
    configuration_measurable_of_eval_measurable _
      (fun φ => configuration_eval_measurable _)
  have h_exp_sm : AEStronglyMeasurable
      (fun ω : Configuration (CylinderTestFunction Ls) => Real.exp (ω f))
      (Measure.map (cylinderPullback Lt Ls) μ) :=
    (Real.measurable_exp.comp (configuration_eval_measurable f)).aestronglyMeasurable
  rw [integral_map hmeas.aemeasurable h_exp_sm]
  simp_rw [cylinderPullback_eval]
  rw [hμ_gauss (cylinderToTorusEmbed Lt Ls f)]
  congr 1
  rw [← cylinderPullbackMeasure_integral_sq Lt Ls μ f]
  simp [cylinderPullbackMeasure]

/-- If a torus measure has diagonal covariance `asymTorusContinuumGreen`, then the pulled-back
cylinder measure has diagonal covariance given by the same torus Green form on embedded test
functions. -/
theorem cylinderPullback_secondMoment_eq_asymTorusGreen
    (Lt : ℝ) [hLt : Fact (0 < Lt)]
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (mass : ℝ) (hmass : 0 < mass)
    (hμ_cov : ∀ g : AsymTorusTestFunction Lt Ls,
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), (ω g) ^ 2 ∂μ =
        asymTorusContinuumGreen Lt Ls mass hmass g g)
    (f : CylinderTestFunction Ls) :
    ∫ ω : Configuration (CylinderTestFunction Ls), (ω f) ^ 2 ∂
        (cylinderPullbackMeasure Lt Ls μ) =
      asymTorusContinuumGreen Lt Ls mass hmass
        (cylinderToTorusEmbed Lt Ls f) (cylinderToTorusEmbed Lt Ls f) := by
  rw [cylinderPullbackMeasure_integral_sq Lt Ls μ f,
    hμ_cov (cylinderToTorusEmbed Lt Ls f)]


end Pphi2

end
