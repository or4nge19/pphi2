/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas

# Covariance Convergence: Torus → Cylinder as Lt → ∞

States and proves (modulo known axioms) that the torus Green's function
of embedded cylinder test functions converges to the cylinder Green's
function as the temporal period Lt → ∞.

## Mathematical content

On the asymmetric torus T_{Lt,Ls}, the Green's function in the
mixed spectral representation (Fourier in x, position in t) is:

  `G_{Lt,Ls}((t,x),(t',x')) = (1/Ls) Σ_n e^{2πin(x-x')/Ls}
      · cosh(ω_n(Lt/2 - |t-t'|)) / (2ω_n sinh(ω_n Lt/2))`

where `ω_n = √((2πn/Ls)² + m²)` is the dispersion relation.

As Lt → ∞, `coth(ω_n Lt/2) → 1`, so each mode's 1D Green's function
converges:

  `cosh(ω_n(Lt/2 - |t|)) / (2ω_n sinh(ω_n Lt/2)) → e^{-ω_n|t|} / (2ω_n)`

The convergence is exponentially fast: the error is O(e^{-m Lt})
since `ω_n ≥ m > 0` for all n (mass gap).

At the level of test functions (bilinear forms), this gives:

  `asymTorusContinuumGreen Lt Ls mass (embed f) (embed g)
    → cylinderGreen Ls mass f g`

as Lt → ∞, where `embed = cylinderToTorusEmbed Lt Ls`.

## Main results

- `asymTorusGreen_tendsto_cylinderGreen` — covariance convergence (axiom)
- `cylinderIRLimit_covariance_eq` — the IR limit measure has the correct
  cylinder covariance

## References

- Glimm-Jaffe, *Quantum Physics*, §19.1 (infinite volume limit)
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII
-/

import Pphi2.IRLimit.CylinderOS
import Pphi2.AsymTorus.AsymTorusEmbedding

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory Filter

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

/-- **Torus Green's function converges to cylinder Green's function.**

For any cylinder test functions f, g ∈ C∞(S¹_{Ls}) ⊗̂ 𝓢(ℝ), the
asymmetric torus Green's function of the embedded test functions
converges to the cylinder Green's function as Lt → ∞.

  `G_{Lt,Ls}(embed f, embed g) → G_cyl(f, g)` as `Lt → ∞`

This is the covariance analogue of `torus_propagator_convergence`
(lattice → torus, as N → ∞). Here the convergence is from finite
temporal volume to infinite temporal volume.

**Convergence mechanism**: For each spatial mode n, the 1D periodic
resolvent kernel on [0, Lt] converges to the infinite-line kernel:
  `cosh(ω_n(Lt/2 - |t|)) / (2ω_n sinh(ω_n Lt/2)) → e^{-ω_n|t|} / (2ω_n)`
Convergence is exponentially fast: error ≤ C · e^{-m·Lt} where m is the
mass (gap), since `ω_n ≥ m` for all n.

**Axiom justification**: This requires connecting the abstract `cylinderGreen`
(defined via the axiomatized `cylinderMassOperator`) to the explicit
resolvent kernel. The content is that `cylinderMassOperator` correctly
implements the spectral decomposition
  `(Tf)_n(p) = ĉ_n(g) · ĥ(p) / √(p² + ω_n²)`
in spatial Fourier mode n, temporal Fourier variable p. -/
axiom asymTorusGreen_tendsto_cylinderGreen
    (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction Ls)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto (fun n =>
      @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
        (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _ f)
        (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _ g))
      atTop (nhds (cylinderGreen Ls mass hmass f g))

/-! ## Covariance of the IR limit

The main payoff: combining the Green's function convergence with the
weak convergence of measures to identify the covariance of the IR limit. -/

/-- **The IR limit measure has the correct cylinder covariance.**

If the sequence of pulled-back torus measures `ν_{Lt_n}` converges
weakly to a measure ν on cylinder configurations, and each torus
measure is Gaussian with the correct torus covariance, then ν has
covariance equal to `cylinderGreen`.

**Proof strategy** (characteristic function method, same as
`torusLimit_covariance_eq`):
1. Each lattice measure is Gaussian: `E[e^{iω(f)}] = exp(-½ G_{Lt}(f,f))`
2. The Green's function converges: `G_{Lt}(embed f, embed f) → G_cyl(f,f)`
3. Weak convergence: `∫ cos(ω(f)) dν_{Lt} → ∫ cos(ω(f)) dν`
4. Combining: `exp(-½ ∫(ωf)² dν) = exp(-½ G_cyl(f,f))`
5. By injectivity of exp: `∫ (ωf)² dν = G_cyl(f,f)` -/
axiom cylinderIRLimit_covariance_eq
    (mass : ℝ) (hmass : 0 < mass)
    (ν : Measure (Configuration (CylinderTestFunction Ls)))
    [IsProbabilityMeasure ν]
    -- ν is a weak limit of pulled-back Gaussian torus measures
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (f : CylinderTestFunction Ls),
      Tendsto (fun n =>
        ∫ ω, Complex.exp (Complex.I * ↑(ω f))
          ∂(cylinderPullbackMeasure (Lt (φ n)) Ls
            (GaussianField.measure
              (@GaussianField.cylinderMassOperator Ls _ mass hmass))))
        atTop (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν)))
    (f : CylinderTestFunction Ls) :
    ∫ ω : Configuration (CylinderTestFunction Ls), (ω f) ^ 2 ∂ν =
    cylinderGreen Ls mass hmass f f

/-! ## Exponential convergence rate

The mass gap m > 0 gives exponential convergence of the periodic
Green's function to the non-periodic one. This is useful for
quantitative control and is the mechanism behind `torusGreen_uniform_bound`
in `Cylinder/MethodOfImages.lean`. -/

/-- Exact wrap-around identity for the 1D periodic resolvent kernel.

The periodic kernel differs from the infinite-line kernel by the sum of the two
nearest image contributions. This is the scalar method-of-images formula behind
the torus-to-cylinder comparison. -/
private theorem periodicResolvent_sub_free_eq_wrapAround
    (ω : ℝ) (hω : 0 < ω)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) :
    Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
      Real.exp (-ω * |t|) / (2 * ω) =
    (Real.exp (-ω * (Lt - |t|)) + Real.exp (-ω * (Lt + |t|))) /
      (2 * ω * (1 - Real.exp (-ω * Lt))) := by
  set a : ℝ := ω * Lt / 2
  set b : ℝ := ω * |t|
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have hsinh_pos : 0 < Real.sinh a := by
    rw [Real.sinh_eq]
    have hnum_pos : 0 < Real.exp a - Real.exp (-a) := by
      exact sub_pos.mpr <| (Real.exp_lt_exp).2 (by linarith [ha_pos])
    nlinarith
  have hsinh_ne : Real.sinh a ≠ 0 := ne_of_gt hsinh_pos
  have hω_ne : ω ≠ 0 := ne_of_gt hω
  have hLt_exp_lt : Real.exp (-ω * Lt) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hone_pos : 0 < 1 - Real.exp (-ω * Lt) := sub_pos.mpr hLt_exp_lt
  have hone_ne : 1 - Real.exp (-ω * Lt) ≠ 0 := ne_of_gt hone_pos
  have hsplit : Real.cosh (a - b) =
      Real.sinh a * Real.exp (-b) + Real.exp (-a) * Real.cosh b := by
    have hcosh_a : Real.cosh a = Real.sinh a + Real.exp (-a) := by
      linarith [Real.cosh_sub_sinh a]
    calc
      Real.cosh (a - b)
          = Real.cosh a * Real.cosh b - Real.sinh a * Real.sinh b := by
              rw [Real.cosh_sub]
      _ = (Real.sinh a + Real.exp (-a)) * Real.cosh b - Real.sinh a * Real.sinh b := by
            rw [hcosh_a]
      _ = Real.sinh a * (Real.cosh b - Real.sinh b) + Real.exp (-a) * Real.cosh b := by
            ring
      _ = Real.sinh a * Real.exp (-b) + Real.exp (-a) * Real.cosh b := by
            rw [Real.cosh_sub_sinh]
  have hdiff :
      Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
          Real.exp (-ω * |t|) / (2 * ω) =
        Real.exp (-a) * Real.cosh b / (2 * ω * Real.sinh a) := by
    have harg : ω * (Lt / 2 - |t|) = a - b := by
      dsimp [a, b]
      ring
    rw [harg, show ω * Lt / 2 = a by rfl, hsplit]
    field_simp [hω_ne, hsinh_ne]
    ring
  have hsinh_exp : 2 * Real.sinh a = Real.exp a - Real.exp (-a) := by
    rw [Real.sinh_eq]
    ring
  have hratio :
      Real.exp (-a) / (2 * Real.sinh a) =
        Real.exp (-ω * Lt) / (1 - Real.exp (-ω * Lt)) := by
    rw [hsinh_exp, Real.exp_neg]
    set u : ℝ := Real.exp a
    have hu_ne : u ≠ 0 := by
      dsimp [u]
      exact ne_of_gt (Real.exp_pos a)
    have hratio_u :
        u⁻¹ / (u - u⁻¹) = (u * u)⁻¹ / (1 - (u * u)⁻¹) := by
      field_simp [hu_ne]
    have hu_sq : Real.exp (-ω * Lt) = (u * u)⁻¹ := by
      rw [show -ω * Lt = -(a + a) by
        dsimp [a]
        ring, Real.exp_neg, Real.exp_add, show Real.exp a = u by rfl]
    rw [hu_sq]
    simpa [u] using hratio_u
  calc
    Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
        Real.exp (-ω * |t|) / (2 * ω)
      = Real.exp (-a) * Real.cosh b / (2 * ω * Real.sinh a) := hdiff
    _ = Real.cosh b * (Real.exp (-ω * Lt) / (ω * (1 - Real.exp (-ω * Lt)))) := by
          calc
            Real.exp (-a) * Real.cosh b / (2 * ω * Real.sinh a)
                = Real.cosh b * (Real.exp (-a) / (2 * Real.sinh a)) / ω := by
                    field_simp [hω_ne, hsinh_ne]
            _ = Real.cosh b * (Real.exp (-ω * Lt) / (1 - Real.exp (-ω * Lt))) / ω := by
                  rw [hratio]
            _ = Real.cosh b * (Real.exp (-ω * Lt) / (ω * (1 - Real.exp (-ω * Lt)))) := by
                  field_simp [hω_ne, hone_ne]
    _ = ((Real.exp b + Real.exp (-b)) / 2) *
          (Real.exp (-ω * Lt) / (ω * (1 - Real.exp (-ω * Lt)))) := by
          rw [Real.cosh_eq]
    _ = (Real.exp (-ω * (Lt - |t|)) + Real.exp (-ω * (Lt + |t|))) /
          (2 * ω * (1 - Real.exp (-ω * Lt))) := by
          have hb : b = ω * |t| := by rfl
          have h₁ : Real.exp b * Real.exp (-ω * Lt) = Real.exp (-ω * (Lt - |t|)) := by
            rw [hb, ← Real.exp_add]
            congr 1
            ring
          have h₂ : Real.exp (-b) * Real.exp (-ω * Lt) = Real.exp (-ω * (Lt + |t|)) := by
            rw [hb, ← Real.exp_add]
            congr 1
            ring
          have hExpLt : Real.exp (-(ω * Lt)) = Real.exp (-ω * Lt) := by
            congr 1
            ring
          field_simp [hω_ne, hone_ne]
          rw [hExpLt]
          rw [add_mul, h₁, h₂]
          ring_nf

/-- The 1D periodic resolvent converges exponentially to the free resolvent.

For ω > 0:
  |cosh(ω(Lt/2 - |t|))/(2ω sinh(ωLt/2)) - e^{-ω|t|}/(2ω)|
    ≤ e^{-ω(Lt - |t|)} / (ω(1 - e^{-ω Lt}))

This is the standard wrap-around contribution from the method of images:
the nearest nontrivial image sits at temporal distance `Lt - |t|`.

In particular, on any fixed compact time interval the error is `O(e^{-ω Lt})`
as `Lt → ∞`. A cleaner half-period bound is stated separately in
`periodicResolvent_convergence_rate_uniform`. -/
theorem periodicResolvent_convergence_rate
    (ω : ℝ) (hω : 0 < ω)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) :
    |Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
     Real.exp (-ω * |t|) / (2 * ω)| ≤
    Real.exp (-ω * (Lt - |t|)) /
      (ω * (1 - Real.exp (-ω * Lt))) := by
  have hLt_exp_lt : Real.exp (-ω * Lt) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hone_pos : 0 < 1 - Real.exp (-ω * Lt) := sub_pos.mpr hLt_exp_lt
  have hω_ne : ω ≠ 0 := ne_of_gt hω
  have hone_ne : 1 - Real.exp (-ω * Lt) ≠ 0 := ne_of_gt hone_pos
  rw [periodicResolvent_sub_free_eq_wrapAround ω hω t Lt hLt, abs_of_nonneg]
  · have hterm_nonneg : 0 ≤ Real.exp (-ω * (Lt + |t|)) := le_of_lt (Real.exp_pos _)
    have hterm_le : Real.exp (-ω * (Lt + |t|)) ≤ Real.exp (-ω * (Lt - |t|)) := by
      exact (Real.exp_le_exp).2 (by nlinarith [abs_nonneg t, hω])
    have hsum_le :
        Real.exp (-ω * (Lt - |t|)) + Real.exp (-ω * (Lt + |t|)) ≤
          2 * Real.exp (-ω * (Lt - |t|)) := by
      nlinarith
    have hden_pos : 0 < 2 * ω * (1 - Real.exp (-ω * Lt)) := by
      positivity
    have hcancel :
        (2 * Real.exp (-ω * (Lt - |t|))) / (2 * ω * (1 - Real.exp (-ω * Lt))) =
          Real.exp (-ω * (Lt - |t|)) / (ω * (1 - Real.exp (-ω * Lt))) := by
      field_simp [hω_ne, hone_ne]
    exact (div_le_div_of_nonneg_right hsum_le hden_pos.le).trans_eq hcancel
  · positivity

/-- Uniform half-period decay for the periodic resolvent error.

On the principal strip `|t| < Lt / 2`, the nearest image lies at distance at
least `Lt / 2`, so the method-of-images error is uniformly `O(e^{-ω Lt / 2})`. -/
theorem periodicResolvent_convergence_rate_uniform
    (ω : ℝ) (hω : 0 < ω)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) (ht : |t| < Lt / 2) :
    |Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
      Real.exp (-ω * |t|) / (2 * ω)| ≤
    Real.exp (-ω * Lt / 2) /
      (ω * (1 - Real.exp (-ω * Lt))) := by
  refine (periodicResolvent_convergence_rate ω hω t Lt hLt).trans ?_
  have hden_pos : 0 < ω * (1 - Real.exp (-ω * Lt)) := by
    have hLt_exp_lt : Real.exp (-ω * Lt) < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith
    exact mul_pos hω (sub_pos.mpr hLt_exp_lt)
  apply div_le_div_of_nonneg_right
  · apply (Real.exp_le_exp).2
    nlinarith
  · exact hden_pos.le

/-- Uniform mass-gap control of the periodic resolvent error.

If the mode frequency satisfies `mass ≤ ω`, then the wrap-around error is
bounded by the universal mass-gap envelope obtained by replacing `ω` with the
lowest possible frequency `mass`. -/
theorem periodicResolvent_convergence_rate_uniform_mass_gap
    (ω mass : ℝ) (hmass : 0 < mass) (hω : mass ≤ ω)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) (ht : |t| < Lt / 2) :
    |Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
      Real.exp (-ω * |t|) / (2 * ω)| ≤
    Real.exp (-mass * Lt / 2) /
      (mass * (1 - Real.exp (-mass * Lt))) := by
  have hω_pos : 0 < ω := lt_of_lt_of_le hmass hω
  have hmass_exp_lt : Real.exp (-mass * Lt) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hω_exp_lt : Real.exp (-ω * Lt) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hω_den_nonneg : 0 ≤ ω * (1 - Real.exp (-ω * Lt)) := by
    exact mul_nonneg hω_pos.le (sub_nonneg.mpr hω_exp_lt.le)
  have hmass_den_pos : 0 < mass * (1 - Real.exp (-mass * Lt)) := by
    exact mul_pos hmass (sub_pos.mpr hmass_exp_lt)
  have hnum_le :
      Real.exp (-ω * Lt / 2) ≤ Real.exp (-mass * Lt / 2) := by
    apply (Real.exp_le_exp).2
    nlinarith
  have hsub_le :
      1 - Real.exp (-mass * Lt) ≤ 1 - Real.exp (-ω * Lt) := by
    have hexp_le : Real.exp (-ω * Lt) ≤ Real.exp (-mass * Lt) := by
      apply (Real.exp_le_exp).2
      nlinarith
    linarith
  have hden_le :
      mass * (1 - Real.exp (-mass * Lt)) ≤
        ω * (1 - Real.exp (-ω * Lt)) := by
    exact mul_le_mul hω hsub_le (sub_nonneg.mpr hmass_exp_lt.le) hω_pos.le
  calc
    |Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
        Real.exp (-ω * |t|) / (2 * ω)|
      ≤ Real.exp (-ω * Lt / 2) / (ω * (1 - Real.exp (-ω * Lt))) :=
        periodicResolvent_convergence_rate_uniform ω hω_pos t Lt hLt ht
    _ ≤ Real.exp (-mass * Lt / 2) / (ω * (1 - Real.exp (-ω * Lt))) :=
        div_le_div_of_nonneg_right hnum_le hω_den_nonneg
    _ ≤ Real.exp (-mass * Lt / 2) / (mass * (1 - Real.exp (-mass * Lt))) :=
        div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos _)) hmass_den_pos hden_le

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
  exact periodicResolvent_convergence_rate_uniform_mass_gap
    (ω := resolventFreq Ls mass n) (mass := mass) hmass
    (resolventFreq_mass_le Ls mass hmass.le n) t Lt hLt ht

/-- The mass-gap envelope for the periodic resolvent error tends to zero as
`Lt → ∞`. -/
private theorem periodicResolvent_uniform_mass_gap_bound_tendsto_zero
    (mass : ℝ) (hmass : 0 < mass)
    (Lt : ℕ → ℝ)
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto
      (fun n =>
        Real.exp (-mass * Lt n / 2) /
          (mass * (1 - Real.exp (-mass * Lt n))))
      atTop (nhds 0) := by
  have hmass_ne : mass ≠ 0 := ne_of_gt hmass
  have hhalf_pos : 0 < mass / 2 := by positivity
  have hneg_tend : Tendsto (fun n => -(mass / 2) * Lt n) atTop atBot := by
    refine Filter.tendsto_atBot.mpr ?_
    intro b
    filter_upwards [(Filter.tendsto_atTop.mp hLt_tend) (-b / (mass / 2))] with n hn
    have hmul : -b ≤ Lt n * (mass / 2) := by
      rw [div_le_iff₀ hhalf_pos] at hn
      simpa [mul_comm, mul_left_comm, mul_assoc] using hn
    nlinarith
  have hnum_tend :
      Tendsto (fun n => Real.exp (-mass * Lt n / 2)) atTop (nhds 0) := by
    have hfun : (fun n => Real.exp (-mass * Lt n / 2)) =
        fun n => Real.exp (-(mass / 2) * Lt n) := by
      funext n
      congr 1
      ring
    rw [hfun]
    exact Real.tendsto_exp_atBot.comp hneg_tend
  have hden_tend :
      Tendsto (fun n => mass * (1 - Real.exp (-mass * Lt n))) atTop (nhds mass) := by
    have hneg_mass_tend : Tendsto (fun n => -mass * Lt n) atTop atBot := by
      refine Filter.tendsto_atBot.mpr ?_
      intro b
      filter_upwards [(Filter.tendsto_atTop.mp hLt_tend) (-b / mass)] with n hn
      have hmul : -b ≤ Lt n * mass := by
        rw [div_le_iff₀ hmass] at hn
        simpa [mul_comm, mul_left_comm, mul_assoc] using hn
      nlinarith
    have hexp_tend : Tendsto (fun n => Real.exp (-mass * Lt n)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp hneg_mass_tend
    have hsub_tend :
        Tendsto (fun n => 1 - Real.exp (-mass * Lt n)) atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub hexp_tend
    simpa using Filter.Tendsto.const_mul mass hsub_tend
  simpa [hmass_ne] using hnum_tend.div hden_tend hmass_ne

/-- The explicit wrap-around error bound tends to zero as `Lt → ∞`. -/
private theorem periodicResolvent_error_tendsto_zero
    (ω : ℝ) (hω : 0 < ω) (t : ℝ)
    (Lt : ℕ → ℝ)
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto
      (fun n =>
        Real.exp (-ω * (Lt n - |t|)) /
          (ω * (1 - Real.exp (-ω * Lt n))))
      atTop (nhds 0) := by
  have hω_ne : ω ≠ 0 := ne_of_gt hω
  have hneg_tend : Tendsto (fun n => -ω * Lt n) atTop atBot := by
    refine Filter.tendsto_atBot.mpr ?_
    intro b
    filter_upwards [(Filter.tendsto_atTop.mp hLt_tend) (-b / ω)] with n hn
    have hmul : -b ≤ Lt n * ω := by
      rw [div_le_iff₀ hω] at hn
      simpa [mul_comm, mul_left_comm, mul_assoc] using hn
    nlinarith
  have hexp_tend : Tendsto (fun n => Real.exp (-ω * Lt n)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hneg_tend
  have hnum_tend :
      Tendsto (fun n => Real.exp (-ω * (Lt n - |t|))) atTop (nhds 0) := by
    have hscaled :
        Tendsto (fun n => Real.exp (ω * |t|) * Real.exp (-ω * Lt n))
          atTop (nhds (Real.exp (ω * |t|) * 0)) :=
      Filter.Tendsto.const_mul (Real.exp (ω * |t|)) hexp_tend
    have hfun :
        (fun n => Real.exp (-ω * (Lt n - |t|))) =
          fun n => Real.exp (ω * |t|) * Real.exp (-ω * Lt n) := by
      funext n
      rw [show -ω * (Lt n - |t|) = ω * |t| + (-ω * Lt n) by ring, Real.exp_add]
    rw [hfun]
    simpa using hscaled
  have hden_tend :
      Tendsto (fun n => ω * (1 - Real.exp (-ω * Lt n))) atTop (nhds ω) := by
    have hsub_tend : Tendsto (fun n => 1 - Real.exp (-ω * Lt n)) atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub hexp_tend
    simpa using Filter.Tendsto.const_mul ω hsub_tend
  simpa [hω_ne] using hnum_tend.div hden_tend hω_ne

/-- For fixed `ω > 0` and `t`, the periodic 1D resolvent kernel converges to
the free resolvent kernel as `Lt → ∞`. -/
theorem periodicResolvent_tendsto_free
    (ω : ℝ) (hω : 0 < ω) (t : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto
      (fun n =>
        Real.cosh (ω * (Lt n / 2 - |t|)) /
          (2 * ω * Real.sinh (ω * Lt n / 2)))
      atTop (nhds (Real.exp (-ω * |t|) / (2 * ω))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set kernel : ℕ → ℝ := fun n =>
    Real.cosh (ω * (Lt n / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt n / 2))
  set free : ℝ := Real.exp (-ω * |t|) / (2 * ω)
  set err : ℕ → ℝ := fun n =>
    Real.exp (-ω * (Lt n - |t|)) /
      (ω * (1 - Real.exp (-ω * Lt n)))
  have herr_tend : Tendsto err atTop (nhds 0) :=
    periodicResolvent_error_tendsto_zero ω hω t Lt hLt_tend
  have hbound : ∀ n, |kernel n - free| ≤ err n := by
    intro n
    exact periodicResolvent_convergence_rate ω hω t (Lt n) (hLt n).out
  have habs_tend : Tendsto (fun n => |kernel n - free|) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds herr_tend
      (fun n => abs_nonneg _) hbound
  simpa [kernel, free, Real.norm_eq_abs] using habs_tend

end Pphi2

end
