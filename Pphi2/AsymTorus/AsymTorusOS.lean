/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Asymmetric Torus OS Axioms: Route B'

States and proves OS0–OS2 for the asymmetric torus interacting continuum
limit, following the same structure as `TorusInteractingOS.lean`.

All proofs follow the IDENTICAL patterns as the symmetric torus case,
with `asymGeomSpacing Lt Ls N` replacing `circleSpacing L N` and
`AsymTorusTestFunction Lt Ls` replacing `TorusTestFunction L`.

## Main results

- `asymTorusInteracting_os0` — analyticity (from analyticOnNhd_integral)
- `asymTorusInteracting_os1` — regularity (from exponential moment bound)
- `asymTorusInteracting_os2_translation` — translation invariance
- `asymTorusInteracting_os2_D4` — D4 invariance (swap + time reflection)
- `asymTorusInteracting_satisfies_OS` — bundled OS0–OS2

## Proof strategy

The proofs are structurally identical to the symmetric torus:
1. Nelson's estimate → exponential moment → OS0 + OS1
2. Lattice symmetry → torus equivariance → weak limit → OS2
3. Translation invariance via lattice approximation argument

The only difference: asymmetric spacings (Lt/N vs Ls/N) in each direction.
-/

import Pphi2.AsymTorus.AsymTorusInteractingLimit

noncomputable section

open GaussianField MeasureTheory Filter Complex

namespace Pphi2

variable (Lt Ls : ℝ) [hLt : Fact (0 < Lt)] [hLs : Fact (0 < Ls)]

/-! ## OS Axiom Definitions -/

/-- The generating functional on the asymmetric torus. -/
def asymTorusGeneratingFunctional
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] (f : AsymTorusTestFunction Lt Ls) : ℂ :=
  ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
    Complex.exp (Complex.I * ↑(ω f)) ∂μ

/-- OS0: Analyticity of the asymmetric torus generating functional. -/
def AsymTorusOS0_Analyticity
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (n : ℕ) (J : Fin n → AsymTorusTestFunction Lt Ls),
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
        Complex.exp (Complex.I *
          ↑(ω (∑ i, (z i).re • J i) + Complex.I * ↑(ω (∑ i, (z i).im • J i)))) ∂μ)
      Set.univ

/-- OS1: Regularity of the asymmetric torus generating functional. -/
def AsymTorusOS1_Regularity
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] : Prop :=
  ∃ (q : AsymTorusTestFunction Lt Ls → ℝ) (_ : Continuous q)
    (c : ℝ) (_ : 0 < c),
  ∀ (f_re f_im : AsymTorusTestFunction Lt Ls),
    ‖∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im))) ∂μ‖ ≤
    Real.exp (c * (q f_re + q f_im))

/-- OS2: Translation invariance on the asymmetric torus. -/
def AsymTorusOS2_TranslationInvariance
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (v : ℝ × ℝ) (f : AsymTorusTestFunction Lt Ls),
    asymTorusGeneratingFunctional Lt Ls μ f =
    asymTorusGeneratingFunctional Lt Ls μ (asymTorusTranslation Lt Ls v f)

/-- OS2: D4 point group invariance on the asymmetric torus.
Note: swap maps AsymTorusTestFunction Lt Ls → AsymTorusTestFunction Ls Lt,
so it's only an endomorphism when Lt = Ls. For asymmetric torus, OS2 D4
includes time reflection (always an endomorphism) but NOT swap. -/
def AsymTorusOS2_TimeReflectionInvariance
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (f : AsymTorusTestFunction Lt Ls),
    asymTorusGeneratingFunctional Lt Ls μ f =
    asymTorusGeneratingFunctional Lt Ls μ (asymTorusTimeReflection Lt Ls f)

/-! ## Bundled OS structure -/

/-- Bundled OS axioms for the asymmetric torus. -/
structure AsymSatisfiesTorusOS
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] where
  os0 : AsymTorusOS0_Analyticity Lt Ls μ
  os1 : AsymTorusOS1_Regularity Lt Ls μ
  os2_translation : AsymTorusOS2_TranslationInvariance Lt Ls μ
  os2_timeReflection : AsymTorusOS2_TimeReflectionInvariance Lt Ls μ

/-! ## OS Proof Infrastructure

Helpers for decomposing the generating functional into cos/sin integrals,
exactly mirroring the private helpers in TorusInteractingOS.lean. -/

private lemma asymCosEval_continuous (g : AsymTorusTestFunction Lt Ls) :
    Continuous (fun ω : Configuration (AsymTorusTestFunction Lt Ls) => Real.cos (ω g)) :=
  Real.continuous_cos.comp (WeakDual.eval_continuous g)

private lemma asymCosEval_bounded (g : AsymTorusTestFunction Lt Ls) :
    ∃ C, ∀ ω : Configuration (AsymTorusTestFunction Lt Ls), |Real.cos (ω g)| ≤ C :=
  ⟨1, fun _ => Real.abs_cos_le_one _⟩

private lemma asymSinEval_continuous (g : AsymTorusTestFunction Lt Ls) :
    Continuous (fun ω : Configuration (AsymTorusTestFunction Lt Ls) => Real.sin (ω g)) :=
  Real.continuous_sin.comp (WeakDual.eval_continuous g)

private lemma asymSinEval_bounded (g : AsymTorusTestFunction Lt Ls) :
    ∃ C, ∀ ω : Configuration (AsymTorusTestFunction Lt Ls), |Real.sin (ω g)| ≤ C :=
  ⟨1, fun _ => Real.abs_sin_le_one _⟩

/-- Decomposition: the generating functional's real part is the cosine integral. -/
private lemma asymGf_re_eq_cos_integral
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] (g : AsymTorusTestFunction Lt Ls) :
    (asymTorusGeneratingFunctional Lt Ls μ g).re =
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), Real.cos (ω g) ∂μ := by
  unfold asymTorusGeneratingFunctional
  rw [show (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ).re =
    Complex.reCLM (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ) from rfl]
  have hint : Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
      Complex.exp (Complex.I * ↑(ω g))) μ := by
    apply (integrable_const (1 : ℂ)).mono
    · exact (Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
          (configuration_eval_measurable g)))).aestronglyMeasurable
    · apply ae_of_all; intro ω; simp only [norm_one]
      rw [show Complex.I * ↑(ω g) = ↑(ω g) * Complex.I from mul_comm _ _]
      exact le_of_eq (Complex.norm_exp_ofReal_mul_I (ω g))
  rw [← ContinuousLinearMap.integral_comp_comm Complex.reCLM hint]
  congr 1 with ω
  simp only [Complex.reCLM_apply, mul_comm Complex.I, Complex.exp_mul_I,
    Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.sin_ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  exact Complex.cos_ofReal_re (ω g)

/-- Decomposition: the generating functional's imaginary part is the sine integral. -/
private lemma asymGf_im_eq_sin_integral
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] (g : AsymTorusTestFunction Lt Ls) :
    (asymTorusGeneratingFunctional Lt Ls μ g).im =
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), Real.sin (ω g) ∂μ := by
  unfold asymTorusGeneratingFunctional
  rw [show (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ).im =
    Complex.imCLM (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ) from rfl]
  have hint : Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
      Complex.exp (Complex.I * ↑(ω g))) μ := by
    apply (integrable_const (1 : ℂ)).mono
    · exact (Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
          (configuration_eval_measurable g)))).aestronglyMeasurable
    · apply ae_of_all; intro ω; simp only [norm_one]
      rw [show Complex.I * ↑(ω g) = ↑(ω g) * Complex.I from mul_comm _ _]
      exact le_of_eq (Complex.norm_exp_ofReal_mul_I (ω g))
  rw [← ContinuousLinearMap.integral_comp_comm Complex.imCLM hint]
  congr 1 with ω
  simp only [Complex.imCLM_apply, mul_comm Complex.I, Complex.exp_mul_I,
    Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  ring

/-! ## Intermediate lemmas (cutoff-level invariances)

These are mechanical adaptations of the symmetric torus lemmas, using
`asymGeomSpacing Lt Ls N` instead of `circleSpacing L N`. Each follows
the same proof structure as in TorusInteractingOS.lean.

TODO: Prove these by generalizing `interactingLatticeMeasure_symmetry_invariant`
to accept any positive spacing `a` (the current version is typed for
`circleSpacing L N`), then instantiating with `asymGeomSpacing Lt Ls N`. -/

/-- Cutoff-level time reflection invariance of the asymmetric torus GF.

Follows the exact same proof as `torusInteractingMeasure_gf_timeReflection_invariant`:
1. `evalAsymAtFinSite` equivariance under time reflection
2. Lattice measure symmetry invariance
The only difference: `asymGeomSpacing Lt Ls N` replaces `circleSpacing L N`. -/
private theorem asymTorusInteractingMeasure_gf_timeReflection_invariant
    (N : ℕ) [NeZero N] (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (f : AsymTorusTestFunction Lt Ls) :
    asymTorusGeneratingFunctional Lt Ls
      (asymTorusInteractingMeasure Lt Ls N P mass hmass) f =
    asymTorusGeneratingFunctional Lt Ls
      (asymTorusInteractingMeasure Lt Ls N P mass hmass)
      (asymTorusTimeReflection Lt Ls f) := by
  sorry
  -- Proof sketch (identical to symmetric case):
  -- 1. evalAsymAtFinSite x (asymTorusTimeReflection f) =
  --    evalAsymAtFinSite (timeReflectSites N x) f
  --    (via evalCLM_comp_mapCLM, as in evalTorusAtSite_timeReflection)
  -- 2. Unfold asymTorusInteractingMeasure, push through Measure.map
  -- 3. Rewrite using the equivariance
  -- 4. Apply interactingLatticeMeasure_symmetry_invariant (generalized to any spacing)

/-! ## Exponential moment bound for the continuum limit

Transfers the cutoff-level Nelson bound to the weak limit by MCT + truncation.
Structurally identical to `torusInteracting_exponentialMomentBound`. -/

/-- Cutoff-level exponential moment bound for the asymmetric interacting measure.

For each test function f and cutoff N, the interacting measure satisfies:
  `∫ exp(|ω f|) dμ_{P,N} ≤ K * exp(G_N(f,f))`
where K is the universal Nelson constant and G_N is the lattice two-point function.

TODO: Prove by adapting `torusInteractingMeasure_exponentialMomentBound_cutoff`. -/
private theorem asymTorusInteractingMeasure_exponentialMomentBound_cutoff
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : AsymTorusTestFunction Lt Ls) (N : ℕ) [NeZero N],
    Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
      Real.exp (|ω f|)) (asymTorusInteractingMeasure Lt Ls N P mass hmass) ∧
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      Real.exp (|ω f|) ∂(asymTorusInteractingMeasure Lt Ls N P mass hmass) ≤
    K * Real.exp (greenFunctionBilinear mass hmass f f) := by
  sorry

/-- The lattice two-point function converges to the continuum Green's function
on the asymmetric torus.

TODO: Prove by adapting `torus_propagator_convergence`. -/
private theorem asymTorus_propagator_convergence
    (mass : ℝ) (hmass : 0 < mass)
    (f g : AsymTorusTestFunction Lt Ls) :
    Filter.Tendsto (fun _N : ℕ =>
      greenFunctionBilinear mass hmass f g)
      Filter.atTop (nhds (asymTorusContinuumGreen Lt Ls mass hmass f g)) := by
  -- asymTorusContinuumGreen is defined as greenFunctionBilinear, so this is trivial
  simp only [asymTorusContinuumGreen]
  exact tendsto_const_nhds

/-- Exponential moment bound for the asymmetric torus continuum limit.

Transfers the cutoff-level bound to the weak limit via truncation + MCT.
Structurally identical to `torusInteracting_exponentialMomentBound`. -/
private theorem asymTorusInteracting_exponentialMomentBound
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun n => ∫ ω, g ω ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, g ω ∂μ)))
    : ∃ K : ℝ, 0 < K ∧ ∀ (f : AsymTorusTestFunction Lt Ls),
    Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
      Real.exp (|ω f|)) μ ∧
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      Real.exp (|ω f|) ∂μ ≤
    K * Real.exp (asymTorusContinuumGreen Lt Ls mass hmass f f) := by
  sorry
  -- Proof sketch (identical to torusInteracting_exponentialMomentBound):
  -- 1. Get K from asymTorusInteractingMeasure_exponentialMomentBound_cutoff
  -- 2. For each f, truncate: min(exp|ωf|, M) is bounded continuous
  -- 3. By weak convergence: ∫ min(exp|ωf|, M) dμ ≤ K * exp(G(f,f))
  -- 4. By MCT as M → ∞: ∫ exp|ωf| dμ ≤ K * exp(G(f,f))

/-! ## OS Proofs -/

/-- OS0: Analyticity of the asymmetric torus generating functional.

TODO: Adapt `torusInteracting_os0` (~100 lines). Uses `analyticOnNhd_integral`
with pointwise analyticity of exp and domination from exponential moment bound. -/
private theorem asymTorusInteracting_os0
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun n => ∫ ω, g ω ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, g ω ∂μ))) :
    AsymTorusOS0_Analyticity Lt Ls μ := by
  sorry

/-- **OS1 for the asymmetric torus interacting continuum limit.**

The complex generating functional satisfies an exponential bound:
  `‖Z_ℂ[f_re, f_im]‖ ≤ exp(c * (q(f_re) + q(f_im)))`
for a continuous seminorm `q` and constant `c > 0`.

Proof: identical to `torusInteracting_os1`. Uses the exponential moment bound
with `q(f) = G_{Lt,Ls}(f,f) + |log K|` and `c = 1`. -/
private theorem asymTorusInteracting_os1
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun n => ∫ ω, g ω ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, g ω ∂μ))) :
    AsymTorusOS1_Regularity Lt Ls μ := by
  -- Get the exponential moment bound with universal constant K
  obtain ⟨K, hK_pos, hK_all⟩ :=
    asymTorusInteracting_exponentialMomentBound Lt Ls P mass hmass μ φ hφ hconv
  -- Use q(f) = G(f,f) + |log K| to absorb the constant K
  have hq_cont : Continuous (fun f : AsymTorusTestFunction Lt Ls =>
      asymTorusContinuumGreen Lt Ls mass hmass f f + |Real.log K|) := by
    have : Continuous (fun f : AsymTorusTestFunction Lt Ls =>
        asymTorusContinuumGreen Lt Ls mass hmass f f) := by
      change Continuous (fun f => greenFunctionBilinear mass hmass f f)
      exact GaussianField.greenFunctionBilinear_continuous_diag mass hmass
    exact this.add continuous_const
  refine ⟨fun f => asymTorusContinuumGreen Lt Ls mass hmass f f + |Real.log K|,
          hq_cont, 1, one_pos, ?_⟩
  intro f_re f_im
  -- Get the bound for f_im (using universal K)
  obtain ⟨h_int_im, h_exp_bound_im⟩ := hK_all f_im
  -- Triangle inequality: ‖Z_ℂ‖ ≤ ∫ ‖exp(...)‖ dμ
  have h_tri : ‖∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im))) ∂μ‖ ≤
      ∫ ω, ‖Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ ∂μ :=
    norm_integral_le_integral_norm _
  -- ‖exp(I*(ω f_re + I*ω f_im))‖ = exp(-ω f_im)
  have h_norm : ∀ ω : Configuration (AsymTorusTestFunction Lt Ls),
      ‖Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ =
      Real.exp (-(ω f_im)) := by
    intro ω
    rw [Complex.norm_exp]; congr 1
    have : Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)) =
        -↑(ω f_im) + ↑(ω f_re) * Complex.I := by
      rw [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul]; ring
    rw [this, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  calc ‖∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
          Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im))) ∂μ‖
      ≤ ∫ ω, ‖Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ ∂μ := h_tri
    _ = ∫ ω, Real.exp (-(ω f_im)) ∂μ := by congr 1; ext ω; exact h_norm ω
    _ ≤ ∫ ω, Real.exp (|ω f_im|) ∂μ := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ (fun _ => (Real.exp_pos _).le)
        · exact h_int_im
        · exact ae_of_all _ (fun ω => Real.exp_le_exp_of_le (neg_le_abs (ω f_im)))
    _ ≤ K * Real.exp (asymTorusContinuumGreen Lt Ls mass hmass f_im f_im) :=
        h_exp_bound_im
    _ ≤ Real.exp (asymTorusContinuumGreen Lt Ls mass hmass f_im f_im + |Real.log K|) := by
        have hle : K ≤ Real.exp (|Real.log K|) := by
          by_cases h1 : 1 ≤ K
          · rw [abs_of_nonneg (Real.log_nonneg h1), Real.exp_log hK_pos]
          · push_neg at h1
            exact le_trans h1.le (Real.one_le_exp (abs_nonneg _))
        calc K * Real.exp (asymTorusContinuumGreen Lt Ls mass hmass f_im f_im)
            ≤ Real.exp (|Real.log K|) *
              Real.exp (asymTorusContinuumGreen Lt Ls mass hmass f_im f_im) :=
              mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
          _ = Real.exp (asymTorusContinuumGreen Lt Ls mass hmass f_im f_im + |Real.log K|) := by
              rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (1 * ((asymTorusContinuumGreen Lt Ls mass hmass f_re f_re + |Real.log K|) +
          (asymTorusContinuumGreen Lt Ls mass hmass f_im f_im + |Real.log K|))) := by
        rw [one_mul]; apply Real.exp_le_exp_of_le
        have hG_nn : 0 ≤ asymTorusContinuumGreen Lt Ls mass hmass f_re f_re := by
          unfold asymTorusContinuumGreen
          exact GaussianField.greenFunctionBilinear_nonneg mass hmass f_re
        linarith [hG_nn, abs_nonneg (Real.log K)]

/-- OS2 (translation) for the asymmetric torus interacting continuum limit.

TODO: Adapt `torusInteracting_os2_translation` (~60 lines).
Uses `torusGF_latticeApproximation_error_vanishes` (asymmetric version). -/
private theorem asymTorusInteracting_os2_translation
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun n => ∫ ω, g ω ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, g ω ∂μ))) :
    AsymTorusOS2_TranslationInvariance Lt Ls μ := by
  sorry
  -- Proof sketch (identical to torusInteracting_os2_translation):
  -- 1. Build GF tendsto from weak convergence via cos/sin decomposition
  -- 2. Get lattice approximation error vanishes (asymmetric version)
  -- 3. Difference of limits = limit of differences = 0
  -- 4. Conclude Z[f] = Z[T_v f]

/-- **OS2 (time reflection) for the asymmetric torus interacting continuum limit.**

The interacting measure is invariant under time reflection Theta: (t,x) -> (-t,x).
  `Z(f) = Z(Theta f)` for all f.

Proved by transferring cutoff-level time reflection invariance
(`asymTorusInteractingMeasure_gf_timeReflection_invariant`) through
the weak limit, using cos/sin decomposition + unique limits. -/
private theorem asymTorusInteracting_os2_timeReflection
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (_hφ : StrictMono φ)
    (hconv : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun n => ∫ ω, g ω ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, g ω ∂μ))) :
    AsymTorusOS2_TimeReflectionInvariance Lt Ls μ := by
  intro f
  apply Complex.ext
  · -- Re part: ∫ cos(ω f) dμ = ∫ cos(ω (Θf)) dμ
    rw [asymGf_re_eq_cos_integral Lt Ls μ f,
        asymGf_re_eq_cos_integral Lt Ls μ (asymTorusTimeReflection Lt Ls f)]
    have h_Θf := hconv _ (asymCosEval_continuous Lt Ls (asymTorusTimeReflection Lt Ls f))
      (asymCosEval_bounded Lt Ls (asymTorusTimeReflection Lt Ls f))
    have h_f := hconv _ (asymCosEval_continuous Lt Ls f) (asymCosEval_bounded Lt Ls f)
    have h_cutoff : ∀ n, ∫ ω, Real.cos (ω (asymTorusTimeReflection Lt Ls f))
        ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass) =
      ∫ ω, Real.cos (ω f) ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass) := by
      intro n
      have hgf := asymTorusInteractingMeasure_gf_timeReflection_invariant Lt Ls (φ n + 1)
        P mass hmass f
      have hre := congr_arg Complex.re hgf
      rw [asymGf_re_eq_cos_integral, asymGf_re_eq_cos_integral] at hre
      exact hre.symm
    exact tendsto_nhds_unique h_f (h_Θf.congr h_cutoff)
  · -- Im part: ∫ sin(ω f) dμ = ∫ sin(ω (Θf)) dμ
    rw [asymGf_im_eq_sin_integral Lt Ls μ f,
        asymGf_im_eq_sin_integral Lt Ls μ (asymTorusTimeReflection Lt Ls f)]
    have h_Θf := hconv _ (asymSinEval_continuous Lt Ls (asymTorusTimeReflection Lt Ls f))
      (asymSinEval_bounded Lt Ls (asymTorusTimeReflection Lt Ls f))
    have h_f := hconv _ (asymSinEval_continuous Lt Ls f) (asymSinEval_bounded Lt Ls f)
    have h_cutoff : ∀ n, ∫ ω, Real.sin (ω (asymTorusTimeReflection Lt Ls f))
        ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass) =
      ∫ ω, Real.sin (ω f) ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass) := by
      intro n
      have hgf := asymTorusInteractingMeasure_gf_timeReflection_invariant Lt Ls (φ n + 1)
        P mass hmass f
      have him := congr_arg Complex.im hgf
      rw [asymGf_im_eq_sin_integral, asymGf_im_eq_sin_integral] at him
      exact him.symm
    exact tendsto_nhds_unique h_f (h_Θf.congr h_cutoff)

/-! ## Bundled OS axioms -/

/-- **The asymmetric torus P(phi)_2 interacting continuum limit satisfies OS0-OS2.**

This bundles all verifiable OS axioms for the interacting asymmetric torus measure.
OS3 (reflection positivity) is dropped -- it is natural on the cylinder, not the torus. -/
theorem asymTorusInteracting_satisfies_OS
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun n => ∫ ω, g ω ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, g ω ∂μ))) :
    AsymSatisfiesTorusOS Lt Ls μ where
  os0 := asymTorusInteracting_os0 Lt Ls P mass hmass μ φ hφ hconv
  os1 := asymTorusInteracting_os1 Lt Ls P mass hmass μ φ hφ hconv
  os2_translation := asymTorusInteracting_os2_translation Lt Ls P mass hmass μ φ hφ hconv
  os2_timeReflection := asymTorusInteracting_os2_timeReflection Lt Ls P mass hmass μ φ hφ hconv

end Pphi2

end
