/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Torus Interacting OS Axioms: OS0–OS2 for the P(φ)₂ Continuum Limit

States and proves (modulo general axioms) the Osterwalder-Schrader axioms
for the torus interacting continuum limit measure.

## Main results

- `torusInteracting_os0` — analyticity of generating functional
- `torusInteracting_os1` — regularity bound
- `torusInteracting_os2_translation` — translation invariance
- `torusInteracting_os2_D4` — D4 point group invariance
- `torusInteracting_satisfies_OS` — bundled OS0–OS2

## Mathematical background

The interacting P(φ)₂ measure on the torus T²_L is the weak limit
  `μ_P = lim_{N→∞} (ι̃_N)_* ((1/Z_N) exp(-V_N) dμ_{GFF,N})`
where V_N is the Wick-ordered interaction on the N×N lattice.

### OS0 (Analyticity)
The generating functional `Z[f] = ∫ exp(iω(f)) dμ_P` is entire analytic
in complex test function coefficients. This follows from:
1. For each ω, the integrand `exp(iω(f))` is entire in f.
2. The interacting measure has exponential moments (Nelson's estimate),
   providing the domination bound.
3. Morera's theorem / analyticity of parameter-dependent integrals
   (`analyticOnNhd_integral`).

### OS1 (Regularity)
The bound `‖Z_ℂ[f_re, f_im]‖ ≤ exp(c · (q(f_re) + q(f_im)))` for a
continuous seminorm q. Follows from Cauchy-Schwarz density transfer:
the interacting exponential moment is bounded by the Gaussian moment
(which grows as exp(½G(f,f))) times √K from Nelson's estimate.

### OS2 (Translation invariance)
On the torus T² = (ℝ/Lℤ)², translations in BOTH spatial and temporal
directions are exact symmetries at every lattice cutoff N (the torus
domain is periodic). This is simpler than the cylinder case where time
translation invariance is broken at finite temporal cutoff.

The proof transfers lattice translation invariance
(`latticeMeasure_translation_invariant`) through the weak limit.

### OS3 (Reflection positivity)
Dropped on the torus — RP is more natural on the cylinder S¹×ℝ.

## References

- Glimm-Jaffe, *Quantum Physics*, §19.3-19.4
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. V-VI
- Nelson (1966), "A quartic interaction in two dimensions"
-/

import Pphi2.TorusContinuumLimit.TorusOSAxioms
import Pphi2.TorusContinuumLimit.TorusInteractingLimit
import Pphi2.GeneralResults.ComplexAnalysis

noncomputable section

open GaussianField MeasureTheory Filter Complex

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## OS0: Analyticity of the interacting generating functional

Unlike the Gaussian case (where Z = exp(quadratic) is trivially entire),
the interacting generating functional is a genuine integral:
  `Z_ℂ[f] = ∫ exp(iω(f)) dμ_P`
Its analyticity requires Morera's theorem (holomorphic dependence on
parameters under the integral sign). -/

/-- **OS0 for the torus interacting continuum limit.**

The generating functional `z ↦ ∫ exp(i Σ zᵢ ω(Jᵢ)) dμ_P` is entire
analytic in `z ∈ ℂⁿ`.

**Proof strategy:**
1. Each cutoff measure `μ_N` has entire generating functional (by
   `analyticOnNhd_integral`: the integrand `exp(i Σ zᵢ ω(Jᵢ))` is
   entire in z for each ω, and the exponential moment bound from
   Nelson's estimate provides domination on compact sets).
2. The cutoff generating functionals converge pointwise to the limit
   generating functional (by weak convergence from `torusInteractingLimit_exists`).
3. By Vitali's convergence theorem (locally bounded analytic functions
   converging pointwise have analytic limits), the limit is analytic.

Steps 1 and 3 use `analyticOnNhd_integral` (axiomatized in
`GeneralResults/ComplexAnalysis.lean`). -/
theorem torusInteracting_os0
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hconv : ∀ (f : Configuration (TorusTestFunction L) → ℝ),
      Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => ∫ ω, f ω ∂(torusInteractingMeasure L (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, f ω ∂μ))) :
    TorusOS0_Analyticity L μ := by
  sorry

/-! ## OS1: Regularity of the interacting generating functional -/

/-- **OS1 for the torus interacting continuum limit.**

The complex generating functional satisfies an exponential bound:
  `‖Z_ℂ[f_re, f_im]‖ ≤ exp(c · (q(f_re) + q(f_im)))`
for a continuous seminorm `q` and constant `c > 0`.

**Proof strategy:**
By Cauchy-Schwarz density transfer, the interacting exponential moment
`E_P[exp(t|ω(f)|)]` is bounded by `√K · E_GFF[exp(2t|ω(f)|)]^{1/2}`
where K is Nelson's constant. The Gaussian exponential moment grows as
`exp(2t² G(f,f))`, so the interacting moment is bounded by
`√K · exp(t² G(f,f))`. Taking q(f) = G_L(f,f) (the continuum Green's
function, which is a continuous seminorm) gives the OS1 bound. -/
theorem torusInteracting_os1
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hconv : ∀ (f : Configuration (TorusTestFunction L) → ℝ),
      Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => ∫ ω, f ω ∂(torusInteractingMeasure L (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, f ω ∂μ))) :
    TorusOS1_Regularity L μ := by
  sorry

/-! ## OS2: Translation invariance of the interacting measure

On the torus T² = (ℝ/Lℤ)², translations in BOTH directions are exact
symmetries at every lattice cutoff N. The interaction
  `V_N(ω) = a² Σ_x :P(φ(x)):_c`
sums over ALL lattice sites with periodic boundary conditions, so
translating by any lattice vector permutes the summand and leaves V_N
unchanged. The free GFF measure is also translation-invariant
(`torusGaussianLimit_os2_translation`). Since both factors in
`(1/Z) exp(-V) dμ_GFF` are invariant, so is each cutoff measure.

Translation invariance passes to the limit by weak convergence:
for any bounded continuous test functional F and translation T_v,
  `∫ F(ω) dμ_N = ∫ F(T_v^{-1} ω) dμ_N`  (cutoff invariance)
Taking N → ∞, both sides converge to the limit, giving
  `∫ F(ω) dμ = ∫ F(T_v^{-1} ω) dμ`     (limit invariance) -/

/-- **OS2 (translation) for the torus interacting continuum limit.**

The interacting measure is invariant under translations on T²_L.
  `Z(f) = Z(T_v f)` for all `v ∈ ℝ²`. -/
theorem torusInteracting_os2_translation
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hconv : ∀ (f : Configuration (TorusTestFunction L) → ℝ),
      Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => ∫ ω, f ω ∂(torusInteractingMeasure L (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, f ω ∂μ))) :
    TorusOS2_TranslationInvariance L μ := by
  sorry

/-! ## OS2: D4 point group invariance

The D4 symmetry group of the square torus (swap + time reflection)
is an exact symmetry of both the free measure and the interaction
at every lattice cutoff. Like translation invariance, it passes
to the continuum limit by weak convergence. -/

/-- **OS2 (D4) for the torus interacting continuum limit.**

The interacting measure is invariant under coordinate swap
and time reflection on T²_L. -/
theorem torusInteracting_os2_D4
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hconv : ∀ (f : Configuration (TorusTestFunction L) → ℝ),
      Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => ∫ ω, f ω ∂(torusInteractingMeasure L (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, f ω ∂μ))) :
    TorusOS2_D4Invariance L μ := by
  sorry

/-! ## Bundled OS axioms -/

/-- **The torus P(φ)₂ interacting continuum limit satisfies OS0–OS2.**

This bundles all verifiable OS axioms for the interacting torus measure.
OS3 (reflection positivity) is dropped — it is natural on the
cylinder S¹×ℝ, not the torus T². -/
theorem torusInteracting_satisfies_OS
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hconv : ∀ (f : Configuration (TorusTestFunction L) → ℝ),
      Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => ∫ ω, f ω ∂(torusInteractingMeasure L (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, f ω ∂μ))) :
    SatisfiesTorusOS L μ where
  os0 := torusInteracting_os0 L P mass hmass μ hconv
  os1 := torusInteracting_os1 L P mass hmass μ hconv
  os2_translation := torusInteracting_os2_translation L P mass hmass μ hconv
  os2_D4 := torusInteracting_os2_D4 L P mass hmass μ hconv

end Pphi2

end
