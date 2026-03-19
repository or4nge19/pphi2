/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cylinder Interacting OS Axioms

Verifies that the P(φ)₂ interacting measure on S¹_L × ℝ satisfies
the Osterwalder-Schrader axioms OS0–OS3.

## Main results

- `cylinderInteracting_satisfies_OS` — the interacting measure satisfies OS0–OS3

## Mathematical background

The OS axioms for the interacting measure follow from:
- **OS0 (Analyticity)**: From uniform L^p bounds on Schwinger functions
  (via density transfer from hypercontractivity)
- **OS1 (Regularity)**: From exponential moment bounds
- **OS2 (Invariance)**: From translation invariance of the interaction
  V_{Λ,T} under spatial translations on S¹_L
- **OS3 (Reflection Positivity)**: From RP of each cutoff measure
  (via `cylinderLattice_rp`) preserved under weak limits
  (via `cylinderMatrixRP_of_weakLimit`, already proved)

## References

- Osterwalder-Schrader (1973, 1975)
- Glimm-Jaffe, *Quantum Physics*, Ch. 19
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII, IX
-/

import Pphi2.CylinderContinuumLimit.CylinderIRRemoval
import Pphi2.CylinderContinuumLimit.CylinderOSAxioms

open GaussianField MeasureTheory

noncomputable section

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## OS axioms for the interacting measure

Each axiom is verified for the P(φ)₂ measure `cylinderMeasure L P mass hmass`
constructed as the UV + IR limit. The proofs transfer properties from the
cutoff measures via weak limit arguments. -/

/-- **OS0 for the interacting measure**: the generating functional is analytic.

**Analytical content**: The complex generating functional
  `Z_ℂ[Σ zᵢJᵢ] = ∫ exp(i Σ zᵢ ω(Jᵢ)) dμ_V`
is entire analytic in `z ∈ ℂⁿ`.

**Proof sketch** (not yet formalized):
1. For each cutoff measure μ_{Λ,T}, the density transfer gives
   `∫ exp(t|ω(f)|) dμ_{Λ,T} ≤ C(t,f)` for t in a strip around 0,
   uniformly in Λ (from `cylinderBoltzmannWeight_sq_integrable` +
   Gaussian exponential moments).
2. This uniform exponential moment bound passes to the UV limit μ_T
   and the IR limit μ by weak convergence of Laplace transforms.
3. Exponential moments in a strip ⟹ moment generating function analytic
   in that strip, and the strip width is independent of the test functions
   (it depends only on the mass and coupling), giving analyticity on ℂⁿ.

**Why axiom**: Requires Vitali convergence theorem for analytic functions
under weak limits, plus careful tracking of exponential moment bounds
through two limit procedures. -/
axiom cylinderInteracting_os0
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    @CylinderOS0_Analyticity L hL (cylinderMeasure L P mass hmass)
      (cylinderMeasure_isProbability L P mass hmass)

/-- **OS1 for the interacting measure**: regularity bound on generating functional.

  `‖Z_ℂ[f_re, f_im]‖ ≤ exp(C · (q(f_re) + q(f_im)))`

where `q(f) = ∫ |ω(f)|² dμ` is the second moment seminorm.

**Analytical content**: The generating functional satisfies an
exponential bound controlled by a continuous seminorm on test functions.

**Proof sketch** (not yet formalized):
1. For the free measure: `cylinderGaussian_os1` gives the bound with
   `q(f) = G_L(f,f)` and `c = 1/2`.
2. For the interacting measure: density transfer
   (`cylinderDensityTransfer`) converts `∫ exp(t ω(f_im)) dμ_V` to
   `≤ √K · (∫ exp(2t ω(f_im)) dμ_free)^{1/2}`, which by the Gaussian
   MGF is `≤ √K · exp(t² G(f_im, f_im))`.
3. The seminorm `q(f) = G_L(f,f)` (cylinder Green's function) is
   continuous by `cylinderGreen_continuous_diag`.
4. The bound transfers through the UV and IR limits since
   `cylinderMeasure_weakLimit` preserves bounded continuous integrals.

**Why axiom**: Requires careful bookkeeping of constants through density
transfer and two weak limit procedures. The Gaussian case is proved
(`cylinderGaussian_os1`); extending to the interacting case is
routine but technically involved. -/
axiom cylinderInteracting_os1
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    @CylinderOS1_Regularity L hL (cylinderMeasure L P mass hmass)
      (cylinderMeasure_isProbability L P mass hmass)

/-- **OS2 (spatial) for the interacting measure**: invariance under
spatial translations on S¹_L.

  `Z(f) = Z(T_v f)` for all `v ∈ ℝ` (equivalently `v ∈ S¹_L`).

**Analytical content**: The interacting measure is invariant under
spatial translations `θ ↦ θ + v` on the circle S¹_L.

**Proof sketch** (not yet formalized):
1. The free measure μ_free is spatially translation-invariant
   (proved via `cylinderGaussian_os2_spatial`: the Green's function
   `G_L(f,g) = G_L(T_v f, T_v g)` by `cylinderGreen_spatialTranslation_invariant`).
2. The interaction `V_{Λ,T}(ω) = ∫₀ᴸ ∫₋ᵀᵀ :P(φ_Λ(θ,t)): dt dθ` is
   manifestly invariant under `θ → θ + v` because:
   - The integrand `:P(φ_Λ(θ+v,t)):` at shifted point equals the
     integrand at θ evaluated on the shifted field
   - Integration over the full circle `[0,L]` with periodic boundary
     conditions absorbs the shift
3. Since both μ_free and V are spatially invariant, each cutoff measure
   `μ_{Λ,T} = (1/Z) exp(-V) dμ_free` is invariant.
4. Invariance of `Z(f) = ∫ cos(ω(f)) dμ` passes through weak limits
   (bounded continuous functional), so the UV limit μ_T and IR limit
   μ inherit spatial translation invariance.

**Why axiom**: Requires formalization of `V_{Λ,T}` invariance under
spatial translation (change of variables in the θ integral) and
transfer through two weak limits. -/
axiom cylinderInteracting_os2_spatial
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    @CylinderOS2_SpatialTranslationInvariance L hL (cylinderMeasure L P mass hmass)
      (cylinderMeasure_isProbability L P mass hmass)

/-- **OS2 (temporal) for the interacting measure**: invariance under
temporal translations `t ↦ t + τ`.

  `Z(f) = Z(T_τ f)` for all `τ ∈ ℝ`.

**Analytical content**: Time translation invariance, which is BROKEN at
finite temporal cutoff T, is restored in the infinite-volume limit T → ∞.

**Proof sketch** (not yet formalized):
1. The free measure μ_free is time-translation invariant (proved via
   `cylinderGaussian_os2_time`).
2. For finite T, the interaction `V_{Λ,T} = ∫₀ᴸ ∫₋ᵀᵀ :P(φ_Λ(θ,t)): dt dθ`
   is NOT time-translation invariant: shifting by τ changes the domain
   from `[-T,T]` to `[-T+τ, T+τ]`.
3. However, as T → ∞, for any fixed τ and test function f supported in
   a compact time interval:
     `|Z_{μ_T}(f) - Z_{μ_T}(T_τ f)| → 0`
   because the "boundary terms" (the difference between V on `[-T,T]`
   and on `[-T+τ, T+τ]`) have measure going to zero.
4. The limit measure μ = lim_{T→∞} μ_T inherits exact time translation
   invariance by uniqueness of limits.

**Why axiom**: This is the most analytically subtle of the OS2 axioms.
It requires showing that the boundary effects of the IR cutoff vanish
in the T → ∞ limit, which involves uniform estimates on the interaction
density near the temporal boundary. See Simon, Ch. VIII, Theorem VIII.13
for the argument in the P(φ)₂ case. -/
axiom cylinderInteracting_os2_time
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    @CylinderOS2_TimeTranslationInvariance L hL (cylinderMeasure L P mass hmass)
      (cylinderMeasure_isProbability L P mass hmass)

/-- **OS2 (time reflection) for the interacting measure**: invariance
under time reflection `Θ : t ↦ -t`.

  `Z(f) = Z(Θf)` for all test functions `f`.

**Analytical content**: The interacting measure is invariant under
the time reflection `Θ : (θ, t) ↦ (θ, -t)`.

**Proof sketch** (not yet formalized):
1. The free measure μ_free is Θ-invariant (proved via
   `cylinderGaussian_os2_reflection`).
2. The interaction `V_{Λ,T}(ω)` is Θ-invariant because:
   - `:P(φ_Λ(θ,-t)):_{c_Λ}` = `:P(φ_Λ(θ,t)):_{c_Λ}` when evaluated
     on the Θ-reflected field, since the free field distribution is
     Θ-invariant and `c_Λ` doesn't depend on t
   - The temporal domain `[-T,T]` is symmetric under `t ↦ -t`
3. Since both μ_free and `exp(-V)` are Θ-invariant, each cutoff measure
   `μ_{Λ,T} = (1/Z) exp(-V) dμ_free` is Θ-invariant.
4. Θ-invariance passes through weak limits (bounded continuous
   functionals), so both the UV limit μ_T and the IR limit μ
   inherit time reflection invariance.

**Why axiom**: Requires formalization of the Θ-invariance of the
interaction functional (change of variables `t ↦ -t` in the temporal
integral, which preserves `[-T,T]`) and transfer through weak limits.
This is simpler than time translation invariance (OS2 temporal) since
the domain `[-T,T]` is already Θ-symmetric at every finite T. -/
axiom cylinderInteracting_os2_reflection
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    @CylinderOS2_TimeReflectionInvariance L hL (cylinderMeasure L P mass hmass)
      (cylinderMeasure_isProbability L P mass hmass)

/-- **OS3 for the interacting measure**: reflection positivity.

  `Σᵢⱼ cᵢ cⱼ Re(Z[fᵢ - Θfⱼ]) ≥ 0`

for all test functions `fᵢ` supported in the positive-time half-space
and real coefficients `cᵢ`.

**Analytical content**: The RP matrix condition, which holds for each
cutoff measure, is preserved through both weak limit procedures.

**Proof sketch** (not yet formalized):
1. Each cutoff measure `μ_{Λ,T}` satisfies RP. This follows from the
   Markov property of the free field + the interaction `V_{Λ,T}` being
   a function of the field on `S¹_L × [-T,T]`. The proof uses the
   Fubini + perfect square argument: on the lattice, the Gaussian
   integral over the t = 0 hyperplane factorizes, and each factor
   contributes a nonneg term. The lattice case is axiomatized in
   `cylinderLattice_rp`.
2. The RP condition is closed under weak limits:
   `cylinderMatrixRP_of_weakLimit` proves that if μ_k → μ weakly and
   each μ_k satisfies RP, then μ satisfies RP. The key observation is
   that each RP matrix entry `Re(Z[g]) = ∫ cos(ω(g)) dμ` is a bounded
   continuous functional of the measure.
3. Applying step 2 twice (UV limit Λ → ∞, then IR limit T → ∞) gives
   RP for the full interacting measure `cylinderMeasure L P mass hmass`.

**Why axiom**: The infrastructure for step 2 is fully proved
(`cylinderMatrixRP_of_weakLimit`). What remains is:
- Connecting `cylinderLattice_rp` (lattice RP) to `μ_{Λ,T}` RP
- Connecting `cylinderMeasure_weakLimit` (axiom'd weak limit) to the
  hypotheses of `cylinderMatrixRP_of_weakLimit`
Both connections require unwinding the axiom'd measures to produce
the sequence-indexed weak convergence that `cylinderMatrixRP_of_weakLimit`
expects. -/
axiom cylinderInteracting_os3
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    @CylinderOS3_ReflectionPositivity L hL (cylinderMeasure L P mass hmass)
      (cylinderMeasure_isProbability L P mass hmass)

/-! ## Main theorem -/

/-- **The P(φ)₂ interacting measure on the cylinder satisfies OS0–OS3.**

This is the main result of the cylinder continuum limit: the measure
  `μ = lim_{T→∞} lim_{Λ→∞} (1/Z_{Λ,T}) exp(-V_{Λ,T}) dμ_free`
satisfies all four Osterwalder-Schrader axioms verifiable in finite
volume (OS4 requires the additional spectral gap / mass gap analysis). -/
theorem cylinderInteracting_satisfies_OS
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    @SatisfiesCylinderOS L hL (cylinderMeasure L P mass hmass)
      (cylinderMeasure_isProbability L P mass hmass) := by
  haveI := cylinderMeasure_isProbability L P mass hmass
  exact {
    os0 := cylinderInteracting_os0 L P mass hmass
    os1 := cylinderInteracting_os1 L P mass hmass
    os2_spatial := cylinderInteracting_os2_spatial L P mass hmass
    os2_time := cylinderInteracting_os2_time L P mass hmass
    os2_reflection := cylinderInteracting_os2_reflection L P mass hmass
    os3 := cylinderInteracting_os3 L P mass hmass
  }

end Pphi2

end
