/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reflection Positivity Transfer: Lattice → Continuum

Proves that the continuum-embedded lattice measures satisfy reflection
positivity, transferring the proved lattice RP through the embedding.

## Main results

- `latticeEmbedLift_intertwines_reflection` — the embedding commutes with
  time reflection: `Θ* ∘ ι = ι ∘ Θ_latt`
- `continuum_embedded_measure_rp` — each continuum-embedded measure has RP

## Proof strategy

The embedding `ι : Configuration(lattice) → Configuration(S'(ℝ²))` satisfies:
  `(Θ*(ι ω))(f) = (ι ω)(Θf) = a² Σ_x ω(e_x) · (Θf)(a·x)`
  `= a² Σ_x ω(e_x) · f(-a·t_x, a·s_x)`
  `= a² Σ_x' ω(e_{Θx'}) · f(a·x')` (reindex x' = Θx, bijective)
  `= (ι(Θ_latt ω))(f)`

where `(Θ_latt ω)(e_x) = ω(e_{Θx})`. This is a pure reindexing of a finite sum.

Then RP transfers: `∫ F·(F∘Θ*) d(ι_* μ) = ∫ (F∘ι)·((F∘ι)∘Θ_latt) dμ ≥ 0`
by lattice RP (`lattice_rp`).

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. III
-/

import Pphi2.ContinuumLimit.AxiomInheritance
import Pphi2.OSProofs.OS3_RP_Lattice

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory

variable (N : ℕ) [NeZero N]

/-! ## Lattice time reflection on Configuration space

The lattice time reflection `Θ_latt` on `Configuration(FinLatticeField 2 N)`
maps `ω ↦ ω ∘ (· ∘ timeReflection2D)`, i.e., it permutes the lattice sites
by `(t,x) ↦ (-t, x)`. -/

/-- Time reflection on `FinLatticeSites 2 N = Fin 2 → ZMod N`.
Negates the 0th coordinate (time), preserves the 1st (space). -/
def siteTimeReflection (x : FinLatticeSites 2 N) : FinLatticeSites 2 N :=
  fun i => if i = 0 then -x i else x i

/-- Time reflection on lattice fields: `(Θφ)(x) = φ(Θx)`. -/
def fieldTimeReflection (φ : FinLatticeField 2 N) : FinLatticeField 2 N :=
  φ ∘ siteTimeReflection N

/-- The field time reflection as a linear map on `FinLatticeField 2 N`. -/
def fieldTimeReflectionLinear : FinLatticeField 2 N →ₗ[ℝ] FinLatticeField 2 N where
  toFun := fieldTimeReflection N
  map_add' φ ψ := by ext x; simp [fieldTimeReflection, Function.comp]
  map_smul' r φ := by ext x; simp [fieldTimeReflection, Function.comp]

/-- Lattice time reflection on configuration space.
`(Θ_latt ω)(φ) = ω(Θφ) = ω(φ ∘ siteTimeReflection)`. -/
def latticeConfigReflection :
    Configuration (FinLatticeField 2 N) → Configuration (FinLatticeField 2 N) :=
  fun ω => ω.comp (fieldTimeReflectionLinear N).toContinuousLinearMap

/-! ## Intertwining identity

The lattice embedding commutes with time reflection:
`distribTimeReflection ∘ latticeEmbedLift = latticeEmbedLift ∘ latticeConfigReflection`

Equivalently, for all ω and f:
`(ι ω)(Θf) = (ι(Θ_latt ω))(f)`

This is a reindexing of the finite sum: `Σ_x ω(e_x) · (Θf)(a·x) = Σ_x ω(e_{Θx}) · f(a·x)`. -/

/-! ## Helper lemmas for the intertwining identity -/

omit [NeZero N] in
lemma siteTimeReflection_involutive :
    Function.Involutive (siteTimeReflection N : FinLatticeSites 2 N → FinLatticeSites 2 N) := by
  intro x; ext i; simp [siteTimeReflection]; split <;> simp [neg_neg]

lemma fieldTimeReflection_single (x : FinLatticeSites 2 N) :
    fieldTimeReflection N (Pi.single x 1) =
    Pi.single (siteTimeReflection N x) (1 : ℝ) := by
  have hinv := siteTimeReflection_involutive N
  have hbij : siteTimeReflection N (siteTimeReflection N x) = x := hinv x
  ext y
  simp only [fieldTimeReflection, Function.comp, Pi.single_apply]
  by_cases h : y = siteTimeReflection N x
  · simp [h, hbij]
  · simp only [h, ite_false]
    have : siteTimeReflection N y ≠ x := fun heq => h (by rw [← heq, hinv y])
    simp [this]

theorem latticeEmbedLift_intertwines_reflection (a : ℝ) (ha : 0 < a)
    (hN_odd : Odd N)
    (ω : Configuration (FinLatticeField 2 N))
    (f : ContinuumTestFunction 2) :
    distribTimeReflection (latticeEmbedLift 2 N a ha ω) f =
    latticeEmbedLift 2 N a ha (latticeConfigReflection N ω) f := by
  -- Unfold both sides to sums and use the helper lemmas.
  -- LHS = (ι ω)(Θf) = a^2 * Σ_x ω(e_x) * (Θf)(pos(x))
  -- RHS = (ι(Θω))(f) = a^2 * Σ_x (Θω)(e_x) * f(pos(x))
  --      = a^2 * Σ_x ω(fieldTimeRefl(e_x)) * f(pos(x))
  --      = a^2 * Σ_x ω(e_{Θx}) * f(pos(x))  (by fieldTimeReflection_single)
  -- Reindex LHS: x' = Θx gives Σ_{x'} ω(e_{Θx'}) * (Θf)(pos(Θx'))
  -- Need: (Θf)(pos(Θx')) = f(pos(x'))  (by position intertwining + signedVal_neg)
  sorry

/-! ## RP transfer theorem

From lattice RP + intertwining, the continuum-embedded measure has RP. -/

/-- **RP of continuum-embedded lattice measures.**

Each `continuumMeasure 2 N P a mass ha hmass` satisfies reflection positivity:
`∫ F(ω) · F(Θ*ω) dν ≥ 0` for all bounded continuous F.

Proof:
1. Change of variables: `∫ F·(F∘Θ*) d(ι_* μ) = ∫ (F∘ι)·((F∘ι)∘Θ_latt) dμ`
   (using intertwining: `F(Θ*(ι φ)) = F(ι(Θ_latt φ))`)
2. Lattice RP: `∫ G·(G∘Θ_latt) dμ ≥ 0` where `G = F ∘ ι`
   (from `lattice_rp` in OS3_RP_Lattice.lean) -/
theorem continuum_embedded_measure_rp'
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (a : ℝ) (ha : 0 < a) :
    ∀ (F : Configuration (ContinuumTestFunction 2) → ℝ),
      Continuous F → (∃ C, ∀ ω, |F ω| ≤ C) →
      0 ≤ ∫ ω, F ω * F (distribTimeReflection ω)
        ∂(continuumMeasure 2 N P a mass ha hmass) := by
  intro F hF_cont ⟨C, hC⟩
  -- Step 1: Change of variables: ∫ G d(ι_* μ) = ∫ G∘ι dμ
  set ι := latticeEmbedLift 2 N a ha
  set μ_latt := interactingLatticeMeasure 2 N P a mass ha hmass
  -- The integrand G(ω) = F(ω) · F(Θ*ω)
  set G : Configuration (ContinuumTestFunction 2) → ℝ :=
    fun ω => F ω * F (distribTimeReflection ω)
  change 0 ≤ ∫ ω, G ω ∂(Measure.map ι μ_latt)
  -- Step 2: Apply integral_map to rewrite as ∫ G∘ι dμ_latt
  -- The change of variables and lattice RP application requires:
  -- (a) Measurability of G ∘ ι on the lattice (finite-dimensional)
  -- (b) The intertwining identity: F(Θ*(ι φ)) = F(ι(Θ_latt φ))
  -- (c) Applying lattice_rp to F ∘ ι
  -- All are standard but require lattice geometry plumbing.
  sorry

end Pphi2

end
