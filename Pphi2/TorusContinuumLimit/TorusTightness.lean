/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tightness of Torus Gaussian Measures

Shows that the family of continuum-embedded Gaussian measures
`{ν_{GFF,N}}_{N ≥ 1}` is tight on Configuration(TorusTestFunction L).

## Main results

- `torus_second_moment_uniform` — `∫ (ω f)² dν_{GFF,N} ≤ C` uniformly in N
- `configuration_tight_of_uniform_second_moments` — (axiom) Mitoma-Chebyshev criterion
- `torusContinuumMeasures_tight` — (proved) tightness from uniform second moments

## Mathematical background

### Tightness on the torus vs S'(ℝ^d)

The torus approach makes tightness significantly easier than on S'(ℝ^d):
- **Finite volume**: The torus T²_L is compact, so there is no IR contribution
  to the Riemann sum bounds.
- **Mitoma criterion on compact spaces**: For measures on the dual of a nuclear
  Fréchet space over a compact base, tightness of 1D marginals suffices.
- **1D marginals are Gaussian**: Each `(ev_f)_* ν_{GFF,N}` is N(0, σ²_N) with
  σ²_N ≤ C uniformly (from `torusEmbeddedTwoPoint_uniform_bound`).

## References

- Mitoma (1983), "Tightness of probabilities on C([0,1]; S') and D([0,1]; S')"
- Simon, *The P(φ)₂ Euclidean QFT*, §V.1
-/

import Pphi2.TorusContinuumLimit.TorusPropagatorConvergence

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Uniform second moment bounds -/

/-- **Uniform bound on torus Gaussian second moments.**

  `∫ (ω f)² dν_{GFF,N} ≤ C(f, L, m)` uniformly in N ≥ 1

This is a direct consequence of `torusEmbeddedTwoPoint_uniform_bound`. -/
theorem torus_second_moment_uniform (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (TorusTestFunction L),
      (ω f) ^ 2 ∂(torusContinuumMeasure L N mass hmass) ≤ C := by
  obtain ⟨C, hC_pos, hC_bound⟩ := torusEmbeddedTwoPoint_uniform_bound L mass hmass f
  refine ⟨C, hC_pos, fun N _ => ?_⟩
  have : ∫ ω : Configuration (TorusTestFunction L),
      (ω f) ^ 2 ∂(torusContinuumMeasure L N mass hmass) =
    torusEmbeddedTwoPoint L N mass hmass f f := by
    congr 1; ext ω; ring
  rw [this]
  exact hC_bound N

/-! ## Mitoma-Chebyshev tightness criterion -/

/-- **Tightness from uniform second moments on nuclear duals (Mitoma-Chebyshev).**

On the weak dual of a nuclear Fréchet space (encoded by `DyninMityaginSpace`),
a family of probability measures is tight if the second moments of all 1D
marginals are uniformly bounded.

This combines two classical results:

1. **Mitoma's criterion** (1983): For nuclear E, tightness on E' (= Configuration E)
   reduces to tightness of 1D marginals `(ev_f)_* μ_i` for each `f ∈ E`.

2. **Chebyshev's inequality**: Uniform variance bounds `sup_i E_i[(ω f)²] ≤ C(f)`
   give `P_i(|ω(f)| > R) ≤ C(f)/R²`, hence 1D tightness.

The nuclearity of E (encoded by `DyninMityaginSpace`) is essential: the
counterexample E = ℓ² (non-nuclear, but E' = ℓ² is Polish) shows that
uniform second moment bounds alone do NOT imply tightness without nuclearity.

**References**: Mitoma (1983), Simon §V.1, Gel'fand-Vilenkin Vol. 4 Ch. IV,
Bogachev *Gaussian Measures* Ch. 3. -/
axiom configuration_tight_of_uniform_second_moments
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [DyninMityaginSpace E]
    [PolishSpace (Configuration E)] [BorelSpace (Configuration E)]
    {ι : Type*}
    (μ : ι → Measure (Configuration E))
    (hprob : ∀ i, IsProbabilityMeasure (μ i))
    (h_moments : ∀ f : E, ∃ C : ℝ, ∀ i,
      ∫ ω : Configuration E, (ω f) ^ 2 ∂(μ i) ≤ C) :
    ∀ ε : ℝ, 0 < ε →
    ∃ K : Set (Configuration E),
      IsCompact K ∧ ∀ i, 1 - ε ≤ (μ i K).toReal

/-! ## Tightness of torus Gaussian measures -/

/-- **Tightness of the torus-embedded Gaussian measures.**

The family `{ν_{GFF,N}}_{N ≥ 1}` is tight on Configuration(TorusTestFunction L).

**Proof**: Apply `configuration_tight_of_uniform_second_moments` with
`ι = {N : ℕ // 0 < N}` and the uniform second moment bounds from
`torus_second_moment_uniform`. The nuclearity hypothesis is satisfied by
`DyninMityaginSpace (TorusTestFunction L)` (from `NuclearTensorProduct`),
and the Polish/Borel instances by `configuration_torus_polish`/`borelSpace`.

Reference: Mitoma (1983), Simon §V.1. -/
theorem torusContinuumMeasures_tight
    (mass : ℝ) (hmass : 0 < mass) :
    ∀ ε : ℝ, 0 < ε →
    ∃ (K : Set (Configuration (TorusTestFunction L))),
      IsCompact K ∧
      ∀ (N : ℕ) [NeZero N],
      1 - ε ≤ (torusContinuumMeasure L N mass hmass K).toReal := by
  haveI := configuration_torus_polish L
  haveI := configuration_torus_borelSpace L
  intro ε hε
  -- Apply Mitoma-Chebyshev with ι = {N : ℕ // 0 < N}
  obtain ⟨K, hK_compact, hK_bound⟩ := configuration_tight_of_uniform_second_moments
    (ι := {N : ℕ // 0 < N})
    (fun ⟨N, hN⟩ => haveI : NeZero N := ⟨by omega⟩;
      torusContinuumMeasure L N mass hmass)
    (fun ⟨N, hN⟩ => by haveI : NeZero N := ⟨by omega⟩; exact inferInstance)
    (fun f => by
      obtain ⟨C, _, hC_bound⟩ := torus_second_moment_uniform L mass hmass f
      exact ⟨C, fun ⟨N, hN⟩ => by haveI : NeZero N := ⟨by omega⟩; exact hC_bound N⟩)
    ε hε
  exact ⟨K, hK_compact, fun N inst => hK_bound ⟨N, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩

end Pphi2

end
