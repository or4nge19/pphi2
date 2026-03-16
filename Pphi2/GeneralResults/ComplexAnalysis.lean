/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# General Results: Complex Analysis

Analyticity of parameter-dependent integrals (holomorphic dependence on
parameters). This is the several-complex-variables version of Morera's
theorem / differentiation under the integral sign.

## Main results

- `analyticOnNhd_integral` — (axiom) if `z ↦ F(z, ω)` is entire for each ω
  and dominated by an integrable bound locally uniform in z, then
  `z ↦ ∫ F(z, ω) dμ` is entire.

## References

- Reed-Simon I, Theorem VI.1 (analytic families of integrands)
- Fernique (1975), §III.4
- Stein-Shakarchi, *Complex Analysis*, Ch. 2 §5 (Morera + Fubini)

## Proof strategy (for future formalization)

For one complex variable: `z ↦ ∫ F(z, ω) dμ` is complex-differentiable
by `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (Mathlib), hence
analytic by `DifferentiableAt.analyticAt` (holomorphic ⟹ analytic).
For several variables: apply the one-variable result in each coordinate
(Hartogs' theorem: separately analytic ⟹ jointly analytic, available
in Mathlib as `AnalyticAt.of_differentiableAt_of_differentiableAt`
or via Osgood's lemma).
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Analytic.Basic

open MeasureTheory Complex Filter

/-- **Analyticity of parameter-dependent integrals (Morera).**

If for each fixed `ω`, the map `z ↦ F(z, ω)` is entire analytic on `ℂⁿ`,
and the family is dominated by an integrable bound that is locally uniform
in `z`, then the integral `z ↦ ∫ F(z, ω) dμ` is entire analytic.

This is a standard result in several complex variables. The proof combines:
1. Differentiation under the integral sign (`hasDerivAt_integral_of_dominated`)
   to get holomorphicity in each variable separately.
2. Hartogs' theorem (separately holomorphic ⟹ jointly holomorphic/analytic).

Axiomatized pending formalization of the several-variables argument.
The one-variable case is provable from existing Mathlib infrastructure. -/
axiom analyticOnNhd_integral {n : ℕ} {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : (Fin n → ℂ) → α → ℂ}
    (hF_an : ∀ ω, AnalyticOnNhd ℂ (F · ω) Set.univ)
    (hF_meas : ∀ z, AEStronglyMeasurable (F z) μ)
    (hF_dom : ∀ K : Set (Fin n → ℂ), IsCompact K →
      ∃ bound : α → ℝ, Integrable bound μ ∧
        ∀ z ∈ K, ∀ᵐ ω ∂μ, ‖F z ω‖ ≤ bound ω) :
    AnalyticOnNhd ℂ (fun z => ∫ ω, F z ω ∂μ) Set.univ
