/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Periodization: Schwartz → Smooth Circle

Defines the periodization map `𝓢(ℝ) →L[ℝ] C∞(S¹_L)` that wraps a
Schwartz function onto a circle of period L by summing translates:

  `(periodize L h)(t) = Σ_{k ∈ ℤ} h(t + kL)`

This is the foundational ingredient for the Route B' IR limit: it defines
how cylinder test functions embed into asymmetric torus test functions.

## References

- Stein-Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Ch. VII
-/

import Cylinder.Basic

noncomputable section

namespace Pphi2

open GaussianField

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Periodization CLM

The periodization map `periodizeCLM L : SchwartzMap ℝ ℝ →L[ℝ] SmoothMap_Circle L ℝ`
sends a Schwartz function `h` to the L-periodic function
`t ↦ Σ_{k ∈ ℤ} h(t + kL)`.

**Well-definedness**: Rapid decay of Schwartz functions guarantees
absolute convergence of the sum in all Sobolev norms.

**Continuity**: For any Sobolev seminorm `‖·‖_{H^s}` on `C∞(S¹_L)`,
there exists a Schwartz seminorm `p_{N,s}` with
`‖periodize L h‖_{H^s} ≤ C · p_{N,s}(h)` for all `h`. -/

axiom periodizeCLM :
    SchwartzMap ℝ ℝ →L[ℝ] SmoothMap_Circle L ℝ

/-- For `h` supported in `[-T, T]` and `L > 2T`, the periodic sum has only
the `k = 0` term on `[0, L/2]`, so `periodize L h` agrees with `h` there. -/
axiom periodizeCLM_eq_on_large_period (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (hL : L > 2 * T) :
    ∀ t ∈ Set.Icc 0 (L / 2), (periodizeCLM L h).toFun t = h t

end Pphi2
