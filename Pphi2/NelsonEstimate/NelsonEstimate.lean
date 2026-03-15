/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nelson's Exponential Estimate

Combines covariance splitting, the smooth classical lower bound, and
hypercontractivity on the rough error to prove Nelson's exponential estimate:

  `∫ exp(-2V) dμ_GFF ≤ K`  (uniform in lattice size N)

## Main results

- `nelson_exponential_estimate_lattice` — the full estimate on the lattice

## Proof outline

1. Split covariance: C = C_S(T) + C_R(T) (CovarianceSplit.lean)
2. Wick binomial: V(φ) = V_S(φ_S) + E_R(φ_S, φ_R) (WickBinomial.lean)
3. Classical lower bound: V_S ≥ -C₁·(1+|log T|)² (SmoothLowerBound.lean)
4. Hypercontractivity: P(|E_R| > λ) ≤ exp(-c·λ^{1/2}/T^{1/8}) (RoughErrorBound.lean)
5. Dynamic cutoff: choose T = exp(-c₃·√M), integrate (this file)

## References

- Simon, *P(φ)₂ Euclidean QFT*, Chapter V, Theorem V.14
- Glimm-Jaffe, *Quantum Physics*, Section 8.6
-/

import Pphi2.NelsonEstimate.SmoothLowerBound
import Pphi2.NelsonEstimate.RoughErrorBound
import Pphi2.TorusContinuumLimit.TorusInteractingLimit

noncomputable section

open GaussianField MeasureTheory Real
open scoped BigOperators

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Nelson's dynamic cutoff argument

Given:
- V(φ) = V_S(φ_S) + E_R(φ_S, φ_R)
- V_S(φ_S) ≥ -C₁·(log T)² (smooth lower bound)
- P(|E_R| > λ) ≤ exp(-c₂·λ^{1/2}/T^{1/8}) (rough tail bound)

If V(φ) ≤ -M, then E_R ≤ -M - V_S ≤ -M + C₁(log T)².

Choose T = T(M) such that C₁(log T)² = M/2:
  T = exp(-√(M/(2C₁)))

Then |E_R| ≥ M/2, so:
  P(V ≤ -M) ≤ P(|E_R| ≥ M/2) ≤ exp(-c₂·(M/2)^{1/2} · exp(c₃·M^{1/2}))

This is DOUBLE EXPONENTIAL decay, so:
  ∫₀^∞ exp(2M) · P(V ≤ -M) dM < ∞ -/

/-- **Nelson's exponential estimate on the lattice** (the main theorem).

For the P(φ)₂ lattice theory on the 2D torus of size L with lattice
spacing a = L/N and mass m > 0:

  `∫ exp(-2V) dμ_GFF ≤ K`

where K depends on P (the interaction polynomial), L, and m,
but NOT on N (the lattice size).

Proof: Dynamic cutoff combining Steps 1-4. -/
theorem nelson_exponential_estimate_lattice
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (K : ℝ), 0 < K ∧
    ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (FinLatticeField 2 N),
        (exp (-interactionFunctional 2 N P (circleSpacing L N) mass ω)) ^ 2
        ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass
          (circleSpacing_pos L N) hmass) ≤ K := by
  -- The proof combines all 4 steps:
  -- Step 1: For each energy level M, choose Schwinger parameter T(M) = exp(-c·√M)
  -- Step 2: Split V = V_S + E_R using covariance splitting at T(M)
  -- Step 3: V_S ≥ -C₁·(1+|log T|)² ≥ -C₁·(c·√M + 1)²
  --         Choose c so that C₁·(c·√M + 1)² = M/2
  -- Step 4: If V ≤ -M, then |E_R| ≥ M/2
  --         P(|E_R| ≥ M/2) ≤ exp(-c₂·(M/2)^{1/2} · T^{-1/8})
  --         = exp(-c₂·(M/2)^{1/2} · exp(c/8·√M))
  --         This is double-exponential decay
  -- Step 5: ∫ exp(2M) · P(V ≤ -M) dM < ∞ by comparison
  sorry

end Pphi2

end
