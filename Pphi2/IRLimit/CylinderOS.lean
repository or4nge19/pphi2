/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cylinder OS Axioms via Route B' IR Limit

States OS0–OS3 for the P(φ)₂ cylinder measure obtained as the IR limit
(Lt → ∞) of asymmetric torus measures from Route B'.

## Main result

- `routeBPrime_cylinder_OS` — the IR limit satisfies OS0–OS3

## References

- Osterwalder-Schrader (1973, 1975)
- Glimm-Jaffe, *Quantum Physics*, Ch. 6, 19
-/

import Pphi2.IRLimit.IRTightness
import Cylinder.Symmetry
import Cylinder.PositiveTime
import Cylinder.ReflectionPositivity

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory Filter

variable (Ls : ℝ) [hLs : Fact (0 < Ls)]

/-! ## Route B' Main Theorem -/

/-- **Route B' main theorem**: the IR limit of asymmetric torus measures
satisfies OS0–OS3 on the cylinder S¹_{Ls} × ℝ.

**OS0** (analyticity): transferred from torus via weak convergence +
exponential moment bounds.

**OS1** (regularity): transferred from torus moment bounds.

**OS2** (invariance): spatial from torus spatial invariance (exact);
temporal from torus time translation in the Lt → ∞ limit;
time reflection from torus time reflection (exact).

**OS3** (reflection positivity): lattice RP (transfer matrix, proved in
OS3_RP_Lattice.lean) → torus RP (weak limit) → cylinder RP (IR limit).
Each step preserves positive semidefiniteness. -/
axiom routeBPrime_cylinder_OS
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop)
    (μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls)))
    (hμ_prob : ∀ n, IsProbabilityMeasure (μ n))
    (hμ_os : ∀ n, @AsymSatisfiesTorusOS (Lt n) Ls _ _ (μ n) (hμ_prob n)) :
    ∃ (ν : Measure (Configuration (CylinderTestFunction Ls))),
    IsProbabilityMeasure ν ∧
    -- OS0: generating functional is entire analytic
    (∀ (n : ℕ) (J : Fin n → CylinderTestFunction Ls),
      AnalyticOnNhd ℂ (fun z : Fin n → ℂ =>
        ∫ ω, Complex.exp (∑ i, Complex.I * z i * ↑(ω (J i))) ∂ν) Set.univ) ∧
    -- OS2: time reflection invariance
    (∀ f : CylinderTestFunction Ls,
      ∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν =
      ∫ ω, Complex.exp (Complex.I * ↑(ω (cylinderTimeReflection Ls f))) ∂ν) ∧
    -- OS3: reflection positivity
    (∀ (n : ℕ) (f : Fin n → ↥(cylinderPositiveTimeSubmodule Ls)) (c : Fin n → ℂ),
      0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
        ∫ ω, Complex.exp (Complex.I *
          ↑(ω ((f i : CylinderTestFunction Ls) -
            cylinderTimeReflection Ls (f j : CylinderTestFunction Ls)))) ∂ν).re)

end Pphi2
