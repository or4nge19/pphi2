/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Green's Function Comparison: Torus vs Cylinder

Axiomatizes the key analytical bound for the Route B' IR limit:
the torus second moment of a periodized test function is uniformly
bounded in Lt by the cylinder Green's function.

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII
-/

import Pphi2.IRLimit.CylinderEmbedding

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory

variable (Ls : ℝ) [hLs : Fact (0 < Ls)]
variable (mass : ℝ) (hmass : 0 < mass)

/-! ## Uniform second moment bound

The key analytical fact: for any cylinder test function f, the
second moment `E[(ωf)²]` under the pulled-back torus interacting
measure is uniformly bounded in Lt.

This combines:
1. Density transfer: `E_P[(ωf)²] ≤ C · E_GFF[(ωf)²]` (from Nelson)
2. Gaussian second moment = Green's function: `E_GFF[(ωf)²] = G_{Lt,Ls}(embed f, embed f)`
3. Green's function comparison: `G_{Lt,Ls}(embed f) ≤ G_{Ls}(f)` (Riemann sum ≤ integral)

The result: `E_P[(ωf)²] ≤ C_total · q(f)` for a continuous seminorm `q`
on `CylinderTestFunction Ls`, uniformly in Lt. -/

/-- Uniform second moment bound for the cylinder pullback measures.

For any cylinder test function f, the second moment under the
pulled-back torus interacting measure is bounded by a continuous
seminorm of f, uniformly in the time period Lt.

This is the core tightness input for the IR limit Lt → ∞. -/
axiom cylinderIR_uniform_second_moment
    (P : InteractionPolynomial) :
    ∃ (C : ℝ) (q : CylinderTestFunction Ls → ℝ),
    0 < C ∧ Continuous q ∧
    ∀ (Lt : ℝ) [Fact (0 < Lt)]
      (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
      [IsProbabilityMeasure μ]
      (f : CylinderTestFunction Ls),
    ∫ ω : Configuration (CylinderTestFunction Ls),
      (ω f) ^ 2 ∂(cylinderPullbackMeasure Lt Ls μ) ≤
    C * q f

end Pphi2
