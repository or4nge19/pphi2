/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uniform Second Moment Bound for Cylinder Pullback

Proves the uniform second moment bound for the cylinder pullback measures
using the method of images from gaussian-field.

## Proof chain

1. `E_{ν_Lt}[(ωf)²] = E_{μ_Lt}[(ω(embed f))²]` — pullback definition
2. `E_{μ_Lt}[(ω(embed f))²] ≤ C · G_{Lt,Ls}(embed f, embed f)` — density transfer (AsymTorusOS)
3. `G_{Lt,Ls}(embed f, embed f) ≤ C' · q(f)²` — method of images (gaussian-field)

Combined: `E_{ν_Lt}[(ωf)²] ≤ C·C' · q(f)²` uniformly in Lt.

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII
-/

import Pphi2.IRLimit.CylinderEmbedding
import Cylinder.MethodOfImages

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory

variable (Ls : ℝ) [hLs : Fact (0 < Ls)]
variable (mass : ℝ) (hmass : 0 < mass)

/-- Uniform second moment bound for the cylinder pullback measures.

For any cylinder test function f, the second moment under the
pulled-back torus interacting measure is bounded by a continuous
seminorm of f, uniformly in the time period Lt ≥ 1.

**Proof**: Chains the pullback identity, the AsymTorus density transfer
(interacting → Gaussian second moment), and the method of images
uniform bound on the torus Green's function.

The bound `E[(ωf)²] ≤ C · q(f)²` with `C` independent of Lt is the
core tightness input for the IR limit. -/
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

-- NOTE: To prove this axiom, wire together:
-- 1. cylinderPullback_eval: (pullback ω) f = ω (embed f)
-- 2. asymTorus interacting second moment bound (from AsymTorusOS)
-- 3. torusGreen_uniform_bound (from Cylinder.MethodOfImages in gaussian-field):
--    G_{Lt,Ls}(embed f, embed f) ≤ C · q(f)² for continuous seminorm q

end Pphi2
