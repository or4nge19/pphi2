/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cylinder → Torus Embedding for Route B' IR Limit

Defines the embedding of cylinder test functions into asymmetric torus
test functions via periodization of the temporal factor, and the induced
pullback on configurations and measures.

`CylinderTestFunction Ls = NTP(SMC_Ls, SchwartzMap ℝ ℝ)` — spatial × temporal
`AsymTorusTestFunction Lt Ls = NTP(SMC_Lt, SMC_Ls)` — temporal × spatial

The embedding periodizes the temporal factor and swaps to match conventions.

## References

- Glimm-Jaffe, *Quantum Physics*, §19 (finite → infinite volume)
-/

import Pphi2.IRLimit.Periodization
import Pphi2.AsymTorus.AsymTorusEmbedding

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory

variable (Lt Ls : ℝ) [hLt : Fact (0 < Lt)] [hLs : Fact (0 < Ls)]

/-! ## Cylinder → Torus Embedding

The NTP infrastructure only supports endomorphism maps (T : E →L[ℝ] E),
not maps between different NTP types. The cylinder-to-torus embedding maps
between different types:

  NTP(SMC_Ls, SchwartzMap ℝ ℝ) → NTP(SMC_Lt, SMC_Ls)

This requires a generalized tensor product functor which we axiomatize here.
The embedding acts on pure tensors as:

  `pure(g_spatial, h_temporal) ↦ pure(periodize Lt h_temporal, g_spatial)`

(periodize the temporal factor, swap the order). -/

/-- The cylinder-to-torus embedding CLM.

Maps `CylinderTestFunction Ls = NTP(SMC_Ls, Schwartz ℝ)` into
`AsymTorusTestFunction Lt Ls = NTP(SMC_Lt, SMC_Ls)` by periodizing the
temporal Schwartz component and swapping factor order.

Axiomatized because `nuclearTensorProduct_mapCLM` only handles endomorphisms.
The proof would construct this as the unique continuous extension of
`pure(g, h) ↦ pure(periodize Lt h, g)` using the DM basis. -/
axiom cylinderToTorusEmbed :
    CylinderTestFunction Ls →L[ℝ] AsymTorusTestFunction Lt Ls

/-- The pullback on configurations: given a torus configuration ω,
produce a cylinder configuration by precomposing with the embedding. -/
def cylinderPullback
    (ω : Configuration (AsymTorusTestFunction Lt Ls)) :
    Configuration (CylinderTestFunction Ls) where
  toFun f := ω (cylinderToTorusEmbed Lt Ls f)
  map_add' f g := by simp [map_add]
  map_smul' r f := by simp [map_smul]
  cont := ω.cont.comp (cylinderToTorusEmbed Lt Ls).cont

/-- The pushforward measure on cylinder configurations. -/
def cylinderPullbackMeasure
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls))) :
    Measure (Configuration (CylinderTestFunction Ls)) :=
  Measure.map (cylinderPullback Lt Ls) μ

/-- Evaluation formula. -/
@[simp] theorem cylinderPullback_eval
    (ω : Configuration (AsymTorusTestFunction Lt Ls))
    (f : CylinderTestFunction Ls) :
    (cylinderPullback Lt Ls ω) f = ω (cylinderToTorusEmbed Lt Ls f) :=
  rfl

/-- The pullback is continuous, hence measurable. -/
theorem cylinderPullback_continuous :
    Continuous (cylinderPullback Lt Ls) := by
  rw [continuous_def]
  intro U hU
  -- The pullback is the composition ω ↦ ω ∘ embed, which is continuous
  -- in the weak-* topology because each evaluation is continuous.
  sorry -- TODO: WeakDual continuity argument

-- Note: Measurability of cylinderPullback follows from continuity
-- once OpensMeasurableSpace is available for the configuration space.
-- This instance is typically derived from the DyninMityaginSpace structure.

end Pphi2
