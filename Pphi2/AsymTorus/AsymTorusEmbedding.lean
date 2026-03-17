/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Asymmetric Torus Embedding: Route B'

Defines the continuum-embedded measures on the asymmetric torus
T_{Lt,Ls} = (ℝ/Lt ℤ) × (ℝ/Ls ℤ), analogous to `TorusEmbedding.lean`
for the symmetric torus.

This is the starting point for Route B': UV limit on T_{Lt,Ls}
followed by IR limit Lt → ∞ to the cylinder S¹_{Ls} × ℝ.

## Main definitions

- `asymTorusEmbedLift` — lifts lattice configs to asymmetric torus configs
- `asymTorusInteractingMeasure` — pushforward of lattice interacting measure
- `asymTorusContinuumGreen` — continuum Green's function on T_{Lt,Ls}

## Design

Uses `AsymTorusTestFunction Lt Ls = NTP(SMC_{Lt}, SMC_{Ls})` from
gaussian-field's `Torus/AsymmetricTorus.lean`. The lattice uses
`AsymLatticeSites Nt Ns = ZMod Nt × ZMod Ns` with spacings
`at = Lt/Nt` (time) and `as = Ls/Ns` (space).

All NTP infrastructure (evalCLM, mapCLM, etc.) works unchanged.
Route B's proofs adapt with minimal type changes.
-/

import Pphi2.InteractingMeasure.LatticeMeasure
import Torus.AsymmetricTorus
import HeatKernel.Bilinear
import SmoothCircle.Eigenvalues

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (Lt Ls : ℝ) [hLt : Fact (0 < Lt)] [hLs : Fact (0 < Ls)]

/-! ## Lattice spacings -/

/-- Time lattice spacing: at = Lt/Nt. -/
def asymTimeSpacing (Nt : ℕ) [NeZero Nt] : ℝ := Lt / Nt

/-- Space lattice spacing: as = Ls/Ns. -/
def asymSpaceSpacing (Ns : ℕ) [NeZero Ns] : ℝ := Ls / Ns

theorem asymTimeSpacing_pos (Nt : ℕ) [NeZero Nt] :
    0 < asymTimeSpacing Lt Nt :=
  div_pos hLt.out (Nat.cast_pos.mpr (NeZero.pos Nt))

theorem asymSpaceSpacing_pos (Ns : ℕ) [NeZero Ns] :
    0 < asymSpaceSpacing Ls Ns :=
  div_pos hLs.out (Nat.cast_pos.mpr (NeZero.pos Ns))

/-! ## Embedding of asymmetric lattice fields

The asymmetric lattice (ZMod Nt) × (ZMod Ns) embeds into the asymmetric
torus configuration space via `asymTorusEmbedCLM` from gaussian-field. -/

/-- The asymmetric torus embedding lift.

Maps a lattice configuration ω on `AsymLatticeField Nt Ns` to a
configuration on `AsymTorusTestFunction Lt Ls` by extracting field
values at each lattice site. -/
def asymTorusEmbedLift (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    Configuration (AsymLatticeField Nt Ns) →
    Configuration (AsymTorusTestFunction Lt Ls) :=
  fun ω => asymTorusEmbedCLM Lt Ls Nt Ns
    (fun x => ω (Pi.single x 1))

/-- The asymmetric torus embedding lift is measurable. -/
theorem asymTorusEmbedLift_measurable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    @Measurable _ _ instMeasurableSpaceConfiguration instMeasurableSpaceConfiguration
      (asymTorusEmbedLift Lt Ls Nt Ns) := by
  apply configuration_measurable_of_eval_measurable
  intro f
  show Measurable (fun (ω : Configuration (AsymLatticeField Nt Ns)) =>
    asymTorusEmbedLift Lt Ls Nt Ns ω f)
  simp only [asymTorusEmbedLift, asymTorusEmbedCLM_apply]
  exact Finset.measurable_sum _ fun x _ =>
    (configuration_eval_measurable (Pi.single x 1)).mul measurable_const

/-! ## Interacting measure on asymmetric torus -/

/-- The asymmetric torus-embedded interacting P(φ)₂ measure.

Pushforward of the lattice interacting measure under the asymmetric
torus embedding. Uses the GEOMETRIC MEAN spacing √(at·as) as the
lattice spacing parameter for the interaction. -/
def asymTorusInteractingMeasure (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    Measure (Configuration (AsymTorusTestFunction Lt Ls)) :=
  sorry -- Need to define the lattice measure on asymmetric sites
  -- The key decision: what spacing parameter to use for the interaction?
  -- Option A: geometric mean √(at·as) — preserves physical volume Lt·Ls
  -- Option B: separate spacings at, as — needs asymmetric interaction
  -- For now: placeholder

/-! ## Continuum Green's function -/

/-- The continuum Green's function on the asymmetric torus T_{Lt,Ls}.

  `G_{Lt,Ls}(f,g) = Σ_{(n₁,n₂)} ĉ_{n₁}(f₁) ĉ_{n₂}(f₂) / ((2πn₁/Lt)² + (2πn₂/Ls)² + m²)`

Uses `greenFunctionBilinear` which works generically for any NTP with
`HasLaplacianEigenvalues` on both factors. Both `SmoothMap_Circle Lt ℝ`
and `SmoothMap_Circle Ls ℝ` have this instance from gaussian-field. -/
noncomputable def asymTorusContinuumGreen (mass : ℝ) (hmass : 0 < mass)
    (f g : AsymTorusTestFunction Lt Ls) : ℝ :=
  greenFunctionBilinear mass hmass f g

end Pphi2

end
