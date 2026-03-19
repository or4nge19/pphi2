# Cylinder IR Limit: Implementation Plan

## Goal

Take the family of asymmetric torus measures `{μ_{P,Lt,Ls}}` (from the
proved UV limit in `AsymTorus/`) and construct their weak limit as
`Lt → ∞`, landing on the cylinder `S¹_{Ls} × ℝ`. Prove OS0–OS3.

## Current State

**Implemented** (`Pphi2/IRLimit/`):

| File | Status | Axioms |
|------|--------|--------|
| `Periodization.lean` | Re-exports from gaussian-field | 0 (3 in g-f) |
| `CylinderEmbedding.lean` | `cylinderToTorusEmbed` is a **def** | 0 + 1 sorry |
| `GreenFunctionComparison.lean` | Axiom: uniform 2nd moment | 1 |
| `IRTightness.lean` | Axiom: Prokhorov extraction | 1 |
| `CylinderOS.lean` | Axiom: main OS0+OS2+OS3 theorem | 1 |

**Total: 3 axioms in pphi2, 5 axioms in gaussian-field.**

## Architecture

```
CylinderTestFunction Ls = NTP(SMC_Ls, Schwartz ℝ)
        │
        │  cylinderToTorusEmbed Lt Ls  (DEF, not axiom)
        │  = swap ∘ (id ⊗ periodize Lt)
        ▼
AsymTorusTestFunction Lt Ls = NTP(SMC_Lt, SMC_Ls)
        │
        │  cylinderPullback Lt Ls  (DEF)
        │  ω_cyl(f) = ω_torus(embed f)
        ▼
Configuration(CylinderTestFunction Ls)
        │
        │  cylinderPullbackMeasure Lt Ls μ  (DEF)
        │  = pushforward of μ under pullback
        ▼
Family of cylinder measures {ν_Lt} indexed by Lt
        │
        │  Prokhorov (axiom: cylinderIRLimit_exists)
        │  Uniform 2nd moment → Mitoma → tightness
        ▼
ν = weak limit  (the P(φ)₂ cylinder measure)
        │
        │  OS axiom transfer (axiom: routeBPrime_cylinder_OS)
        ▼
ν satisfies OS0 + OS2 + OS3
```

## What needs proving

### Axiom 1: `cylinderIR_uniform_second_moment`

**Statement**: For any cylinder test function `f`, the second moment
`E_{ν_Lt}[(ωf)²]` is bounded uniformly in `Lt`.

**Proof route**:
1. `E_{ν_Lt}[(ωf)²] = E_{μ_Lt}[(ω(embed f))²]` (pullback)
2. `E_{μ_Lt}[(ω(embed f))²] ≤ C · G_{Lt,Ls}(embed f, embed f)` (density transfer, proved in AsymTorusOS)
3. `G_{Lt,Ls}(embed f, embed f) ≤ G_{Ls}(f, f)` (Green's function comparison: Riemann sum ≤ integral)
4. `G_{Ls}(f, f) ≤ q(f)` for continuous seminorm `q` (cylinder Green's function continuity)

**Key new ingredient**: Step 3, the Green's function comparison. In Fourier:
the torus sums over discrete temporal momenta `2πn/Lt`, the cylinder
integrates over continuous `p`. The sum is a Riemann approximation to the
integral, bounded by the integral since all terms are positive.

**Estimated effort**: ~200 lines (Fourier comparison + wiring).

### Axiom 2: `cylinderIRLimit_exists`

**Statement**: The family `{ν_Lt}` has a weakly convergent subsequence.

**Proof route**: Identical to `asymTorusInteractingLimit_exists`:
1. Uniform second moments (from axiom 1)
2. `configuration_tight_of_uniform_second_moments` (gaussian-field)
3. Prokhorov's theorem on the Polish configuration space

**Estimated effort**: ~150 lines (follows template exactly).

### Axiom 3: `routeBPrime_cylinder_OS`

**Statement**: The limit measure satisfies OS0, OS2, OS3.

**Proof route**:

**OS0** (analyticity): Each torus generating functional `Z_{Lt}[z]` is
entire analytic (from `asymTorusInteracting_os0`). The limit `Z[z]` is
analytic because: weak convergence of characteristic functionals +
uniform exponential moment bounds → analyticity of the limit.

**OS2** (invariance): Spatial translation is exact at each torus (the
spatial circle `S¹_{Ls}` is common). Time translation: for any shift `τ`,
the shifted cylinder test function embeds into `T_{Lt}` for `Lt` large
enough, and the torus measures are approximately time-translation invariant
(lattice → continuous in the UV limit). Time reflection is exact at each
torus.

**OS3** (reflection positivity): This is the main payoff.
1. Lattice RP from transfer matrix positivity (`OS3_RP_Lattice.lean`)
2. Torus RP: weak limit of lattice RP (positive semidefiniteness is closed)
3. Cylinder RP: IR limit of torus RP (same closure argument)

**Estimated effort**: ~300 lines (OS0: 100, OS2: 100, OS3: 100).

## gaussian-field additions needed

Already added (cylinder branch, pushed):

| File | Content | Axioms |
|------|---------|--------|
| `Nuclear/GeneralMapCLM.lean` | NTP functor for different types | 2 |
| `SchwartzNuclear/Periodization.lean` | `periodizeCLM` | 3 |

Still needed:

| File | Content | Est. |
|------|---------|------|
| `Cylinder/GreenFunctionComparison.lean` | `G_{Lt} ≤ G_cyl` | ~200 lines |

## Dependencies

```
gaussian-field (cylinder branch):
  Nuclear/GeneralMapCLM.lean ← NEW
  SchwartzNuclear/Periodization.lean ← NEW
  Cylinder/GreenFunctionComparison.lean ← TODO

pphi2:
  AsymTorus/ (0 axioms, 0 sorry) ← DONE
  IRLimit/Periodization.lean (re-export) ← DONE
  IRLimit/CylinderEmbedding.lean (def) ← DONE
  IRLimit/GreenFunctionComparison.lean (1 axiom) ← TODO
  IRLimit/IRTightness.lean (1 axiom) ← TODO
  IRLimit/CylinderOS.lean (1 axiom) ← TODO
```

## Order of work

1. **Green's function comparison** in gaussian-field (~200 lines)
   → Unblocks `cylinderIR_uniform_second_moment`
2. **Prove `cylinderIR_uniform_second_moment`** in pphi2 (~200 lines)
   → Unblocks tightness
3. **Prove `cylinderIRLimit_exists`** in pphi2 (~150 lines)
   → Follows template from AsymTorusInteractingLimit
4. **Prove `routeBPrime_cylinder_OS`** in pphi2 (~300 lines)
   → OS0+OS2 transfer + OS3 from transfer matrix

Total remaining: ~850 lines across gaussian-field + pphi2.
