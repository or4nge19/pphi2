# Torus Continuum Limit Completion Plan

## Overview

The torus continuum limit isolates the UV limit (a = L/N → 0) from IR issues
by fixing the physical volume L. The pipeline handles both Gaussian and
interacting (P(φ)₂) measures.

**Current state (2026-03-02):** 6 files in `TorusContinuumLimit/`, 7 torus
axioms, 5 sorries (2 in TorusGaussianLimit, 2 in TorusPropagatorConvergence,
1 in TorusEmbedding).

## Architecture

```
gaussian-field (upstream)                    pphi2 (downstream)
─────────────────────────                    ──────────────────
NuclearTensorProduct.evalCLM ──────────────→ TorusEmbedding.lean
HeatKernel/Bilinear.lean    ──────────────→   torusContinuumGreen (def)
  HasLaplacianEigenvalues                      torusContinuumMeasure
  heatKernelBilinear                           torusEmbeddedTwoPoint
  greenFunctionBilinear
                                             TorusPropagatorConvergence.lean
                                               torus_propagator_convergence (axiom)
                                               torusEmbeddedTwoPoint_uniform_bound (sorry)
                                               torusContinuumGreen_pos (sorry)

                                             TorusTightness.lean
                                               torusContinuumMeasures_tight (axiom)

                                             TorusConvergence.lean
                                               torusGaussianLimit_exists (PROVED)

                                             TorusGaussianLimit.lean
                                               torusGaussianLimit_isGaussian (axiom)
                                               torusGaussianMeasure_isGaussian (axiom)
                                               torusLimit_covariance_eq (axiom)
                                               gaussian_measure_unique_of_covariance (axiom)
                                               torusGaussianLimit_converges (PROVED, 2 sorries)

                                             TorusInteractingLimit.lean
                                               torus_interacting_tightness (axiom)
                                               torusInteractingLimit_exists (PROVED)
```

## Tier 1: Definitions and Infrastructure

These are prerequisite definitions in gaussian-field that pphi2 needs.

### 1a. `evalCLM` in gaussian-field

Already on the torus branch as a sorry. Provides the evaluation CLM:
```
evalCLM φ₁ φ₂ (pure e₁ e₂) = φ₁(e₁) · φ₂(e₂)
```
Extends linearly to the full tensor product. Used by `torusEmbedCLM`.

### 1b. `HeatKernel/Bilinear.lean` in gaussian-field

New file implementing heat kernel and Green's function on any
`DyninMityaginSpace` with `HasLaplacianEigenvalues`.

**Key definitions:**
- `HasLaplacianEigenvalues E (μ : ℕ → ℝ)` — eigenvalues of -Δ (mass-free, ≥ 0)
- `heatKernelBilinear E t f g = Σ_m e^{-tμ_m} coeff_m(f) coeff_m(g)`
- `greenFunctionBilinear E mass f g = ∫₀^∞ e^{-tm²} K_t(f,g) dt`
  = `Σ_m coeff_m(f) coeff_m(g) / (μ_m + mass²)`

**Key properties:**
- `heatKernelBilinear_tensor` — K_{t,E₁⊗E₂} = K_{t,E₁} ⊗ K_{t,E₂}
- `heatKernelBilinear_tendsto_l2` — K_t(f,g) → ⟨f,g⟩_{L²} as t → 0⁺
- `greenFunctionBilinear_pos` — G(f,f) > 0 for f ≠ 0

Once this is implemented, `torusContinuumGreen` in pphi2 becomes:
```lean
def torusContinuumGreen ... := greenFunctionBilinear (TorusTestFunction L) mass hmass f g
```

### 1c. `torusGaussianMeasure_isGaussian` (axiom → provable?)

Currently an axiom stating the lattice GFF pushforward is Gaussian. With
proper infrastructure (Gaussian pushforward under linear maps), this could
become a theorem. Low priority for now.

**Dependency:** None (standalone axiom about lattice GFF).

## Tier 2: Provable Sorries

These are sorries where the proof strategy is clear and no new axioms are
needed.

### 2a. `torusContinuumGreen` definition (TorusEmbedding.lean)

Currently `sorry`. Replace with `greenFunctionBilinear` once Tier 1b is done.

**Blocked by:** Tier 1b (HeatKernel/Bilinear.lean in gaussian-field).

### 2b. `torusContinuumGreen_pos` (TorusPropagatorConvergence.lean)

Currently `sorry`. Once `torusContinuumGreen` is defined via
`greenFunctionBilinear`, this follows from `greenFunctionBilinear_pos`
(Fourier coefficients of nonzero f can't all vanish).

**Blocked by:** Tier 2a.

### 2c. `torusEmbeddedTwoPoint_uniform_bound` (TorusPropagatorConvergence.lean)

Currently `sorry`. Proof: all eigenvalues of -Δ_lat + m² satisfy λ ≥ m²,
so E[Φ_N(f)²] ≤ (1/m²)·‖f‖². The Riemann sum over the finite torus is
bounded by ‖f‖²_{L²(T²)} + O(1/N).

**Blocked by:** Tier 2a (need the definition to state the bound precisely).
Can also be proved directly from the spectral representation.

### 2d. Z₂ symmetry sorry (TorusGaussianLimit.lean, line 236)

Currently `sorry` inside `torusGaussianLimit_converges`. The lattice GFF
is Z₂-symmetric (Gaussian is even), and Z₂ symmetry is preserved under
weak limits (preimage of measurable sets under negation).

**Blocked by:** Nothing — provable from existing API.

### 2e. Full sequence convergence sorry (TorusGaussianLimit.lean, line 246)

Currently `sorry`. Standard topology argument: if every subsequence has a
further subsequence converging to the same limit (by Gaussian uniqueness),
then the full sequence converges.

**Proof strategy:** By contradiction. If the full sequence doesn't converge
to μ, there exists ε > 0 and a subsequence staying ε-away. But that
subsequence has a further convergent subsequence (by tightness + Prokhorov),
which must converge to μ (by uniqueness), contradiction.

**Blocked by:** Nothing — pure topology, provable from existing API.

## Tier 3: Core Analytical Axioms

These are the mathematically substantive axioms that require real analytical
arguments. They are correctly formulated and could be proved with sufficient
Mathlib infrastructure.

### 3a. `torus_propagator_convergence` (1 axiom)

Lattice eigenvalues `(4N²/L²) sin²(πn/N) + m²` converge to continuum
eigenvalues `(2πn/L)² + m²` for each mode. Combined with rapid decay of
smooth Fourier coefficients, dominated convergence gives the result.

**Difficulty:** Medium. Pure UV limit, no IR subtlety. The mode-by-mode
convergence is elementary (sin(x)/x → 1). The dominated convergence
argument needs uniform bounds on the partial sums.

**References:** Glimm-Jaffe §6.1, Simon Ch. I.

### 3b. `torusContinuumMeasures_tight` (1 axiom)

Tightness of {ν_N} on Configuration(TorusTestFunction L). Uses Mitoma
criterion: tightness of 1D marginals (each is N(0, σ²_N) with σ² bounded
by `torusEmbeddedTwoPoint_uniform_bound`).

**Difficulty:** Medium. The Mitoma criterion reduces to 1D Gaussian
tightness, which is elementary (bounded variance ⇒ tight).

**References:** Mitoma (1983), Fernique (1975).

### 3c. `torusGaussianLimit_isGaussian` (1 axiom)

Weak limits of Gaussian measures are Gaussian. Characteristic functionals
converge pointwise (weak convergence), and the Gaussian form exp(-½σ²)
is preserved in the limit by continuity.

**Difficulty:** Medium. Standard but requires Bochner-Minlos on nuclear
Fréchet spaces.

**References:** Fernique §III.4, Simon Ch. I.

### 3d. `torusLimit_covariance_eq` (1 axiom)

Weak convergence transfers second moments when they're uniformly bounded.
This is uniform integrability + weak convergence ⇒ moment convergence.

**Difficulty:** Easy-Medium. Standard measure theory (Vitali convergence
theorem or direct uniform integrability argument).

### 3e. `gaussian_measure_unique_of_covariance` (1 axiom)

Gaussian measures on nuclear spaces are determined by their covariance.
Follows from Bochner-Minlos: the characteristic functional exp(-½C(f,f))
determines the measure.

**Difficulty:** Easy (given Bochner-Minlos). The uniqueness statement is
essentially the injectivity of the Fourier transform on measures.

## Tier 4: Interacting Extension

### 4a. `torus_interacting_tightness` (1 axiom)

The interacting measures μ_{P,N} = (1/Z_N) e^{-V_N} dμ_{GFF,N} are tight.

**Proof strategy:** Cauchy-Schwarz density transfer.
E_P[|ω(f)|²] ≤ (1/Z)·E_GFF[|ω(f)|⁴]^{1/2} · E_GFF[e^{-2V}]^{1/2}.
- GFF 4th moment: controlled (Gaussian Wick formula)
- E_GFF[e^{-2V}]: bounded by Nelson's hypercontractive estimate
- Combined with Gaussian tightness ⇒ interacting tightness

**Difficulty:** Hard. Requires Nelson's estimate (hypercontractivity) and
careful bounds on the partition function.

**References:** Simon Ch. V, Nelson (1973), Guerra-Rosen-Simon.

### 4b. `torusInteractingLimit_exists` (PROVED)

Already proved from tightness + Polish + Prokhorov. No further work needed.

## Dependency Graph

```
Tier 1b (HeatKernel)
  └→ Tier 2a (torusContinuumGreen def)
       ├→ Tier 2b (Green positivity)
       └→ Tier 2c (uniform bound)
            └→ Tier 3b (tightness)  ←── already used via axiom

Tier 1a (evalCLM)  ←── already used via sorry

Tier 2d (Z₂ symmetry)     ←── independent
Tier 2e (full convergence) ←── independent

Tier 3a (propagator convergence)  ←── independent
Tier 3c (Gaussianity of limit)    ←── independent
Tier 3d (covariance transfer)     ←── independent
Tier 3e (Gaussian uniqueness)     ←── independent

Tier 4a (interacting tightness)   ←── depends on Tier 3b conceptually
```

## Implementation Order

**Phase A — gaussian-field infrastructure:**
1. Complete `evalCLM` (fill sorry on torus branch)
2. Create `HeatKernel/Bilinear.lean` with definitions + key properties
3. Build and test gaussian-field

**Phase B — pphi2 definitions:**
4. Replace `torusContinuumGreen` sorry with `greenFunctionBilinear`
5. Prove `torusContinuumGreen_pos` from `greenFunctionBilinear_pos`
6. Prove `torusEmbeddedTwoPoint_uniform_bound`

**Phase C — pphi2 topology:**
7. Prove Z₂ symmetry sorry
8. Prove full sequence convergence sorry

**Phase D — axiom reduction (ongoing):**
9. Attempt to prove analytical axioms as infrastructure matures
10. Priority order: 3e (uniqueness) > 3d (covariance) > 3c (Gaussianity)
    > 3a (propagator) > 3b (tightness) > 4a (interacting)

## Success Criteria

- All 5 current sorries filled (Tier 2)
- `torusContinuumGreen` has a real definition (not sorry)
- `lake build` passes with no regressions
- Axiom count ideally decreases (some Tier 3 axioms proved)
- Interacting limit exists on torus (Tier 4)
