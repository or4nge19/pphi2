# Axiom Status Snapshot

*Current state of pphi2's axiom inventory. No history — see
[`axiom_audit.md`](axiom_audit.md) for the historical log of audit
passes and discharges. Last refreshed: 2026-06-02.*

## At a glance

| Count | Value |
|---|---|
| pphi2 axioms (active) | **18** (17 public + 1 `private`) |
| pphi2 sorries | **0** — `rough_error_variance` is now fully proved; `#print axioms Pphi2.rough_error_variance` shows only `[propext, Classical.choice, Quot.sound]`. |
| `lake build` | clean (exit code 0, 2026-06-02 after pulling `origin/main`) |
| Direct upstream deps (pins from `lake-manifest.json`) | gaussian-field (`dc2b3b8`, **3 axioms / 0 sorries** — verified via `count_axioms.sh`); gibbs-variational (`a7535d1`, **0 axioms / 1 off-critical-path sorry**); markov-semigroups (`acf6491`, tracks `main`), gaussian-hilbert (`56ee09f`, tracks `main`), bochner (`34222bb`, tracks `main`), reflection-positivity (`1940650`, tracks `main`). Sister-repo axiom counts drift with `main` and are not re-verifiable from here (`count_axioms.sh` covers only pphi2 + gaussian-field) — see each repo's own `AXIOM_AUDIT.md` for current figures (gaussian-hilbert was ~1 axiom at the 2026-05-11 audit; markov-semigroups ~11). |

The `scripts/count_axioms.sh` script reports the declaration count directly:
18 pphi2 axioms and 0 pphi2 sorries.

### Conventions

Audit-table conventions per
[`research-dev/library/lean/AXIOM_MANAGEMENT.md`](https://github.com/mrdouglasny/research-dev/blob/main/library/lean/AXIOM_MANAGEMENT.md)
§2:

| Sources | Meaning |
|---|---|
| `GR` | External Gemini review (chat-mode) |
| `DT` | Gemini deep think verification |
| `SA` | Self-audit (agent's own assessment) |
| `PR` | Peer review (another human or agent) |
| `LP` | Literature proof (cited theorem with page number) |

| Rating | Meaning |
|---|---|
| `Standard` | Well-known fact, correctly stated |
| `Likely correct` | Mathematically sound, needs type/quantifier check |
| `Needs review` | Potentially problematic or non-standard formulation |
| `Placeholder` | Conclusion is `True`, trivially weak, or a research endpoint |
| `Flagged` | Known issue identified by review |

## Critical-path axioms

### T² interacting OS theory (`torusInteracting_satisfies_OS`, OS0–OS4 on T²)

Verified via `#print axioms`: **0 non-builtin axioms** for
`Pphi2.torusInteracting_satisfies_OS`.

| Axiom | File | Discharge plan | Effort |
|---|---|---|---|
| — | — | No active pphi2 axiom in this closure. | — |

After this discharge, 3 transitive OU placeholders from gaussian-hilbert
will appear in `torusInteracting_satisfies_OS`'s axiom set; those have
their own plan: [`gaussian-hilbert/docs/ou-mehler-discharge-plan.md`](https://github.com/mrdouglasny/gaussian-hilbert/blob/main/docs/ou-mehler-discharge-plan.md) (~3-4 weeks).

### T² Gaussian (free-field) OS theory (`torusGaussianLimit_satisfies_OS`)

Verified via `#print axioms`: **0 non-builtin axioms**. Fully proved.

### Flat-ℝ² S'(ℝ²) continuum theory (alternative target)

| Axiom | File | Discharge plan | Effort |
|---|---|---|---|
| `latticeGreenBilinear_basis_tendsto_continuum` | `GaussianContinuumLimit/PropagatorConvergence.lean:103` | [`lattice-green-flat-Rd-discharge-plan.md`](../plans/lattice-green-flat-Rd-discharge-plan.md) (Strategy A) | ~3 weeks |

NOT on the T² critical path. Only needed if the project pushes to flat-ℝ²
S'(ℝ²) Wightman directly.

## Full axiom inventory

### Bridge / phase-6 (3 axioms — pphi2 ↔ φ⁴ classification)

| Axiom | File:Line | Rating | Sources | Notes |
|---|---|---|---|---|
| `schwinger_agreement` | `Bridge.lean:263` | Likely correct | DT 2026-02-24 | n-point Schwinger function equality at weak coupling. |
| `os2_from_phi4` | `Bridge.lean:334` | Likely correct | DT 2026-02-24 | Requires `IsPhi4ContinuumLimit`. |
| `pphi2_nontriviality` | `Main.lean:128` | Placeholder | — | Phase-4 research endpoint: bridge to φ⁴; downstream of `same_continuum_measure`. |

`measure_determined_by_schwinger` was discharged 2026-06-02 via
`TorusContinuumLimit/MeasureUniqueness.lean`.

### Continuum-limit machinery (4 axioms — concrete construction and inheritance)

| Axiom | File:Line | Rating | Sources | Notes |
|---|---|---|---|---|
| `continuum_exponential_moment_bound` | `ContinuumLimit/AxiomInheritance.lean:123` | Likely correct | SA 2026-04-19 | Design bridge: mixed `L¹`/Green `∫ exp(\|ωf\|) dμ ≤ exp(c₁∫\|f\| + c₂ G(f,f))`. |
| `continuum_exponential_clustering` | `ContinuumLimit/AxiomInheritance.lean:354` | Likely correct | GR 2026-03-07 | Correct for P(Φ)₂; spectral-gap input for continuum OS4. |
| `continuumLimit_nonGaussian` | `ContinuumLimit/Convergence.lean:256` | Placeholder | — | Phase-4 research endpoint: nontriviality of the limit. |
| `pphi2_limit_exists` | `ContinuumLimit/Convergence.lean:282` | Standard | LP | Coupled UV/IR Prokhorov construction from concrete lattice approximants. Replaces the former theorem that was witnessed by `δ₀` under the too-weak marker predicate. |

`canonical_continuumMeasure_cf_tendsto` was discharged 2026-06-02: it is now a
theorem extracted from the strengthened `IsPphi2Limit` certificate.

### Cluster A — Nelson exponential estimate (1 axiom — bridge)

| Axiom | File:Line | Rating | Sources | Notes |
|---|---|---|---|---|
| `nelson_exponential_estimate_master_bounded` | `NelsonEstimate/PolynomialChaosBridge.lean:1310` | Standard | DT 2026-05-08, DT 2026-05-10 | Compatibility wrapper for the bounded-volume Nelson estimate. Consumers should move to the fixed-volume API or prove the genuinely stronger coupled-volume estimate. |

### Cluster A Phase B — discharged textbook theorems

The two former Phase B textbook axioms are now theorems in
`NelsonEstimate/CovarianceBoundsGJ.lean`:

- `smoothWickConstant_le_log_uniform_in_aN`
- `canonicalRoughCovariance_pow_sum_le_uniform_in_aN`

They no longer contribute to the pphi2 axiom inventory. Historical
design and discharge notes remain in
[`phase-B-textbook-axioms.md`](phase-B-textbook-axioms.md).

### Spectral gap / mass gap (4 axioms)

| Axiom | File:Line | Rating | Sources | Notes |
|---|---|---|---|---|
| `spectral_gap_uniform` | `TransferMatrix/SpectralGap.lean:89` | Standard | LP | Spectral gap of transfer matrix uniform in lattice size. |
| `spectral_gap_lower_bound` | `TransferMatrix/SpectralGap.lean:100` | Standard | LP | Reed-Simon XIII.12 (cited in CLAUDE.md). |
| `two_point_clustering_from_spectral_gap` | `OSProofs/OS4_MassGap.lean:137` | Standard | — | Standard reconstruction theorem. |
| `general_clustering_from_spectral_gap` | `OSProofs/OS4_MassGap.lean:160` | Standard | — | n-point version. |

### OS proofs (2 axioms)

| Axiom | File:Line | Rating | Sources | Notes |
|---|---|---|---|---|
| `rotation_cf_defect_polylog_bound` | `OSProofs/OS2_WardIdentity.lean:614` | Likely correct | SA 2026-04-19 | Polylog `a²` defect bound for `rotationCFDefect`, uniform in N. Replaces stronger pointwise formulation. |
| `gaussian_rp_cov_perfect_square` (`private`) | `OSProofs/OS3_RP_Lattice.lean:648` | Standard | SA | Covariance form is a perfect square (Gaussian RP technical). |

### Flat-ℝ² Gaussian continuum (1 axiom — alternative target)

| Axiom | File:Line | Rating | Sources | Notes |
|---|---|---|---|---|
| `latticeGreenBilinear_basis_tendsto_continuum` | `GaussianContinuumLimit/PropagatorConvergence.lean:103` | Standard | SA | Spectral lattice Green bilinear → continuum on basis pairs. **Plan**: [`lattice-green-flat-Rd-discharge-plan.md`](../plans/lattice-green-flat-Rd-discharge-plan.md) (Strategy A, ~3 weeks). NOT on T² critical path. |

### AsymTorus / cylinder-isotropic layer (3 axioms)

| Axiom | File:Line | Rating | Sources | Notes |
|---|---|---|---|---|
| `asymInteracting_expMoment_volume_uniform` | `AsymTorus/AsymContinuumLimit.lean:621` | Likely correct | DT | Volume-uniform interacting exponential moment for the asymmetric/cylinder family. |
| `asymInteracting_mgf_gaussianDominated` | `AsymTorus/AsymExpMomentDischarge.lean:127` | Standard | LP | Newman/Lee-Yang style MGF domination input used in the discharge architecture. |
| `asymInteractingVariance_le_freeVariance_Lt_uniform` | `AsymTorus/AsymExpMomentDischarge.lean:190` | Standard | LP | Uniform variance comparison input for the cylinder shortcut. |

`AsymTorus/AsymTorusOS.lean` is axiom-free as of 2026-06-02.
`asymTorusInteracting_exponentialMomentBound` was discharged by combining the
cutoff exponential-moment bound, the uniform second-moment estimate, and the
generic BC weak-limit exponential-moment transfer theorem.

## Upstream axiom counts (transitively imported)

For full transitive axiom dependencies of pphi2's main theorems via
`#print axioms`, see
[`.lake/packages/«gaussian-hilbert»/docs/AXIOM_AUDIT.md`](https://github.com/mrdouglasny/gaussian-hilbert/blob/main/docs/AXIOM_AUDIT.md)
and [`.lake/packages/MarkovSemigroups/docs/AXIOM_AUDIT.md`](https://github.com/mrdouglasny/markov-semigroups/blob/main/docs/AXIOM_AUDIT.md).

| Repo | Axioms | Plan-coverage |
|---|---|---|
| pphi2 | 18 | No non-builtin axiom in `torusInteracting_satisfies_OS`; remaining axioms are broader bridge/continuum/AsymTorus/OS2-OS4/QFT-estimate items with literature-backed plans |
| gaussian-hilbert | 4 | All 4 plan-covered: 1 (`polynomial_dense_L2_of_subGaussian`) is DT-vetted Standard; 3 (OU placeholders) covered by `ou-mehler-discharge-plan.md` |
| markov-semigroups | 11 | All textbook with literature refs in `AXIOM_AUDIT.md`; no near-term discharge plans (long-term debt) |
| gaussian-field | 3 | Down from 8 after the 2026-05-10 cylinder/Hermite discharges + the 2026-05-11 `gff_wickPower_two_site_inner` proof (axiom-free, Janson 2-site Wick formula on lattice GFF). Remaining 3 axioms are Gemini-vetted Standard classical-analysis (embed-L²-uniform-bound, fourier-multiplier-Schwartz, Hermite-Galerkin tendsto). |

## How to update this file

When adding/removing/discharging an axiom:

1. Update the relevant section above with the new file:line, rating, plan link.
2. Run `scripts/count_axioms.sh` to refresh the at-a-glance count.
3. If a critical-path axiom changes status, update the **Critical-path axioms** section.
4. Add a chronological entry to [`axiom_audit.md`](axiom_audit.md) describing what changed and why (this file is the snapshot; that file is the log).
5. If the change affects upstream consumers (lgt, pphi2N, etc.), bump pins in those repos.
