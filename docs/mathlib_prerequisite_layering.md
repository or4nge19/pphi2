# Mathlib-style prerequisite layering (P) vs construction goal (X)

This note fixes vocabulary for how `pphi2` should grow: **theorem-driven** extensions of **real Mathlib (and gaussian-field) types**, with **definitions only where a Mathlib PR would plausibly carry the same generality**, and **explicit tracking** of everything else as application glue or admitted analysis.

## X — construction goal (this project)

**X** is the *assembled* statement the repository aims at, not the ambient linear algebra:

- A **probability measure** on `Configuration (SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ)` (tempered distributions on `ℝ²` in the Gaussian-field sense) that arises as a **continuum limit** of the Glimm–Jaffe/Nelson **lattice** `P(Φ)₂` construction.
- That measure **satisfies** the bundled Osterwalder–Schrader interface formalized here (`SatisfiesFullOS` / OS0–OS4), with **honest** separation between what is **proved**, what is **axiomatized** (substantive analysis), and what is **limit/inheritance** infrastructure.

References for X (keep in sync with module docstrings and `refs/`):

| Primary texts | Role in X |
|---------------|-----------|
| Glimm–Jaffe, *Quantum Physics* | Lattice → continuum, transfer matrix, OS-style clustering input |
| Simon, *The P(φ)₂ Euclidean QFT* | Same pipeline; Ch. I propagator / covariance scaling |
| Nelson (1973) | Markov/random-field → Euclidean measure |
| Osterwalder–Schrader (1973, 1975) | Axiom list OS0–OS4; reconstruction hypotheses |
| Guerra–Rosen–Simon, *Ann. Math.* **101** (1975) Part II | Lattice Markov fields (`refs/GRS1975-p2.md`); infinite `ℤ²` vs our finite torus |

## Reference map: formal layer ↔ text ↔ Mathlib (P)

Use this to avoid **semantic debt**: every axiom or boundary `def` should appear in one row with a **citation** and a **P-anchor** where possible.

| Formal locus | Text anchor | P (Mathlib / GF) anchor |
|--------------|-------------|-------------------------|
| `ContinuumSpaceTime d`, `ContinuumTestFunction d` | Euclidean `ℝ^d`, `S(ℝ^d)` | `EuclideanSpace ℝ (Fin d)`, `SchwartzMap` (`ContinuumSpaceTime_eq`, … in `Backgrounds/EuclideanPlane.lean`) |
| `schwartzOfReal`, `schwartz_decompose`, `continuumEuclideanActionComplex` vs re/im | OS generating functional on `S(ℝ^d;ℂ)` | Mathlib `SchwartzMap.postcompCLM`; `EuclideanComplex.lean`: `schwartz_decompose_continuumEuclideanActionComplex`, `generatingFunctionalℂ_ofReal_add_real_smul` |
| `∫ exp(i⟨ω,f⟩)` real/imag decomposition | Characteristic functional as cosine/sine moments | `GeneralResults/FunctionalAnalysis.lean`: `configuration_expIntegral_re_eq_integral_cos`, `configuration_expIntegral_im_eq_integral_sin`; `EuclideanOS.lean` and torus/cylinder routes are specializations |
| `latticeEuclideanTimeSeparation` | Cyclic Euclidean time on `(ℤ/Nℤ)²` | `ZMod.valMinAbs.natAbs` (`ZMod.valMinAbs_natAbs_eq_min`); `refs/GRS1975-p2.md` §IV for infinite lattice |
| OS4 lattice clustering axioms | Transfer-matrix gap → exponential decay | Torus: cyclic `d_cyc` in exponent; continuum `|τ|` after IR (`OS4_MassGap` header) |
| `latticeGreenBilinear_basis_tendsto_continuum` | Glimm–Jaffe §6.1; Simon Ch. I | Fourier / discrete Laplacian resolvent limit; single named IR axiom in `PropagatorConvergence` |
| `SatisfiesFullOS` (`OSAxioms`) | OS I+II (1973, 1975) | Bundles `EuclideanOS` + `plane2TimeStructure`; not a Mathlib type |

## P — prerequisites (Mathlib / gaussian-field / shared QFT-facing lemmas)

**P** is any statement or type that **does not** mention `Pphi2`-specific physics data (`InteractionPolynomial`, Wick-ordered lattice interaction, `interactingLatticeMeasure`, route-specific OS bundles, etc.):

| Area | Mathlib-style objects (examples) |
|------|----------------------------------|
| Ambient analysis | `EuclideanSpace`, `SchwartzMap`, `Function.HasTemperateGrowth`, `WeakDual`, `MeasureTheory` |
| Finite symmetry / periodicity | `ZMod`, `ZMod.valMinAbs`, `Fin`, `PiLp` |
| Linear geometry | `LinearIsometryEquiv`, `ContinuousLinearMap`, `NormedSpace` |
| Probability | `IsProbabilityMeasure`, moments, variance |
| Repo “near-Mathlib” | `GaussianField.*` (lattice, configuration, translation), `Pphi2.GeneralResults.*` candidates for upstream |

**Rule:** If a lemma can be stated with **only** P-types and imports from **Mathlib + gaussian-field**, it belongs in `GeneralResults/` or a future upstream PR, not inside a proof file that fixes `P(Φ)₂` data.

## Boundary definitions — allowed, but not “Mathlib core”

These are **optimal for this construction** but still **application-specific**; they should stay small and be **characterized by theorems** in terms of P:

- **`EuclideanPlaneBackground`**: a **single-field** structure `dim : ℕ`; all continuum types are **abbreviations** to `EuclideanSpace` / `SchwartzMap` / `Configuration` / `≃ₗᵢ`. *Mathlib analogue:* a typeclass or `def` “Euclidean space of dimension `d`” — here we use the explicit `Fin d` model only.
- **Lattice Euclidean time** (`latticeEuclideanTimeShift`, `latticeEuclideanTimeSeparation`, `latticeConfigEuclideanTimeShift`): encode the **choice of time axis** on `FinLatticeSites 2 N` and **cyclic separation** via **`ZMod.valMinAbs.natAbs`** (see `InteractingMeasure/LatticeEuclideanTime.lean`). *Mathlib:* cyclic distance is already `ZMod.valMinAbs`; the **embedding** into `FinLatticeSites` is QFT-specific.
- **Interaction / OS bundle**: `InteractionPolynomial`, Wick ordering, lattice measure, OS axiom predicates — **intrinsically** part of X, not P.

## Theorem-driven discipline (no hidden debt)

1. **Every non-trivial `def`** should admit at least one **`theorem`** that re-expresses it in **P vocabulary** (e.g. `latticeEuclideanTimeSeparation_eq_min`, `translate_apply`, `schwartzTranslate_apply`).
2. **Axioms** are **single named points** for substantive analysis (spectral gap, clustering, propagator IR limit, etc.), with **docstrings** that cite a **precise** textbook location — not placeholders for “obvious” Mathlib lemmas.
3. **Abbreviations** are **not** semantic debt: they are **notational specialization** of P-types, as long as no theorem quantifies over a “new” universe.
4. **Ambient theorem debt** is avoided by **not** stating lemmas that silently assume a stronger `μ` than the construction provides; use explicit predicates (`IsPphi2Limit`, `SatisfiesFullOS`, …).

## Reuse / upstream path

- **Upstream to Mathlib:** cyclic `ZMod` facts, Schwartz composition, variance identities, Dynin–Mityagin-style nuclear estimates — **if** stated without `Pphi2` namespaces.
- **Stay in `pphi2`:** assembly of lattice → continuum → OS, and any axiom that is **literally** the constructive `P(Φ)₂` theorem in Glimm–Jaffe/Simon.

## Related notes

- Broader foundational routes (measure vs Schwinger vs reconstruction): `docs/foundational-roadmap.md`.
- Axiom inventory and verification notes: `docs/axiom_audit.md`, `docs/axiom_proof_plans.md`.
- In-repo transcriptions: `refs/GRS1975.md`, `refs/GRS1975-p2.md`.
