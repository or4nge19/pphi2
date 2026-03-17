# Proving `osgood_separately_analytic`

## Current Status

The axiom `osgood_separately_analytic` in `Pphi2/GeneralResults/ComplexAnalysis.lean`
is the sole remaining axiom for `analyticOnNhd_integral`. Everything else is proved.

```lean
axiom osgood_separately_analytic {n : ℕ}
    {f : (Fin n → ℂ) → ℂ}
    (hf_cont : Continuous f)
    (hf_sep : ∀ (j : Fin n) (z₀ : Fin n → ℂ),
      AnalyticAt ℂ (fun t : ℂ => f (Function.update z₀ j t)) (z₀ j)) :
    AnalyticOnNhd ℂ f Set.univ
```

## Reference Implementation

Geoffrey Irving formalized Osgood and full Hartogs for ℂ² in `girving/ray`:
- Repo cloned at `../girving-ray`
- `Ray/Hartogs/Osgood.lean` — Osgood for `ℂ × ℂ → E` (with continuity)
- `Ray/Hartogs/Hartogs.lean` — Full Hartogs for `ℂ × ℂ → E` (no continuity)
- Uses Lean `v4.27.0-rc1`, Mathlib master

Key theorem (`Osgood.lean:572`):
```lean
public theorem osgood {E : Type} {f : ℂ × ℂ → E} {s : Set (ℂ × ℂ)}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (o : IsOpen s) (fc : ContinuousOn f s)
    (fa0 : ∀ z0 z1, (z0, z1) ∈ s → AnalyticAt ℂ (fun z0 ↦ f (z0, z1)) z0)
    (fa1 : ∀ z0 z1, (z0, z1) ∈ s → AnalyticAt ℂ (fun z1 ↦ f (z0, z1)) z1) :
    AnalyticOnNhd ℂ f s
```

## Proof Plan for ℂⁿ

### Approach: Induction on n using Cauchy integral formula

**Base cases:**
- `n = 0`: constant function, trivially analytic
- `n = 1`: separately analytic in 1 variable = analytic (trivial)
- `n = 2`: adapt Irving's `osgood` via `Fin 2 → ℂ ≃ ℂ × ℂ`

**Inductive step (n → n+1):**
Use `Fin (n+1) → ℂ ≃ ℂ × (Fin n → ℂ)` via `Equiv.piFinSucc`.

Given `f : ℂ × (Fin n → ℂ) → ℂ` continuous and separately analytic:
1. For fixed `v ∈ Fin n → ℂ`, `w ↦ f(w, v)` is analytic on ℂ
2. For fixed `w ∈ ℂ`, `v ↦ f(w, v)` is separately analytic + continuous,
   hence jointly analytic by IH
3. Use 1D Cauchy integral formula in `w`:
   `f(w, v) = Σₖ aₖ(v) · (w - w₀)ᵏ`
   where `aₖ(v) = (2πi)⁻¹ ∮ f(ζ, v) / (ζ-w₀)^{k+1} dζ`
4. Each `aₖ` is analytic in `v` (contour integral of analytic function)
5. Construct joint power series from the product expansion

### Key difficulty: Step 4

Showing `v ↦ ∮ f(ζ, v) h(ζ) dζ` is analytic when `v ↦ f(ζ, v)` is
analytic for each `ζ`. This is `analyticOnNhd_integral` for contour
integrals, but we can't use our theorem (it depends on Osgood).

**Resolution:** For contour integrals specifically, the Riemann sum
approximation works: finite sums of analytic functions are analytic,
and the convergence is uniform on compact sets. Use the 1D Weierstrass
theorem in each coordinate separately (from Mathlib) plus continuity
(from uniform convergence) to re-enter the IH.

Alternatively: directly construct the power series coefficients
`qₖ = ∮ pζ,k h(ζ) dζ` where `pζ,k` are the power series coefficients
of `v ↦ f(ζ, v)`, and show convergence.

### Alternative: Generalize Irving's proof to `ℂ × E`

Instead of `ℂ × ℂ`, prove Osgood for `ℂ × E` where `E` is any
finite-dimensional complex Banach space. Irving's proof structure
(Cauchy integral in first variable, Baire category, subharmonic
estimates) should carry over. This gives the inductive step directly.

## Mathlib lemmas needed

- `Equiv.piFinSucc` — `Fin (n+1) → ℂ ≃ ℂ × (Fin n → ℂ)`
- `circleIntegral` — Cauchy contour integrals
- `hasSum_of_summable_norm` — absolute convergence of power series
- `TendstoLocallyUniformlyOn.differentiableOn` — Weierstrass (1D)
- `DifferentiableOn.analyticOnNhd` — Goursat (1D)

## References

- Krantz, *Function Theory of Several Complex Variables*, Thm 7.2.1
- Irving, `girving/ray`, `Ray/Hartogs/Osgood.lean`
- Hörmander, *An Introduction to Complex Analysis in Several Variables*, Ch. 2
