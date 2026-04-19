/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas

# Lattice Propagator Convergence

The main analytical content of the Gaussian continuum limit: the lattice
Green's function converges to the continuum Green's function as a → 0.

## Main results

- `latticeGreenBilinear_basis_tendsto_continuum` — (axiom) basis-pair spectral
  convergence
- `latticeGreenBilinear_tendsto_continuum` — theorem extending basis-pair
  convergence to arbitrary Schwartz test functions
- `propagator_convergence` — theorem deduced from
  `embeddedTwoPoint_eq_latticeGreenBilinear`
- `embeddedTwoPoint_uniform_bound` — `E[Φ_a(f)²] ≤ C · ‖f‖²` uniformly in a, N
- `continuumGreenBilinear_pos` — `G(f,f) > 0` for nonzero f

## Mathematical background

### Propagator convergence

The lattice propagator in Fourier space is:

  `Ĉ_a(k) = 1 / ((4/a²) Σ_i sin²(πk_i a/L) + m²)`

For k in any compact set, as a → 0 with L = Na → ∞:

  `Ĉ_a(k) → 1 / (|k|² + m²)`

since `(2/a) sin(πk_i a/L) → 2πk_i/L → k_i` (with appropriate scaling).

The rapid decay of f̂, ĝ controls the contribution from large k, giving:

  `a^{2d} Σ_{x,y} C_a(x,y) f(ax) g(ay) → ∫ f̂(k) ĝ(k) / (|k|²+m²) dk/(2π)^d`

### Uniform bound

All eigenvalues of `-Δ_a + m²` satisfy `λ ≥ m²`, so:

  `E[Φ_a(f)²] = ⟨f_a, C_a f_a⟩ ≤ (1/m²) · ‖f_a‖²_{L²(Λ_a)}`

The discretized L² norm `a^d Σ_x |f(ax)|²` converges to `‖f‖²_{L²(ℝ^d)}` and is
uniformly bounded for Schwartz f, giving `E[Φ_a(f)²] ≤ C/m²`.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
-/

import Pphi2.GaussianContinuumLimit.EmbeddedCovariance
import Pphi2.GeneralResults.LatticeProductDFT
import Pphi2.GeneralResults.DyninMityaginBilinear
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.MeasureTheory.Integral.Prod
import SchwartzNuclear.HermiteNuclear
import SchwartzNuclear.Periodization

noncomputable section

open GaussianField MeasureTheory Filter

namespace Pphi2

variable (d N : ℕ) [NeZero N]

private noncomputable instance continuumFinNonempty [Fact (0 < d)] : Nonempty (Fin d) :=
  Fin.pos_iff_nonempty.mp Fact.out

private noncomputable instance continuumEuclideanNontrivial [Fact (0 < d)] :
    Nontrivial (EuclideanSpace ℝ (Fin d)) := inferInstance

@[reducible] private noncomputable instance continuumTestFunction_dyninMityagin [Fact (0 < d)] :
    DyninMityaginSpace (ContinuumTestFunction d) := by
  cases d with
  | zero =>
      exact False.elim ((lt_irrefl 0) Fact.out)
  | succ d' =>
      simpa [ContinuumTestFunction_eq] using
        (schwartz_dyninMityaginSpace_euclidean d')

/-! ## Propagator convergence -/

/- **Basis-pair lattice propagator converges to the continuum Green's function.**

This is the remaining analytic input after all algebraic rewrites:
for each pair of Dynin-Mityagin basis vectors and lattice parameters
`a → 0` with `Na → ∞`, the lattice spectral Green form converges to the
continuum Green form.

The full Schwartz-space convergence theorem `latticeGreenBilinear_tendsto_continuum`
is proved later in this file by two DM-expansion steps plus polynomial bounds
on the lattice bilinear form applied to basis vectors.

Reference: Glimm-Jaffe §6.1, Simon Ch. I. -/
section ConvergenceAxiom

variable [Fact (0 < d)]
axiom latticeGreenBilinear_basis_tendsto_continuum
    (mass : ℝ) (hmass : 0 < mass)
    -- Sequence of lattice spacings tending to 0
    (a_seq : ℕ → ℝ) (ha_pos : ∀ n, 0 < a_seq n)
    (ha_lim : Tendsto a_seq atTop (nhds 0))
    -- Sequence of lattice sizes with N_n · a_n → ∞
    (N_seq : ℕ → ℕ) [∀ n, NeZero (N_seq n)]
    (hNa : Tendsto (fun n => (N_seq n : ℝ) * a_seq n) atTop atTop)
    (i j : ℕ) :
    Tendsto
      (fun n =>
        latticeGreenBilinear d (N_seq n) (a_seq n) mass
          (DyninMityaginSpace.basis i)
          (DyninMityaginSpace.basis j))
      atTop
      (nhds
        (continuumGreenBilinear d mass
          (DyninMityaginSpace.basis i)
          (DyninMityaginSpace.basis j)))

end ConvergenceAxiom

/-- The lattice Green bilinear form is the explicit product-DFT spectral sum
for the discretized lattice test fields. This removes the last algebraic layer
between `latticeGreenBilinear` and the UV/IR convergence problem. -/
theorem latticeGreenBilinear_eq_product_dft_spectral_sum
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : ContinuumTestFunction d) :
    latticeGreenBilinear d N a mass f g =
      ∑ m : (Fin d → Fin N),
        latticeFourierProductCoeff N d (latticeTestField d N a f) m *
          latticeFourierProductCoeff N d (latticeTestField d N a g) m /
          (((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2) *
            latticeFourierProductNormSq N d m) := by
  rw [latticeGreenBilinear, ← lattice_covariance_eq_spectral]
  exact abstract_spectral_eq_dft_spectral_family (N := N) d a mass ha hmass
    (latticeTestField d N a f) (latticeTestField d N a g)

/-- Basis-pair specialization of the product-DFT spectral formula.
This is the concrete spectral sum whose convergence remains to be proved. -/
theorem latticeGreenBilinear_basis_eq_product_dft_spectral_sum [Fact (0 < d)]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (i j : ℕ) :
    latticeGreenBilinear d N a mass
      (DyninMityaginSpace.basis i)
      (DyninMityaginSpace.basis j) =
      ∑ m : (Fin d → Fin N),
        latticeFourierProductCoeff N d
          (latticeTestField d N a (DyninMityaginSpace.basis i)) m *
          latticeFourierProductCoeff N d
            (latticeTestField d N a (DyninMityaginSpace.basis j)) m /
          (((∑ k : Fin d, latticeEigenvalue1d N a (m k)) + mass ^ 2) *
            latticeFourierProductNormSq N d m) := by
  simpa using latticeGreenBilinear_eq_product_dft_spectral_sum
    (d := d) (N := N) (a := a) (mass := mass) ha hmass
    (DyninMityaginSpace.basis i) (DyninMityaginSpace.basis j)

/-- In positive dimension, the continuum Dynin-Mityagin basis is the flattened
multi-dimensional Hermite basis coming from `schwartzRapidDecayEquivNd`. -/
private theorem continuum_basis_apply_eq_hermite (d : ℕ)
    (n : ℕ) (x : ContinuumSpaceTime (d + 1)) :
    DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 1)) n x =
      hermiteFunctionNd (d + 1) ((multiIndexEquiv d).symm n) x := by
  change (((schwartzRapidDecayEquivNd d).symm (RapidDecaySeq.basisVec n)) x =
    hermiteFunctionNd (d + 1) ((multiIndexEquiv d).symm n) x)
  rw [schwartzRapidDecayEquivNd_symm_apply]
  simp [RapidDecaySeq.basisVec]

/-- In one dimension, the continuum DM basis is exactly the classical Hermite
basis evaluated on the unique Euclidean coordinate. -/
private theorem continuum_basis_apply_eq_hermite1D
    (n : ℕ) (x : ContinuumSpaceTime 1) :
    DyninMityaginSpace.basis (E := ContinuumTestFunction 1) n x =
      schwartzHermiteBasis1D n (x 0) := by
  change (((schwartzRapidDecayEquivNd 0).symm (RapidDecaySeq.basisVec n)) x =
    schwartzHermiteBasis1D n (x 0))
  rw [schwartzRapidDecayEquivNd_symm_apply]
  simp [RapidDecaySeq.basisVec, hermiteFunctionNd, multiIndexEquiv,
    schwartzHermiteBasis1D_apply]

/-- Each Schwartz seminorm of the continuum DM/Hermite basis grows polynomially
in the flattened basis index. -/
private theorem continuum_basis_seminorm_growth (d : ℕ) (k l : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ s : ℕ, ∀ n,
      SchwartzMap.seminorm ℝ k l
        (DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 1)) n) ≤
          C * (1 + (n : ℝ)) ^ s := by
  simpa [continuumTestFunction_dyninMityagin] using
    (DyninMityaginSpace.basis_growth
      (E := ContinuumTestFunction (d + 1))
      (i := ((k, l) : ℕ × ℕ)))

omit [NeZero N] in
/-- The initial coordinates of the centered physical position of a snoc'd lattice
site agree with the centered physical position of the initial lattice coordinates. -/
private theorem euclideanInit_physicalPosition_snoc (d : ℕ) (a : ℝ)
    (xs : FinLatticeSites (d + 1) N) (z : ZMod N) :
    euclideanInit (d + 1)
      (physicalPosition (d := d + 2) (N := N) a (Fin.snoc xs z)) =
        physicalPosition (d := d + 1) (N := N) a xs := by
  apply (WithLp.equiv 2 _).injective
  simp [euclideanInit, physicalPosition, Fin.snoc_castSucc]

omit [NeZero N] in
/-- The last coordinate of the centered physical position of a snoc'd lattice
site is the centered real coordinate of the appended lattice point. -/
private theorem physicalPosition_snoc_last (d : ℕ) (a : ℝ)
    (xs : FinLatticeSites (d + 1) N) (z : ZMod N) :
    physicalPosition (d := d + 2) (N := N) a (Fin.snoc xs z) (Fin.last (d + 1)) =
      a * (signedVal N z : ℝ) := by
  simp [physicalPosition, Fin.snoc_last]

omit [NeZero N] in
/-- Evaluating a continuum DM basis vector on a snoc'd lattice site factors
into the lower-dimensional basis evaluation and a 1D Hermite factor. -/
private theorem evalAtSite_basis_snoc (d : ℕ) (a : ℝ)
    (n : ℕ) (xs : FinLatticeSites (d + 1) N) (z : ZMod N) :
    evalAtSite (d := d + 2) (N := N) a (DyninMityaginSpace.basis n) (Fin.snoc xs z) =
      evalAtSite (d := d + 1) (N := N) a
        (DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 1)) (Nat.unpair n).1) xs *
      schwartzHermiteBasis1D (Nat.unpair n).2 (a * (signedVal N z : ℝ)) := by
  rw [evalAtSite]
  rw [continuum_basis_apply_eq_hermite]
  rw [hermiteFunctionNd_unpair]
  rw [euclideanInit_physicalPosition_snoc (d := d) (N := N) (a := a) xs z,
    physicalPosition_snoc_last (d := d) (N := N) (a := a) xs z]
  rw [evalAtSite, continuum_basis_apply_eq_hermite, schwartzHermiteBasis1D_apply]

omit [NeZero N] in
/-- The discretized test field of a continuum DM basis vector inherits the same
snoc factorization, with the extra `a` coming from the Riemann-sum weight. -/
private theorem latticeTestField_basis_snoc (d : ℕ) (a : ℝ)
    (n : ℕ) (xs : FinLatticeSites (d + 1) N) (z : ZMod N) :
    latticeTestField (d := d + 2) (N := N) a (DyninMityaginSpace.basis n) (Fin.snoc xs z) =
      a *
        latticeTestField (d := d + 1) (N := N) a
          (DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 1)) (Nat.unpair n).1) xs *
        schwartzHermiteBasis1D (Nat.unpair n).2 (a * (signedVal N z : ℝ)) := by
  rw [latticeTestField, evalAtSite_basis_snoc, latticeTestField]
  ring

/-- Split a sum over `(ZMod N)^(d+1)` into the initial coordinates and the last
coordinate. -/
private theorem sum_finLatticeSites_snoc {α : Type*} [AddCommMonoid α]
    (d : ℕ) (F : FinLatticeSites (d + 1) N → α) :
    ∑ x : FinLatticeSites (d + 1) N, F x =
      ∑ xs : FinLatticeSites d N, ∑ z : ZMod N, F (Fin.snoc xs z) := by
  let e : FinLatticeSites (d + 1) N ≃ FinLatticeSites d N × ZMod N :=
    { toFun := fun x => (fun i => x (Fin.castSucc i), x (Fin.last d))
      invFun := fun p => Fin.snoc p.1 p.2
      left_inv := by
        intro x
        funext i
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last]
        · intro j
          simp [Fin.snoc_castSucc]
      right_inv := by
        intro p
        cases p
        simp [Fin.snoc_castSucc, Fin.snoc_last] }
  calc
    ∑ x : FinLatticeSites (d + 1) N, F x
      = ∑ p : FinLatticeSites d N × ZMod N, F (Fin.snoc p.1 p.2) := by
          exact Fintype.sum_equiv e
            (fun x : FinLatticeSites (d + 1) N => F x)
            (fun p : FinLatticeSites d N × ZMod N => F (Fin.snoc p.1 p.2))
            (fun x => by
              simpa [e] using congrArg F (e.left_inv x).symm)
    _ = ∑ xs : FinLatticeSites d N, ∑ z : ZMod N, F (Fin.snoc xs z) := by
          rw [Fintype.sum_prod_type]

/-- Recursive decomposition of product DFT coefficients by peeling off the last
coordinate. -/
private theorem latticeFourierProductCoeff_snoc (d : ℕ)
    (f : FinLatticeSites (d + 1) N → ℝ) (m : Fin d → Fin N) (mLast : Fin N) :
    latticeFourierProductCoeff N (d + 1) f (Fin.snoc m mLast) =
      ∑ z : ZMod N,
        latticeFourierProductCoeff N d (fun xs => f (Fin.snoc xs z)) m *
          latticeFourierBasisFun N mLast z := by
  unfold latticeFourierProductCoeff
  rw [sum_finLatticeSites_snoc (N := N) d
    (F := fun x : FinLatticeSites (d + 1) N =>
      f x * latticeFourierProductBasisFun N (d + 1) (Fin.snoc m mLast) x)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro z hz
  calc
    ∑ xs : FinLatticeSites d N,
        f (Fin.snoc xs z) *
          latticeFourierProductBasisFun N (d + 1) (Fin.snoc m mLast) (Fin.snoc xs z)
      = ∑ xs : FinLatticeSites d N,
          (f (Fin.snoc xs z) * latticeFourierProductBasisFun N d m xs) *
            latticeFourierBasisFun N mLast z := by
              refine Finset.sum_congr rfl ?_
              intro xs hxs
              simp [latticeFourierProductBasisFun, Fin.prod_univ_castSucc,
                Fin.snoc_castSucc, Fin.snoc_last]
              ring
    _ = latticeFourierProductCoeff N d (fun xs => f (Fin.snoc xs z)) m *
          latticeFourierBasisFun N mLast z := by
            rw [latticeFourierProductCoeff, Finset.sum_mul]

/-- Product DFT coefficients of discretized continuum basis vectors factor into
the lower-dimensional product DFT coefficient and a centered 1D Hermite sum. -/
private theorem latticeFourierProductCoeff_basis_snoc (d : ℕ) (a : ℝ)
    (n : ℕ) (m : Fin (d + 1) → Fin N) (mLast : Fin N) :
    latticeFourierProductCoeff N (d + 2)
      (latticeTestField (d := d + 2) (N := N) a (DyninMityaginSpace.basis n))
      (Fin.snoc m mLast) =
      latticeFourierProductCoeff N (d + 1)
        (latticeTestField (d := d + 1) (N := N) a
          (DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 1)) (Nat.unpair n).1)) m *
      ∑ z : ZMod N,
        a * schwartzHermiteBasis1D (Nat.unpair n).2 (a * (signedVal N z : ℝ)) *
          latticeFourierBasisFun N mLast z := by
  rw [latticeFourierProductCoeff_snoc]
  set c :=
    latticeFourierProductCoeff N (d + 1)
      (latticeTestField (d := d + 1) (N := N) a
        (DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 1)) (Nat.unpair n).1)) m
  have hslice :
      ∀ z : ZMod N,
        latticeFourierProductCoeff N (d + 1)
          (fun xs =>
            latticeTestField (d := d + 2) (N := N) a
              (DyninMityaginSpace.basis n) (Fin.snoc xs z)) m =
          c * (a * schwartzHermiteBasis1D (Nat.unpair n).2 (a * (signedVal N z : ℝ))) := by
    intro z
    dsimp [c]
    unfold latticeFourierProductCoeff
    calc
      ∑ xs : FinLatticeSites (d + 1) N,
          latticeTestField (d := d + 2) (N := N) a (DyninMityaginSpace.basis n) (Fin.snoc xs z) *
            latticeFourierProductBasisFun N (d + 1) m xs
        = ∑ xs : FinLatticeSites (d + 1) N,
            (a *
                latticeTestField (d := d + 1) (N := N) a
                  (DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 1))
                    (Nat.unpair n).1) xs *
                schwartzHermiteBasis1D (Nat.unpair n).2 (a * (signedVal N z : ℝ))) *
              latticeFourierProductBasisFun N (d + 1) m xs := by
                refine Finset.sum_congr rfl ?_
                intro xs hxs
                rw [latticeTestField_basis_snoc (d := d) (N := N) (a := a) (n := n) xs z]
      _ =
          ∑ xs : FinLatticeSites (d + 1) N,
            (a * schwartzHermiteBasis1D (Nat.unpair n).2 (a * (signedVal N z : ℝ))) *
              (latticeTestField (d := d + 1) (N := N) a
                (DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 1))
                  (Nat.unpair n).1) xs *
                latticeFourierProductBasisFun N (d + 1) m xs) := by
                refine Finset.sum_congr rfl ?_
                intro xs hxs
                ring
      _ =
          (a * schwartzHermiteBasis1D (Nat.unpair n).2 (a * (signedVal N z : ℝ))) *
            ∑ xs : FinLatticeSites (d + 1) N,
              latticeTestField (d := d + 1) (N := N) a
                (DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 1))
                  (Nat.unpair n).1) xs *
              latticeFourierProductBasisFun N (d + 1) m xs := by
                rw [← Finset.mul_sum]
      _ = c * (a * schwartzHermiteBasis1D (Nat.unpair n).2 (a * (signedVal N z : ℝ))) := by
            simp [c, latticeFourierProductCoeff, mul_comm, mul_assoc]
  simp_rw [hslice]
  calc
    ∑ z : ZMod N,
        (c * (a * schwartzHermiteBasis1D (Nat.unpair n).2 (a * (signedVal N z : ℝ)))) *
          latticeFourierBasisFun N mLast z
      = ∑ z : ZMod N,
          c * (a * schwartzHermiteBasis1D (Nat.unpair n).2 (a * (signedVal N z : ℝ)) *
            latticeFourierBasisFun N mLast z) := by
              refine Finset.sum_congr rfl ?_
              intro z hz
              ring
    _ = c * ∑ z : ZMod N,
          a * schwartzHermiteBasis1D (Nat.unpair n).2 (a * (signedVal N z : ℝ)) *
            latticeFourierBasisFun N mLast z := by
              symm
              rw [Finset.mul_sum]
    _ = _ := by
      simp [c]

/-- Split a sum over `(Fin (d+2) → Fin N)` into the initial coordinates and the
last Fourier mode. -/
private theorem sum_finModes_snoc {N : ℕ} {α : Type*} [AddCommMonoid α]
    (d : ℕ) (F : (Fin (d + 2) → Fin N) → α) :
    ∑ m : (Fin (d + 2) → Fin N), F m =
      ∑ ms : (Fin (d + 1) → Fin N), ∑ mLast : Fin N, F (Fin.snoc ms mLast) := by
  let e : (Fin (d + 2) → Fin N) ≃ (Fin (d + 1) → Fin N) × Fin N :=
    { toFun := fun x => (fun i => x (Fin.castSucc i), x (Fin.last (d + 1)))
      invFun := fun p => Fin.snoc p.1 p.2
      left_inv := by
        intro x
        funext i
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last]
        · intro j
          simp [Fin.snoc_castSucc]
      right_inv := by
        intro p
        cases p
        simp [Fin.snoc_castSucc, Fin.snoc_last] }
  calc
    ∑ m : (Fin (d + 2) → Fin N), F m
      = ∑ p : (Fin (d + 1) → Fin N) × Fin N, F (Fin.snoc p.1 p.2) := by
          exact Fintype.sum_equiv e
            (fun m : (Fin (d + 2) → Fin N) => F m)
            (fun p : (Fin (d + 1) → Fin N) × Fin N => F (Fin.snoc p.1 p.2))
            (fun m => by
              simpa [e] using congrArg F (e.left_inv m).symm)
    _ = ∑ ms : (Fin (d + 1) → Fin N), ∑ mLast : Fin N, F (Fin.snoc ms mLast) := by
          rw [Fintype.sum_prod_type]

/-- The squared norm of a product DFT basis vector factors under `Fin.snoc`. -/
private theorem latticeFourierProductNormSq_snoc (d : ℕ)
    (m : Fin (d + 1) → Fin N) (mLast : Fin N) :
    latticeFourierProductNormSq N (d + 2) (Fin.snoc m mLast) =
      latticeFourierProductNormSq N (d + 1) m * latticeFourierNormSq N mLast := by
  simp [latticeFourierProductNormSq, Fin.prod_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last]

/-- The lattice eigenvalue sum splits into the initial coordinates and the last
Fourier mode under `Fin.snoc`. -/
private def snocFourierMode {N : ℕ} (d : ℕ)
    (m : Fin (d + 1) → Fin N) (mLast : Fin N) :
    Fin (d + 2) → Fin N :=
  Fin.snoc m mLast

private theorem latticeEigenvalueSum_snoc {N : ℕ} (d : ℕ) (a : ℝ)
    (m : Fin (d + 1) → Fin N) (mLast : Fin N) :
    (∑ k : Fin (d + 2),
        latticeEigenvalue1d N a
          ((snocFourierMode (N := N) d m mLast k : Fin N) : ℕ)) =
      (∑ k : Fin (d + 1), latticeEigenvalue1d N a (m k)) +
        latticeEigenvalue1d N a mLast := by
  rw [Fin.sum_univ_castSucc]
  simp [snocFourierMode]

/-- The `(d+1)`-dimensional product DFT coefficient of the lower-dimensional
Hermite basis factor appearing in the `Fin.snoc` recursion. -/
private noncomputable def latticeBasisPrefixCoeff (d : ℕ) (a : ℝ) (n : ℕ)
    (m : Fin (d + 1) → Fin N) : ℝ := by
  letI : Fact (0 < d + 1) := ⟨by positivity⟩
  exact latticeFourierProductCoeff N (d + 1)
    (latticeTestField (d := d + 1) (N := N) a
      (DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 1)) n)) m

/-- The 1D Hermite slice DFT coefficient arising from the `Fin.snoc` recursion. -/
private def latticeHermiteSliceCoeff (a : ℝ) (n : ℕ) (m : Fin N) : ℝ :=
  ∑ z : ZMod N,
    a * schwartzHermiteBasis1D n (a * (signedVal N z : ℝ)) *
      latticeFourierBasisFun N m z

omit d in
/-- The periodized Hermite function with period `N * a` agrees at raw and centered
lattice coordinates, because the two coordinates differ by an integer multiple
of the period. -/
private theorem periodizeFun_hermite_raw_eq_centered
    (a : ℝ) [Fact (0 < (N : ℝ) * a)]
    (n : ℕ) (z : ZMod N) :
    periodizeFun ((N : ℝ) * a) (schwartzHermiteBasis1D n) (a * (ZMod.val z : ℝ)) =
      periodizeFun ((N : ℝ) * a) (schwartzHermiteBasis1D n)
        (a * (signedVal N z : ℝ)) := by
  have hper := periodizeFun_periodic ((N : ℝ) * a) (schwartzHermiteBasis1D n)
  by_cases hz : (ZMod.val z : ℤ) ≤ (N : ℤ) / 2
  · have hsigned : (signedVal N z : ℝ) = (ZMod.val z : ℝ) := by
      unfold signedVal
      rw [if_pos hz]
      norm_num
    rw [hsigned]
  · have hsigned :
        a * (signedVal N z : ℝ) + ((N : ℝ) * a) =
          a * (ZMod.val z : ℝ) := by
      have hsigned_int : signedVal N z = (ZMod.val z : ℤ) - (N : ℤ) := by
        unfold signedVal
        rw [if_neg hz]
      rw [hsigned_int]
      push_cast
      ring
    simpa [hsigned, add_assoc, add_comm, add_left_comm] using
      hper (a * (signedVal N z : ℝ))

omit d in
/-- Sampling the large-period periodization of a Hermite slice on the circle of
length `N * a` produces the centered lattice sample weighted by the exact
Riemann-sum factor `a`. -/
private theorem circleRestriction_scaledPeriodizedHermite_eq
    (a : ℝ) [Fact (0 < (N : ℝ) * a)] (ha : 0 < a)
    (n : ℕ) (z : ZMod N) :
    circleRestriction ((N : ℝ) * a) N
      ((Real.sqrt a) • periodizeCLM ((N : ℝ) * a) (schwartzHermiteBasis1D n)) z =
        a * periodizeFun ((N : ℝ) * a) (schwartzHermiteBasis1D n)
          (a * (signedVal N z : ℝ)) := by
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hspacing : circleSpacing ((N : ℝ) * a) N = a := by
    rw [circleSpacing_eq]
    field_simp [hN_ne]
  have hpoint : circlePoint ((N : ℝ) * a) N z = a * (ZMod.val z : ℝ) := by
    rw [circlePoint]
    field_simp [hN_ne]
  rw [circleRestriction_apply, hspacing, hpoint]
  change Real.sqrt a *
      (Real.sqrt a * (periodizeCLM ((N : ℝ) * a) (schwartzHermiteBasis1D n)).toFun
        (a * (ZMod.val z : ℝ))) =
    a * periodizeFun ((N : ℝ) * a) (schwartzHermiteBasis1D n)
      (a * (signedVal N z : ℝ))
  rw [periodizeCLM_apply]
  calc
    Real.sqrt a *
        (Real.sqrt a * periodizeFun ((N : ℝ) * a) (schwartzHermiteBasis1D n)
          (a * (ZMod.val z : ℝ))) =
      Real.sqrt a ^ 2 * periodizeFun ((N : ℝ) * a) (schwartzHermiteBasis1D n)
        (a * (ZMod.val z : ℝ)) := by
          ring
    _ = a * periodizeFun ((N : ℝ) * a) (schwartzHermiteBasis1D n)
        (a * (ZMod.val z : ℝ)) := by
          rw [Real.sq_sqrt ha.le]
    _ = a * periodizeFun ((N : ℝ) * a) (schwartzHermiteBasis1D n)
          (a * (signedVal N z : ℝ)) := by
            rw [periodizeFun_hermite_raw_eq_centered (N := N) (a := a) (n := n) (z := z)]

omit d in
/-- The wrap-around defect between the centered nonperiodic Hermite slice
coefficient and the exact large-period circle DFT coefficient. -/
private def latticeHermiteSlicePeriodizationDefect
    (a : ℝ) [Fact (0 < (N : ℝ) * a)] (n : ℕ) (m : Fin N) : ℝ :=
  ∑ z : ZMod N,
    a *
      (periodizeFun ((N : ℝ) * a) (schwartzHermiteBasis1D n)
          (a * (signedVal N z : ℝ)) -
        schwartzHermiteBasis1D n (a * (signedVal N z : ℝ))) *
      latticeFourierBasisFun N m z

omit d in
/-- The centered Hermite slice coefficient is exactly the large-period circle
DFT coefficient of the scaled periodized Hermite function, up to the explicit
wrap-around defect coming from the nonzero periodization images. -/
private theorem latticeDFTCoeff_periodizedHermite_eq_slice_add_defect
    (a : ℝ) [Fact (0 < (N : ℝ) * a)] (ha : 0 < a)
    (n : ℕ) (m : Fin N) :
    latticeDFTCoeff1d ((N : ℝ) * a) N
      ((Real.sqrt a) • periodizeCLM ((N : ℝ) * a) (schwartzHermiteBasis1D n)) m =
        latticeHermiteSliceCoeff (N := N) a n m +
          latticeHermiteSlicePeriodizationDefect (N := N) a n m := by
  rw [latticeDFTCoeff1d, if_pos m.isLt]
  calc
    ∑ z : ZMod N,
        circleRestriction ((N : ℝ) * a) N
          ((Real.sqrt a) • periodizeCLM ((N : ℝ) * a) (schwartzHermiteBasis1D n)) z *
          latticeFourierBasisFun N m z
      = ∑ z : ZMod N,
          a * periodizeFun ((N : ℝ) * a) (schwartzHermiteBasis1D n)
            (a * (signedVal N z : ℝ)) *
            latticeFourierBasisFun N m z := by
              apply Finset.sum_congr rfl
              intro z hz
              rw [circleRestriction_scaledPeriodizedHermite_eq
                (N := N) (a := a) (ha := ha) (n := n) (z := z)]
    _ = ∑ z : ZMod N,
          ((a * schwartzHermiteBasis1D n (a * (signedVal N z : ℝ)) *
              latticeFourierBasisFun N m z) +
            (a *
                (periodizeFun ((N : ℝ) * a) (schwartzHermiteBasis1D n)
                    (a * (signedVal N z : ℝ)) -
                  schwartzHermiteBasis1D n (a * (signedVal N z : ℝ))) *
              latticeFourierBasisFun N m z)) := by
                apply Finset.sum_congr rfl
                intro z hz
                ring
    _ = (∑ z : ZMod N,
          a * schwartzHermiteBasis1D n (a * (signedVal N z : ℝ)) *
            latticeFourierBasisFun N m z) +
        (∑ z : ZMod N,
          a *
              (periodizeFun ((N : ℝ) * a) (schwartzHermiteBasis1D n)
                  (a * (signedVal N z : ℝ)) -
                schwartzHermiteBasis1D n (a * (signedVal N z : ℝ))) *
            latticeFourierBasisFun N m z) := by
                rw [Finset.sum_add_distrib]
    _ = latticeHermiteSliceCoeff (N := N) a n m +
          latticeHermiteSlicePeriodizationDefect (N := N) a n m := by
            rfl

omit [NeZero N] in
/-- The one-dimensional discretized basis field is the Hermite basis evaluated
at the centered physical coordinate. -/
private theorem latticeTestField_basis_one_eq_slice
    (a : ℝ) (n : ℕ) (z : ZMod N) (xs : FinLatticeSites 0 N) :
    latticeTestField (d := 1) (N := N) a
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) n)
      (Fin.cons z xs) =
    a * schwartzHermiteBasis1D n (a * (signedVal N z : ℝ)) := by
  rw [latticeTestField, evalAtSite, continuum_basis_apply_eq_hermite1D]
  simp [physicalPosition]

/-- For the last remaining peeled coordinate, the prefix coefficient is exactly
the 1D Hermite slice coefficient. -/
private theorem latticeBasisPrefixCoeff_zero_eq_sliceCoeff
    (a : ℝ) (n : ℕ) (m : Fin 1 → Fin N) :
    latticeBasisPrefixCoeff (N := N) 0 a n m =
      latticeHermiteSliceCoeff (N := N) a n (m 0) := by
  change latticeFourierProductCoeff N 1
    (latticeTestField (d := 1) (N := N) a
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) n)) m =
    latticeHermiteSliceCoeff (N := N) a n (m 0)
  have hm : m = Fin.cons (m 0) (fun i : Fin 0 => nomatch i) := by
    funext i
    fin_cases i
    rfl
  rw [hm, latticeFourierProductCoeff_succ (N := N) (d := 0)]
  unfold latticeHermiteSliceCoeff
  refine Finset.sum_congr rfl ?_
  intro z hz
  simp [latticeFourierProductCoeff, latticeFourierProductBasisFun]
  left
  simpa using
    (latticeTestField_basis_one_eq_slice
      (N := N) (a := a) (n := n) (z := z) (xs := default))

/-- The 1D lattice Green bilinear form for Hermite slices with an external
mass shift coming from the already-peeled coordinates. -/
private def latticeHermiteSliceGreenTerm (a massShift : ℝ) (i j : ℕ) (m : Fin N) : ℝ :=
  latticeHermiteSliceCoeff (N := N) a i m *
    latticeHermiteSliceCoeff (N := N) a j m /
    ((massShift + latticeEigenvalue1d N a m) * latticeFourierNormSq N m)

/-- The 1D lattice Green bilinear form for Hermite slices with an external
mass shift coming from the already-peeled coordinates. -/
private def latticeHermiteSliceBilinear (a massShift : ℝ) (i j : ℕ) : ℝ :=
  ∑ m : Fin N,
    latticeHermiteSliceGreenTerm (N := N) a massShift i j m

/-- The `(d+2)`-dimensional continuum Hermite basis vector, packaged so later
recursive statements do not need to normalize the positive-dimension instance
in their theorem statement. -/
private noncomputable def continuumBasisSuccSucc (d : ℕ) (n : ℕ) :
    ContinuumTestFunction (d + 2) := by
  letI : Fact (0 < d + 2) := ⟨by positivity⟩
  exact DyninMityaginSpace.basis n

/-- The peeled `Fin.snoc` spectral sum: an outer `(d+1)`-dimensional DFT factor
times an inner 1D Hermite-slice Green form. -/
private def latticeBasisPrefixGreenFactor (d : ℕ) (a : ℝ) (i j : ℕ)
    (m : Fin (d + 1) → Fin N) : ℝ :=
  latticeBasisPrefixCoeff (N := N) d a (Nat.unpair i).1 m *
    latticeBasisPrefixCoeff (N := N) d a (Nat.unpair j).1 m /
    latticeFourierProductNormSq N (d + 1) m

/-- In the physically relevant two-dimensional case, the peeled prefix factor is
itself a 1D Hermite-slice spectral factor. -/
private theorem latticeBasisPrefixGreenFactor_zero_eq_slice
    (a : ℝ) (i j : ℕ) (m : Fin 1 → Fin N) :
    latticeBasisPrefixGreenFactor (N := N) 0 a i j m =
      latticeHermiteSliceCoeff (N := N) a (Nat.unpair i).1 (m 0) *
        latticeHermiteSliceCoeff (N := N) a (Nat.unpair j).1 (m 0) /
        latticeFourierNormSq N (m 0) := by
  rw [latticeBasisPrefixGreenFactor,
    latticeBasisPrefixCoeff_zero_eq_sliceCoeff,
    latticeBasisPrefixCoeff_zero_eq_sliceCoeff]
  simp [latticeFourierProductNormSq]

/-- The full `(d+2)`-dimensional basis-pair spectral term, packaged so that
recursive `Fin.snoc` reductions can be stated without expanding the whole sum. -/
private def latticeBasisSpectralTermSuccSucc (d : ℕ) (a mass : ℝ) (i j : ℕ)
    (m : Fin (d + 2) → Fin N) : ℝ :=
  latticeFourierProductCoeff N (d + 2)
      (latticeTestField (d := d + 2) (N := N) a (continuumBasisSuccSucc d i)) m *
    latticeFourierProductCoeff N (d + 2)
      (latticeTestField (d := d + 2) (N := N) a (continuumBasisSuccSucc d j)) m /
    (((∑ k : Fin (d + 2), latticeEigenvalue1d N a (m k)) + mass ^ 2) *
      latticeFourierProductNormSq N (d + 2) m)

/-- The peeled `Fin.snoc` spectral sum: an outer `(d+1)`-dimensional DFT factor
times an inner 1D Hermite-slice Green form. -/
private def latticeBasisIteratedSliceSum (d : ℕ) (a mass : ℝ) (i j : ℕ) : ℝ :=
  ∑ m : Fin (d + 1) → Fin N,
    latticeBasisPrefixGreenFactor (N := N) d a i j m *
      latticeHermiteSliceBilinear (N := N) a
        ((∑ k : Fin (d + 1), latticeEigenvalue1d N a (m k)) + mass ^ 2)
        (Nat.unpair i).2 (Nat.unpair j).2

/-- The fully peeled 2D spectral term: one Hermite-slice factor for the first
coordinate, then the 1D Green term for the second coordinate. -/
private def latticeHermiteDoubleGreenTerm (a mass : ℝ) (i j : ℕ)
    (m0 m1 : Fin N) : ℝ :=
  latticeHermiteSliceCoeff (N := N) a (Nat.unpair i).1 m0 *
    latticeHermiteSliceCoeff (N := N) a (Nat.unpair j).1 m0 /
    latticeFourierNormSq N m0 *
    latticeHermiteSliceGreenTerm (N := N) a
      (latticeEigenvalue1d N a m0 + mass ^ 2)
      (Nat.unpair i).2 (Nat.unpair j).2 m1

/-- Repackage `latticeFourierProductCoeff_basis_snoc` using the prefix/slice
helper definitions introduced above. This is the exact coefficient-level
reduction needed for the future one-dimensional slice analysis. -/
private theorem latticeFourierProductCoeff_basis_snoc_eq_prefix_slice
    (d : ℕ) (a : ℝ) (n : ℕ) (m : Fin (d + 1) → Fin N) (mLast : Fin N) :
    latticeFourierProductCoeff N (d + 2)
      (latticeTestField (d := d + 2) (N := N) a (continuumBasisSuccSucc d n))
      (Fin.snoc m mLast) =
      latticeBasisPrefixCoeff (N := N) d a (Nat.unpair n).1 m *
        latticeHermiteSliceCoeff (N := N) a (Nat.unpair n).2 mLast := by
  letI : Fact (0 < d + 2) := ⟨by positivity⟩
  change latticeFourierProductCoeff N (d + 2)
    (latticeTestField (d := d + 2) (N := N) a
      (DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 2)) n))
    (Fin.snoc m mLast) =
    latticeBasisPrefixCoeff (N := N) d a (Nat.unpair n).1 m *
      latticeHermiteSliceCoeff (N := N) a (Nat.unpair n).2 mLast
  simpa [latticeBasisPrefixCoeff, latticeHermiteSliceCoeff] using
    (latticeFourierProductCoeff_basis_snoc (N := N) (d := d) (a := a)
      (n := n) (m := m) (mLast := mLast))

/-- The full `(d+2)`-dimensional spectral term factors under `Fin.snoc` into a
lower-dimensional prefix Green factor and a single 1D Hermite-slice Green term. -/
private theorem latticeBasisSpectralTermSuccSucc_snoc
    (d : ℕ) (a mass : ℝ) (hmass : 0 < mass) (i j : ℕ)
    (m : Fin (d + 1) → Fin N) (mLast : Fin N) :
    latticeBasisSpectralTermSuccSucc (N := N) d a mass i j (Fin.snoc m mLast) =
      latticeBasisPrefixGreenFactor (N := N) d a i j m *
        latticeHermiteSliceGreenTerm (N := N) a
          ((∑ k : Fin (d + 1), latticeEigenvalue1d N a (m k)) + mass ^ 2)
          (Nat.unpair i).2 (Nat.unpair j).2 mLast := by
  have hi :=
    latticeFourierProductCoeff_basis_snoc_eq_prefix_slice
      (N := N) (d := d) (a := a) (n := i) (m := m) (mLast := mLast)
  have hj :=
    latticeFourierProductCoeff_basis_snoc_eq_prefix_slice
      (N := N) (d := d) (a := a) (n := j) (m := m) (mLast := mLast)
  have hnormPrefix :
      latticeFourierProductNormSq N (d + 1) m ≠ 0 := by
    exact ne_of_gt (latticeFourierProductNormSq_pos (N := N) (d + 1) m)
  have hnormLast : latticeFourierNormSq N mLast ≠ 0 := by
    exact ne_of_gt (latticeFourierNormSq_pos N mLast mLast.isLt)
  have hmassShift_pos :
      0 < ((∑ k : Fin (d + 1), latticeEigenvalue1d N a (m k)) + mass ^ 2) +
        latticeEigenvalue1d N a mLast := by
    have heig_nonneg :
        0 ≤ ∑ k : Fin (d + 1), latticeEigenvalue1d N a (m k) := by
      exact Finset.sum_nonneg fun k _ => latticeEigenvalue1d_nonneg N a (m k)
    linarith [heig_nonneg, sq_pos_of_pos hmass, latticeEigenvalue1d_nonneg N a mLast]
  have heigSum :
      (∑ k : Fin (d + 2),
          latticeEigenvalue1d N a
            ((snocFourierMode (N := N) d m mLast k : Fin N) : ℕ)) =
        (∑ k : Fin (d + 1), latticeEigenvalue1d N a (m k)) +
          latticeEigenvalue1d N a mLast :=
    latticeEigenvalueSum_snoc (N := N) (d := d) (a := a) m mLast
  simp [snocFourierMode] at heigSum
  unfold latticeBasisSpectralTermSuccSucc latticeBasisPrefixGreenFactor latticeHermiteSliceGreenTerm
  rw [hi, hj, heigSum,
    latticeFourierProductNormSq_snoc (N := N) (d := d) m mLast]
  set X : ℝ :=
    latticeBasisPrefixCoeff (N := N) d a (Nat.unpair i).1 m *
      latticeHermiteSliceCoeff (N := N) a (Nat.unpair i).2 mLast *
      latticeBasisPrefixCoeff (N := N) d a (Nat.unpair j).1 m *
      latticeHermiteSliceCoeff (N := N) a (Nat.unpair j).2 mLast
  set D : ℝ :=
    (∑ k : Fin (d + 1), latticeEigenvalue1d N a (m k)) + mass ^ 2 +
      latticeEigenvalue1d N a mLast
  have hD_ne : D ≠ 0 := ne_of_gt (by simpa [D, add_left_comm, add_comm] using hmassShift_pos)
  have hXexpr :
      latticeBasisPrefixCoeff (N := N) d a (Nat.unpair i).1 m *
          latticeHermiteSliceCoeff (N := N) a (Nat.unpair i).2 mLast *
          (latticeBasisPrefixCoeff (N := N) d a (Nat.unpair j).1 m *
            latticeHermiteSliceCoeff (N := N) a (Nat.unpair j).2 mLast) =
        X := by
    simp [X]
    ring
  have hDexpr :
      (∑ k : Fin (d + 1), latticeEigenvalue1d N a (m k)) +
          latticeEigenvalue1d N a mLast + mass ^ 2 = D := by
    simp [D, add_left_comm, add_comm]
  rw [hXexpr, hDexpr]
  field_simp [X, D, hnormPrefix, hnormLast, hD_ne]
  simp [X, mul_assoc, mul_left_comm]

/-- After peeling one coordinate by `Fin.snoc`, the `(d+2)`-dimensional basis-pair
spectral sum becomes an outer `(d+1)`-dimensional Green factor times an inner
1D Hermite-slice bilinear form. -/
private theorem latticeGreenBilinear_basis_eq_iterated_slice_sum
    (d : ℕ) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (i j : ℕ) :
    latticeGreenBilinear (d + 2) N a mass
      (continuumBasisSuccSucc d i)
      (continuumBasisSuccSucc d j) =
      latticeBasisIteratedSliceSum (N := N) d a mass i j := by
  letI : Fact (0 < d + 2) := ⟨by positivity⟩
  change latticeGreenBilinear (d + 2) N a mass
    (DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 2)) i)
    (DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 2)) j) =
    latticeBasisIteratedSliceSum (N := N) d a mass i j
  rw [latticeGreenBilinear_basis_eq_product_dft_spectral_sum
    (d := d + 2) (N := N) (a := a) (mass := mass) ha hmass i j]
  change
    ∑ mFull : (Fin (d + 2) → Fin N),
      latticeBasisSpectralTermSuccSucc (N := N) d a mass i j mFull =
    latticeBasisIteratedSliceSum (N := N) d a mass i j
  rw [sum_finModes_snoc (N := N) (d := d)
    (F := latticeBasisSpectralTermSuccSucc (N := N) d a mass i j)]
  unfold latticeBasisIteratedSliceSum latticeHermiteSliceBilinear
  refine Finset.sum_congr rfl ?_
  intro m hm
  simp_rw [latticeBasisSpectralTermSuccSucc_snoc
    (N := N) (d := d) (a := a) (mass := mass) (hmass := hmass) (i := i) (j := j) (m := m)]
  rw [← Finset.mul_sum]

/-- Concrete specialization of the recursive spectral reduction to the physical
two-dimensional continuum limit. This is the exact `P(phi)_2` basis-pair
spectral sum written as a one-dimensional outer mode sum with Hermite slices. -/
private theorem latticeGreenBilinear_basis_eq_iterated_slice_sum_2d
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (i j : ℕ) :
    latticeGreenBilinear 2 N a mass
      (continuumBasisSuccSucc 0 i)
      (continuumBasisSuccSucc 0 j) =
      latticeBasisIteratedSliceSum (N := N) 0 a mass i j := by
  simpa using
    latticeGreenBilinear_basis_eq_iterated_slice_sum
      (N := N) (d := 0) (a := a) (mass := mass) ha hmass i j

omit [NeZero N] in
/-- A sum over one lattice Fourier mode is just a sum over `Fin N`, via the
unique decomposition of functions `Fin 1 → Fin N`. -/
private theorem sum_finModes_one {α : Type*} [AddCommMonoid α]
    (F : (Fin 1 → Fin N) → α) :
    ∑ m : (Fin 1 → Fin N), F m =
      ∑ m0 : Fin N, F (Fin.cons m0 (fun i : Fin 0 => nomatch i)) := by
  let e : (Fin 1 → Fin N) ≃ Fin N :=
    { toFun := fun m => m 0
      invFun := fun m0 => Fin.cons m0 (fun i : Fin 0 => nomatch i)
      left_inv := by
        intro m
        funext i
        fin_cases i
        rfl
      right_inv := by
        intro m0
        rfl }
  calc
    ∑ m : (Fin 1 → Fin N), F m
      = ∑ m0 : Fin N, F (Fin.cons m0 (fun i : Fin 0 => nomatch i)) := by
          exact Fintype.sum_equiv e
            (fun m : (Fin 1 → Fin N) => F m)
            (fun m0 : Fin N => F (Fin.cons m0 (fun i : Fin 0 => nomatch i)))
            (fun m => by
              simpa [e] using congrArg F (e.left_inv m).symm)

/-- The one-dimensional basis-pair lattice Green form is exactly the
Hermite-slice bilinear form with `massShift = mass^2`. -/
private theorem latticeGreenBilinear_basis_eq_sliceBilinear_1d
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (i j : ℕ) :
    latticeGreenBilinear 1 N a mass
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i)
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) j) =
      latticeHermiteSliceBilinear (N := N) a (mass ^ 2) i j := by
  letI : Fact (0 < 1) := ⟨by positivity⟩
  rw [latticeGreenBilinear_basis_eq_product_dft_spectral_sum
    (d := 1) (N := N) (a := a) (mass := mass) ha hmass i j]
  rw [sum_finModes_one (N := N)
    (F := fun m : (Fin 1 → Fin N) =>
      latticeFourierProductCoeff N 1
          (latticeTestField (d := 1) (N := N) a
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i)) m *
        latticeFourierProductCoeff N 1
          (latticeTestField (d := 1) (N := N) a
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) j)) m /
        (((∑ k : Fin 1, latticeEigenvalue1d N a (m k)) + mass ^ 2) *
          latticeFourierProductNormSq N 1 m))]
  unfold latticeHermiteSliceBilinear
  refine Finset.sum_congr rfl ?_
  intro m0 hm0
  have hiCoeff :
      latticeFourierProductCoeff N 1
        (latticeTestField (d := 1) (N := N) a
          (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i))
        (Fin.cons m0 (fun i : Fin 0 => nomatch i)) =
      latticeHermiteSliceCoeff (N := N) a i m0 := by
    simpa [latticeBasisPrefixCoeff] using
      (latticeBasisPrefixCoeff_zero_eq_sliceCoeff (N := N) (a := a) (n := i)
        (m := Fin.cons m0 (fun i : Fin 0 => nomatch i)))
  have hjCoeff :
      latticeFourierProductCoeff N 1
        (latticeTestField (d := 1) (N := N) a
          (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) j))
        (Fin.cons m0 (fun i : Fin 0 => nomatch i)) =
      latticeHermiteSliceCoeff (N := N) a j m0 := by
    simpa [latticeBasisPrefixCoeff] using
      (latticeBasisPrefixCoeff_zero_eq_sliceCoeff (N := N) (a := a) (n := j)
        (m := Fin.cons m0 (fun i : Fin 0 => nomatch i)))
  simp [hiCoeff, hjCoeff, latticeFourierProductNormSq,
    latticeHermiteSliceGreenTerm, add_comm]

/-- Repackage the Hermite slice form as the one-dimensional lattice Green form
with effective mass `sqrt massShift`. -/
private theorem latticeHermiteSliceBilinear_eq_latticeGreenBilinear_1d
    (a massShift : ℝ) (ha : 0 < a) (hmassShift : 0 < massShift) (i j : ℕ) :
    latticeHermiteSliceBilinear (N := N) a massShift i j =
      latticeGreenBilinear 1 N a (Real.sqrt massShift)
        (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i)
        (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) j) := by
  have hsqrt : 0 < Real.sqrt massShift := Real.sqrt_pos.mpr hmassShift
  symm
  simpa [Real.sq_sqrt hmassShift.le] using
    (latticeGreenBilinear_basis_eq_sliceBilinear_1d (N := N)
      (a := a) (mass := Real.sqrt massShift) ha hsqrt i j)

/-- The outer peeled 2D spectral term can be viewed as a sum of one-dimensional
lattice Green forms with effective masses `sqrt (lambda_m + mass^2)`. -/
private def latticeHermiteEffectiveMassTerm (a mass : ℝ) (i j : ℕ)
    (m0 : Fin N) : ℝ :=
  latticeHermiteSliceCoeff (N := N) a (Nat.unpair i).1 m0 *
    latticeHermiteSliceCoeff (N := N) a (Nat.unpair j).1 m0 /
    latticeFourierNormSq N m0 *
    latticeGreenBilinear 1 N a
      (Real.sqrt (latticeEigenvalue1d N a m0 + mass ^ 2))
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).2)
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).2)

/-- In two dimensions, the basis Green form is an outer Fourier-mode sum whose
integrand is a first-coordinate Hermite slice factor times a one-dimensional
effective-mass lattice propagator in the second coordinate. -/
private theorem latticeGreenBilinear_basis_eq_effective_mass_sum_2d
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (i j : ℕ) :
    latticeGreenBilinear 2 N a mass
      (continuumBasisSuccSucc 0 i)
      (continuumBasisSuccSucc 0 j) =
      ∑ m0 : Fin N, latticeHermiteEffectiveMassTerm (N := N) a mass i j m0 := by
  rw [latticeGreenBilinear_basis_eq_iterated_slice_sum_2d
    (N := N) (a := a) (mass := mass) ha hmass i j]
  unfold latticeBasisIteratedSliceSum latticeHermiteEffectiveMassTerm
  rw [sum_finModes_one (N := N)
    (F := fun m : (Fin 1 → Fin N) =>
      latticeBasisPrefixGreenFactor (N := N) 0 a i j m *
        latticeHermiteSliceBilinear (N := N) a
          ((∑ k : Fin 1, latticeEigenvalue1d N a (m k)) + mass ^ 2)
          (Nat.unpair i).2 (Nat.unpair j).2)]
  refine Finset.sum_congr rfl ?_
  intro m0 hm0
  have hshift_pos : 0 < latticeEigenvalue1d N a m0 + mass ^ 2 := by
    exact add_pos_of_nonneg_of_pos
      (latticeEigenvalue1d_nonneg N a m0) (sq_pos_of_pos hmass)
  simp only [Fin.sum_univ_one]
  simp
  rw [latticeHermiteSliceBilinear_eq_latticeGreenBilinear_1d
    (N := N) (a := a)
    (massShift := latticeEigenvalue1d N a m0 + mass ^ 2)
    ha hshift_pos (Nat.unpair i).2 (Nat.unpair j).2]
  simp [latticeBasisPrefixGreenFactor_zero_eq_slice]

/-- In two dimensions, the recursive basis-pair spectral sum is an explicit
finite double sum over two one-dimensional Hermite slice mode indices. -/
private theorem latticeBasisIteratedSliceSum_zero_eq_double_sum
    (a mass : ℝ) (i j : ℕ) :
    latticeBasisIteratedSliceSum (N := N) 0 a mass i j =
      ∑ m0 : Fin N, ∑ m1 : Fin N,
        latticeHermiteDoubleGreenTerm (N := N) a mass i j m0 m1 := by
  unfold latticeBasisIteratedSliceSum
  rw [sum_finModes_one (N := N)
    (F := fun m : (Fin 1 → Fin N) =>
      latticeBasisPrefixGreenFactor (N := N) 0 a i j m *
        latticeHermiteSliceBilinear (N := N) a
          ((∑ k : Fin 1, latticeEigenvalue1d N a (m k)) + mass ^ 2)
          (Nat.unpair i).2 (Nat.unpair j).2)]
  refine Finset.sum_congr rfl ?_
  intro m0 hm0
  rw [latticeHermiteSliceBilinear, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m1 hm1
  simp [latticeHermiteDoubleGreenTerm, latticeBasisPrefixGreenFactor_zero_eq_slice]

/-- In the `P(phi)_2` case, the basis Green form is now an explicit finite
double Hermite-slice mode sum. The remaining debt is purely the asymptotic
analysis of this 1D-sliced expression. -/
private theorem latticeGreenBilinear_basis_eq_double_hermite_slice_sum_2d
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (i j : ℕ) :
    latticeGreenBilinear 2 N a mass
      (continuumBasisSuccSucc 0 i)
      (continuumBasisSuccSucc 0 j) =
      ∑ m0 : Fin N, ∑ m1 : Fin N,
        latticeHermiteDoubleGreenTerm (N := N) a mass i j m0 m1 := by
  rw [latticeGreenBilinear_basis_eq_iterated_slice_sum_2d
    (N := N) (a := a) (mass := mass) ha hmass i j,
    latticeBasisIteratedSliceSum_zero_eq_double_sum
      (N := N) (a := a) (mass := mass) (i := i) (j := j)]

/-! ## Uniform bound on the embedded two-point function -/

/-- **Covariance upper bound via eigenvalue lower bound.**

The covariance `⟨T h, T h⟩ ≤ (1/m²) · ‖h‖²_ℓ²` because all eigenvalues of
the mass operator satisfy `λ_k ≥ m²`, hence `λ_k⁻¹ ≤ m⁻²`. By the spectral
decomposition `⟨Th, Th⟩ = Σ_k λ_k⁻¹ (e_k · h)²`, the bound follows from Parseval. -/
private theorem covariance_le_mass_inv_sq_norm (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (h : FinLatticeField d N) :
    GaussianField.covariance (latticeCovariance d N a mass ha hmass) h h ≤
    mass⁻¹ ^ 2 * ∑ x : FinLatticeSites d N, h x ^ 2 := by
  rw [lattice_covariance_eq_spectral]
  -- Bound each term: λ_k⁻¹ * (e_k · h)² ≤ m⁻² * (e_k · h)²
  calc ∑ k, (massEigenvalues d N a mass k)⁻¹ *
        (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * h x) *
        (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * h x)
      = ∑ k, (massEigenvalues d N a mass k)⁻¹ *
          (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * h x) ^ 2 := by
        congr 1; ext k; ring
    _ ≤ ∑ k, mass⁻¹ ^ 2 *
          (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * h x) ^ 2 := by
        apply Finset.sum_le_sum; intro k _
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        -- Need: λ_k⁻¹ ≤ m⁻²
        have hev_pos := massOperatorMatrix_eigenvalues_pos d N a mass ha hmass k
        have hev_ge : mass ^ 2 ≤ massEigenvalues d N a mass k := by
          -- Use the quadratic form: Σ_x e_k(x) * (Q e_k)(x) = λ_k ≥ m²
          -- because Q = -Δ + m² and -Δ ≥ 0
          set e_k := (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _)
          -- Quadratic form equals eigenvalue * norm² = eigenvalue * 1
          have hquad := massOperator_quadratic_eq_spectral (d := d) (N := N) a mass e_k
          -- The k-th coefficient of e_k in the eigenbasis is 1, rest are 0
          -- So the sum simplifies to lambda_k * 1
          have hcoeff : ∀ j : FinLatticeSites d N,
              (∑ x, (massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) x *
                e_k x) = if j = k then 1 else 0 := by
            intro j
            have hinner := (massEigenvectorBasis d N a mass).inner_eq_ite j k
            -- hinner: ∑ i, e_k(i) * e_j(i) = if j = k then 1 else 0
            rw [← hinner]
            apply Finset.sum_congr rfl; intro x _; exact mul_comm _ _
          rw [show (∑ x, (e_k : FinLatticeSites d N → ℝ) x *
              (massOperator d N a mass (e_k : FinLatticeSites d N → ℝ)) x) =
              ∑ x, e_k x * (massOperator d N a mass e_k) x from rfl] at hquad
          simp_rw [hcoeff] at hquad
          -- Simplify: (if j = k then 1 else 0)^2 → ite, then sum_ite_eq'
          have hquad' := hquad
          simp only [ite_pow, one_pow, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
            not_false_eq_true] at hquad'
          -- Now: ∑ x, eigenvalue x * if x = k then 1 else 0
          -- Rewrite mul_ite and simplify
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, ite_true] at hquad'
          -- Now hquad': Σ_x e_k(x) * Q(e_k)(x) = massEigenvalues d N a mass k
          -- Lower bound from finiteLaplacian_neg_semidefinite
          have hmass_bound :
            mass ^ 2 * ∑ x : FinLatticeSites d N, e_k x ^ 2 ≤
            ∑ x, e_k x * (massOperator d N a mass e_k) x := by
            -- Expand massOperator = -Δ + m²·id
            have hexpand : ∀ x : FinLatticeSites d N,
                e_k x * (massOperator d N a mass e_k) x =
                -(e_k x * (finiteLaplacian d N a e_k) x) + mass ^ 2 * e_k x ^ 2 := by
              intro x
              simp only [massOperator, ContinuousLinearMap.add_apply,
                ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
                ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
                smul_eq_mul]
              ring
            have hlap := finiteLaplacian_neg_semidefinite d N a ha e_k
            simp_rw [hexpand, Finset.sum_add_distrib, ← Finset.mul_sum]
            linarith [Finset.sum_neg_distrib
              (f := fun x => e_k x * (finiteLaplacian d N a e_k) x)
              (s := Finset.univ)]
          -- e_k is normalized: Σ_x e_k(x)^2 = 1
          have hnorm : ∑ x : FinLatticeSites d N, e_k x ^ 2 = 1 := by
            have h_norm1 := (massEigenvectorBasis d N a mass).orthonormal.1 k
            simp only [EuclideanSpace.norm_eq] at h_norm1
            have h1 : ∑ x : FinLatticeSites d N, e_k x ^ 2 =
              ∑ x, ‖e_k x‖ ^ 2 := by
              congr 1; ext x; rw [Real.norm_eq_abs, sq_abs]
            rw [h1]
            have h3 : 0 ≤ ∑ x, ‖e_k x‖ ^ 2 :=
              Finset.sum_nonneg (fun x _ => sq_nonneg _)
            -- sqrt(s) = 1 implies s = sqrt(s)^2 = 1^2 = 1
            nlinarith [Real.sq_sqrt h3]
          rw [hnorm, mul_one] at hmass_bound
          linarith [hmass_bound, hquad']
        rw [inv_pow, ← one_div, ← one_div]
        exact div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hmass) hev_ge
    _ = mass⁻¹ ^ 2 * ∑ k,
          (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * h x) ^ 2 := by
        rw [← Finset.mul_sum]
    _ = mass⁻¹ ^ 2 * ∑ x, h x ^ 2 := by
        congr 1
        -- Parseval: Σ_k (e_k · h)² = Σ_x h(x)²
        have := massEigenbasis_sum_mul_sum_eq_site_inner (d := d) (N := N) a mass h h
        simp only [sq]
        linarith

/-! ### Helper lemmas for the Schwartz Riemann sum bound -/

/-- EuclideanSpace component norm ≤ full norm: `‖y_i‖ ≤ ‖y‖`. -/
private lemma euclidean_component_le_norm
    (y : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    ‖y i‖ ≤ ‖y‖ := by
  have h1 : ‖y i‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have : y i = y.ofLp i := rfl; rw [this]
    exact Finset.single_le_sum (f := fun j => ‖y.ofLp j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith [sq_nonneg (‖y i‖ - ‖y‖), norm_nonneg y]

/-- Schwartz decay squared: `f(y)² ≤ S_f² / (1+‖y‖)^{2d}`. -/
private lemma schwartz_sq_decay (f : ContinuumTestFunction d)
    (y : EuclideanSpace ℝ (Fin d)) :
    f y ^ 2 ≤ (2 ^ d * ((Finset.Iic ((d : ℕ), (0 : ℕ))).sup
      fun m => SchwartzMap.seminorm ℝ m.1 m.2) f) ^ 2 /
    (1 + ‖y‖) ^ (2 * d) := by
  set S := 2 ^ d * ((Finset.Iic ((d : ℕ), (0 : ℕ))).sup
    fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  have hdecay : (1 + ‖y‖) ^ d * ‖f y‖ ≤ S := by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℝ) (m := (d, 0)) (k := d) (n := 0)
      (le_refl d) (le_refl 0) f y
    simp only [norm_iteratedFDeriv_zero] at h; exact h
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ‖y‖) ^ (2 * d))]
  calc f y ^ 2 * (1 + ‖y‖) ^ (2 * d)
      = (‖f y‖) ^ 2 * ((1 + ‖y‖) ^ d) ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs, ← pow_mul]; ring_nf
    _ = ((1 + ‖y‖) ^ d * ‖f y‖) ^ 2 := by ring
    _ ≤ S ^ 2 := by
        apply sq_le_sq'
        · nlinarith [mul_nonneg
            (pow_nonneg
              (show (0 : ℝ) ≤ 1 + ‖y‖ by linarith [norm_nonneg y]) d)
            (norm_nonneg (f y))]
        · exact hdecay

/-- Product norm bound: `∏_i (1+‖y_i‖)² ≤ (1+‖y‖)^{2d}`. -/
private lemma norm_prod_bound (y : EuclideanSpace ℝ (Fin d)) :
    ∏ i : Fin d, (1 + ‖y i‖) ^ 2 ≤ (1 + ‖y‖) ^ (2 * d) := by
  rw [show (1 + ‖y‖) ^ (2 * d) = ∏ _i : Fin d, (1 + ‖y‖) ^ 2
    from by simp [Finset.prod_const, pow_mul]]
  exact Finset.prod_le_prod (fun i _ => sq_nonneg _)
    (fun i _ => pow_le_pow_left₀
      (by linarith [norm_nonneg (y i)])
      (by linarith [euclidean_component_le_norm d y i]) 2)

/-- Schwartz product bound: `f(y)² · ∏_i (1+‖y_i‖)² ≤ S_f²`. -/
private lemma schwartz_sq_product_bound (f : ContinuumTestFunction d)
    (y : EuclideanSpace ℝ (Fin d)) :
    f y ^ 2 * ∏ i : Fin d, (1 + ‖y i‖) ^ 2 ≤
    (2 ^ d * ((Finset.Iic ((d : ℕ), (0 : ℕ))).sup
      fun m => SchwartzMap.seminorm ℝ m.1 m.2) f) ^ 2 := by
  set S := 2 ^ d * ((Finset.Iic ((d : ℕ), (0 : ℕ))).sup
    fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  calc f y ^ 2 * ∏ i, (1 + ‖y i‖) ^ 2
      ≤ S ^ 2 / (1 + ‖y‖) ^ (2 * d) * ∏ i, (1 + ‖y i‖) ^ 2 :=
        mul_le_mul_of_nonneg_right (schwartz_sq_decay d f y)
          (Finset.prod_nonneg (fun i _ => sq_nonneg _))
    _ ≤ S ^ 2 / (1 + ‖y‖) ^ (2 * d) * (1 + ‖y‖) ^ (2 * d) :=
        mul_le_mul_of_nonneg_left (norm_prod_bound d y)
          (div_nonneg (sq_nonneg _) (le_of_lt (by positivity)))
    _ = S ^ 2 := by field_simp

/-- `signedVal` agrees with Mathlib's centered representative `ZMod.valMinAbs`. -/
private lemma signedVal_eq_valMinAbs (x : ZMod N) :
    signedVal N x = x.valMinAbs := by
  rw [signedVal, ZMod.valMinAbs_def_pos]
  have hxcast : x.cast = (x.val : ℤ) := by
    simpa using (ZMod.cast_eq_val (R := ℤ) x)
  by_cases h : x.val ≤ N / 2
  · have h' : x.cast ≤ (N : ℤ) / 2 := by
      rw [hxcast]
      omega
    simp [h, h']
  · have h' : ¬ x.cast ≤ (N : ℤ) / 2 := by
      intro hx
      apply h
      rw [hxcast] at hx
      omega
    simp [h, h']

/-- The absolute centered representative equals the minimum of the two boundary
distances on `ZMod N`. -/
private lemma signedVal_natAbs_eq_min (x : ZMod N) :
    (signedVal N x).natAbs = min (ZMod.val x) (N - ZMod.val x) := by
  rw [signedVal_eq_valMinAbs N x, ZMod.valMinAbs_natAbs_eq_min]

omit [NeZero N] in
private lemma physPos_norm_component (a : ℝ) (ha : 0 < a)
    (x : FinLatticeSites d N) (i : Fin d) :
    ‖(physicalPosition d N a x) i‖ =
      a * ((signedVal N (x i)).natAbs : ℝ) := by
  rw [show (physicalPosition d N a x) i = a * (signedVal N (x i) : ℝ)
    from by rfl]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_of_lt ha)]
  have h_abs : ((signedVal N (x i)).natAbs : ℝ) = |(signedVal N (x i) : ℝ)| := by
    simpa using (Nat.cast_natAbs (α := ℝ) (signedVal N (x i)))
  rw [← h_abs]

/-- ZMod sum equals Finset.range sum. -/
private lemma zmod_sum_eq_range_sum (g : ℕ → ℝ) :
    ∑ x : ZMod N, g (ZMod.val x) =
    ∑ n ∈ Finset.range N, g n := by
  rw [show ∑ x : ZMod N, g (ZMod.val x) = ∑ n : Fin N, g n.val
    from Fintype.sum_bijective
      (fun (x : ZMod N) =>
        (⟨ZMod.val x, ZMod.val_lt x⟩ : Fin N))
      ⟨fun a b h => ZMod.val_injective N (Fin.mk.inj h),
       fun ⟨n, hn⟩ =>
        ⟨(n : ZMod N), by
          ext; exact ZMod.val_natCast_of_lt hn⟩⟩
      _ _ (fun _ => rfl),
    ← Finset.sum_range (f := g)]

/-- Telescoping: `a/(1+an)² ≤ 1/(1+a(n-1)) - 1/(1+an)` for `n ≥ 1`. -/
private lemma telescoping_step (a : ℝ) (ha : 0 < a)
    (n : ℕ) (hn : 1 ≤ n) :
    a / (1 + a * (n : ℝ)) ^ 2 ≤
    1 / (1 + a * ((n : ℝ) - 1)) - 1 / (1 + a * (n : ℝ)) := by
  have h1 : (0 : ℝ) < 1 + a * (n : ℝ) := by positivity
  have h2 : (0 : ℝ) < 1 + a * ((n : ℝ) - 1) := by
    nlinarith [show (1 : ℝ) ≤ (n : ℝ) from Nat.one_le_cast.mpr hn]
  suffices a / (1 + a * (n : ℝ)) ^ 2 ≤
      a / ((1 + a * ((n : ℝ) - 1)) * (1 + a * (n : ℝ))) by
    calc a / (1 + a * (n : ℝ)) ^ 2
        ≤ a / ((1 + a * ((n : ℝ) - 1)) * (1 + a * (n : ℝ))) := this
      _ = 1 / (1 + a * ((n : ℝ) - 1)) - 1 / (1 + a * (n : ℝ)) := by
          field_simp; ring
  exact div_le_div_of_nonneg_left (le_of_lt ha)
    (mul_pos h2 h1) (by nlinarith [le_of_lt h1])

/-- 1D sum bound: `Σ_{n ∈ range M} a/(1+an)² ≤ 2` for `0 < a ≤ 1`. -/
private lemma one_d_sum_bound (a : ℝ) (ha : 0 < a)
    (ha1 : a ≤ 1) (M : ℕ) :
    ∑ n ∈ Finset.range M,
      a / (1 + a * (n : ℝ)) ^ 2 ≤ 2 := by
  cases M with
  | zero => simp
  | succ K =>
    rw [Finset.sum_range_succ'
      (f := fun n => a / (1 + a * (n : ℝ)) ^ 2)]
    simp only [Nat.cast_zero, mul_zero, add_zero,
      one_pow, div_one]
    have htel : ∑ k ∈ Finset.range K,
        a / (1 + a * ((k : ℝ) + 1)) ^ 2 ≤
        ∑ k ∈ Finset.range K,
          (1 / (1 + a * (k : ℝ)) -
           1 / (1 + a * ((k : ℝ) + 1))) := by
      apply Finset.sum_le_sum; intro k _
      have h := telescoping_step a ha (k + 1)
        (Nat.le_add_left 1 k)
      simp only [Nat.cast_add, Nat.cast_one,
        show ((k : ℝ) + 1) - 1 = (k : ℝ) by ring] at h
      exact h
    have hsum_eq : ∑ k ∈ Finset.range K,
        (1 / (1 + a * (k : ℝ)) -
         1 / (1 + a * ((k : ℝ) + 1))) =
        1 - 1 / (1 + a * (K : ℝ)) := by
      have h := Finset.sum_range_sub'
        (fun k => 1 / (1 + a * (k : ℝ))) K
      simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one,
        mul_zero, add_zero, div_one] at h
      exact h
    -- Normalize ↑(k+1) to ↑k + 1 everywhere
    simp only [Nat.cast_add, Nat.cast_one] at htel ⊢
    rw [hsum_eq] at htel
    linarith [div_nonneg one_pos.le
      (le_of_lt
        (by positivity : (0 : ℝ) < 1 + a * (K : ℝ)))]

/-- Tail version of the 1D decay bound:
    `Σ_{n ∈ range M} a/(1+a(n+1))² ≤ 1`. -/
private lemma one_d_shift_sum_bound (a : ℝ) (ha : 0 < a) (M : ℕ) :
    ∑ n ∈ Finset.range M,
      a / (1 + a * ((n : ℝ) + 1)) ^ 2 ≤ 1 := by
  have htel : ∑ n ∈ Finset.range M,
      a / (1 + a * ((n : ℝ) + 1)) ^ 2 ≤
      ∑ n ∈ Finset.range M,
        (1 / (1 + a * (n : ℝ)) -
         1 / (1 + a * ((n : ℝ) + 1))) := by
    apply Finset.sum_le_sum
    intro n _
    have h := telescoping_step a ha (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    simpa only [Nat.cast_add, Nat.cast_one,
      show ((n : ℝ) + 1) - 1 = (n : ℝ) by ring] using h
  calc ∑ n ∈ Finset.range M, a / (1 + a * ((n : ℝ) + 1)) ^ 2
      ≤ ∑ n ∈ Finset.range M,
          (1 / (1 + a * (n : ℝ)) -
           1 / (1 + a * ((n : ℝ) + 1))) := htel
    _ = 1 - 1 / (1 + a * (M : ℝ)) := by
        have h := Finset.sum_range_sub' (fun k => 1 / (1 + a * (k : ℝ))) M
        simpa only [Nat.cast_zero, Nat.cast_add, Nat.cast_one,
          mul_zero, add_zero, div_one] using h
    _ ≤ 1 := by
        have hpos : (0 : ℝ) < 1 + a * (M : ℝ) := by positivity
        linarith [div_nonneg one_pos.le (le_of_lt hpos)]

/-- 1D bound over `ZMod N` written in centered coordinates:
    `Σ_{n : ZMod N} a/(1+a·|signedVal n|)² ≤ 3`. -/
private lemma one_d_zmod_bound (a : ℝ) (ha : 0 < a)
    (ha1 : a ≤ 1) :
    ∑ n : ZMod N,
      a / (1 + a * ((signedVal N n).natAbs : ℝ)) ^ 2 ≤ 3 := by
  let g : ℕ → ℝ := fun n => a / (1 + a * (n : ℝ)) ^ 2
  have hpoint : ∀ n : ZMod N,
      g ((signedVal N n).natAbs) ≤ g (ZMod.val n) + g (N - ZMod.val n) := by
    intro n
    rw [signedVal_natAbs_eq_min N n]
    by_cases h : ZMod.val n ≤ N - ZMod.val n
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (by positivity)
    · rw [min_eq_right (Nat.le_of_lt (lt_of_not_ge h))]
      exact le_add_of_nonneg_left (by positivity)
  calc ∑ n : ZMod N, a / (1 + a * ((signedVal N n).natAbs : ℝ)) ^ 2
      = ∑ n : ZMod N, g ((signedVal N n).natAbs) := by
          simp [g]
    _ ≤ ∑ n : ZMod N, (g (ZMod.val n) + g (N - ZMod.val n)) := by
          exact Finset.sum_le_sum (fun n _ => hpoint n)
    _ = (∑ n : ZMod N, g (ZMod.val n)) + ∑ n : ZMod N, g (N - ZMod.val n) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ n ∈ Finset.range N, g n) + ∑ n ∈ Finset.range N, g (N - n) := by
          rw [zmod_sum_eq_range_sum N g, zmod_sum_eq_range_sum N (fun n => g (N - n))]
    _ = (∑ n ∈ Finset.range N, g n) + ∑ n ∈ Finset.range N, g (n + 1) := by
          congr 1
          trans ∑ n ∈ Finset.range N, g (N - 1 - n + 1)
          · apply Finset.sum_congr rfl
            intro n hn
            congr 1
            have hnlt : n < N := Finset.mem_range.mp hn
            omega
          · simpa [Nat.succ_eq_add_one] using
              (Finset.sum_range_reflect (fun n => g (n + 1)) N)
    _ ≤ 3 := by
          have h1 : ∑ n ∈ Finset.range N, g n ≤ 2 := one_d_sum_bound a ha ha1 N
          have h2 : ∑ n ∈ Finset.range N, g (n + 1) ≤ 1 := by
            simpa [g] using one_d_shift_sum_bound a ha N
          linarith

/-! ### Schwartz Riemann sum bound -/

private def schwartzSeminormWindow (d : ℕ) : Finset (ℕ × ℕ) :=
  Finset.Iic ((d : ℕ), (0 : ℕ))

private def schwartzDecayMajorant (d : ℕ) (f : ContinuumTestFunction d) : ℝ :=
  2 ^ d * ((schwartzSeminormWindow d).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) f

/-- The Riemann-sum estimate with an explicit seminorm majorant.

If `S` dominates the finite family of seminorms used in
`schwartz_sq_product_bound`, then the lattice Schwartz Riemann sum is bounded by
`S² * 3^d`. -/
private theorem schwartz_riemann_sum_bound_of_majorant
    (f : ContinuumTestFunction d) (S : ℝ)
    (hS :
      schwartzDecayMajorant d f ≤ S) :
    ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∀ (N : ℕ) [NeZero N],
    a ^ d * ∑ x : FinLatticeSites d N,
      (evalAtSite d N a f x) ^ 2 ≤ S ^ 2 * 3 ^ d := by
  intro a ha ha1 N _
  have hmajorant_nonneg : 0 ≤ schwartzDecayMajorant d f := by
    unfold schwartzDecayMajorant
    exact mul_nonneg (by positivity)
      (apply_nonneg
        ((schwartzSeminormWindow d).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) f)
  have hS_nonneg : 0 ≤ S := le_trans hmajorant_nonneg hS
  simp only [evalAtSite]
  have hbound : ∀ x : FinLatticeSites d N,
      f (physicalPosition d N a x) ^ 2 ≤
      S ^ 2 / ∏ i : Fin d,
        (1 + a * ((signedVal N (x i)).natAbs : ℝ)) ^ 2 := by
    intro x
    have hprod_pos : (0 : ℝ) < ∏ i : Fin d,
        (1 + a * ((signedVal N (x i)).natAbs : ℝ)) ^ 2 :=
      Finset.prod_pos (fun i _ =>
        sq_pos_of_pos (by positivity))
    rw [le_div_iff₀ hprod_pos]
    calc f (physicalPosition d N a x) ^ 2 *
          ∏ i, (1 + a * ((signedVal N (x i)).natAbs : ℝ)) ^ 2
        = f (physicalPosition d N a x) ^ 2 *
          ∏ i, (1 + ‖(physicalPosition d N a x) i‖) ^ 2 := by
          congr 1; apply Finset.prod_congr rfl
          intro i _; congr 1; congr 1
          exact (physPos_norm_component d N a ha x i).symm
      _ ≤ schwartzDecayMajorant d f ^ 2 := by
          simpa [schwartzDecayMajorant, schwartzSeminormWindow] using
            schwartz_sq_product_bound d f (physicalPosition d N a x)
      _ ≤ S ^ 2 := by
          nlinarith [hS, hmajorant_nonneg]
  calc a ^ d * ∑ x, f (physicalPosition d N a x) ^ 2
      ≤ a ^ d * ∑ x : FinLatticeSites d N,
          S ^ 2 / ∏ i : Fin d,
            (1 + a * ((signedVal N (x i)).natAbs : ℝ)) ^ 2 := by
        gcongr with x
        exact hbound x
    _ = S ^ 2 * ∑ x : FinLatticeSites d N,
          ∏ i : Fin d,
            a / (1 + a * ((signedVal N (x i)).natAbs : ℝ)) ^ 2 := by
        conv_lhs =>
          rw [Finset.mul_sum]
          arg 2; ext x
          rw [show a ^ d * (S ^ 2 /
              ∏ i : Fin d,
                (1 + a * ((signedVal N (x i)).natAbs : ℝ)) ^ 2) =
            S ^ 2 * (a ^ d /
              ∏ i : Fin d,
                (1 + a * ((signedVal N (x i)).natAbs : ℝ)) ^ 2) from
              by ring]
          rw [show a ^ d = ∏ _i : Fin d, a from
            by simp [Finset.prod_const]]
          rw [← Finset.prod_div_distrib]
        rw [← Finset.mul_sum]
    _ = S ^ 2 * ∏ _i : Fin d,
          ∑ n : ZMod N,
            a / (1 + a * ((signedVal N n).natAbs : ℝ)) ^ 2 := by
        congr 1
        rw [← Fintype.prod_sum
          (fun _ => fun n : ZMod N =>
            a / (1 + a * ((signedVal N n).natAbs : ℝ)) ^ 2)]
    _ ≤ S ^ 2 * 3 ^ d := by
        gcongr
        rw [show (3 : ℝ) ^ d = ∏ _i : Fin d, (3 : ℝ)
          from by simp [Finset.prod_const]]
        exact Finset.prod_le_prod
          (fun i _ => Finset.sum_nonneg
            (fun n _ => div_nonneg
              (le_of_lt ha) (sq_nonneg _)))
          (fun i _ => one_d_zmod_bound N a ha ha1)

/-- **Schwartz Riemann sum bound.**

For a Schwartz function f : S(ℝ^d) and the lattice (ℤ/Nℤ)^d with spacing a,
the weighted sum `a^d · Σ_{x} |f(a·x)|²` is bounded uniformly in a ∈ (0,1] and N.

The proof uses:
1. Schwartz decay: `(1+‖y‖)^d · |f(y)| ≤ S_f` from seminorm bounds
2. Product factorization: `(1+‖y‖)^{2d} ≥ ∏_i (1+|y_i|)²`
3. Sum factorization: `Σ_x ∏_i g(x_i) = ∏_i Σ_n g(n)` over the lattice
4. 1D centered-coordinate bound: `Σ_n a/(1+a|n|)² ≤ 3` for `0 < a ≤ 1`

This gives `a^d Σ_x f(ax)² ≤ S_f² · 3^d`. -/
private theorem schwartz_riemann_sum_bound
    (f : ContinuumTestFunction d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∀ (N : ℕ) [NeZero N],
    a ^ d * ∑ x : FinLatticeSites d N,
      (evalAtSite d N a f x) ^ 2 ≤ C := by
  set S := schwartzDecayMajorant d f
  refine ⟨S ^ 2 * 3 ^ d + 1, by positivity, ?_⟩
  intro a ha ha1 N _
  have hmain := schwartz_riemann_sum_bound_of_majorant (d := d) (N := N) f S (le_rfl) a ha ha1
  linarith

/-- Polynomial Riemann-sum bound on DM basis vectors of the Schwartz space. -/
private theorem schwartz_riemann_sum_basis_bound [Fact (0 < d)] :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℕ, ∀ i (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∀ (N : ℕ) [NeZero N],
    a ^ d * ∑ x : FinLatticeSites d N,
      (evalAtSite d N a (DyninMityaginSpace.basis i) x) ^ 2 ≤
        C * (1 + (i : ℝ)) ^ r := by
  obtain ⟨D, hD_pos, r, hD⟩ :=
    finset_sup_poly_bound
      (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)
      (schwartzSeminormWindow d)
      (DyninMityaginSpace.basis (E := ContinuumTestFunction d))
      (fun m _hm => by
        have hd_ne : d ≠ 0 := Nat.ne_of_gt Fact.out
        rcases Nat.exists_eq_succ_of_ne_zero hd_ne with ⟨d', rfl⟩
        simpa using continuum_basis_seminorm_growth d' m.1 m.2)
  set A : ℝ := 2 ^ d * D
  refine ⟨A ^ 2 * 3 ^ d + 1, by positivity, 2 * r, ?_⟩
  intro i a ha ha1 N _
  have hmajorant :
      schwartzDecayMajorant d (DyninMityaginSpace.basis (E := ContinuumTestFunction d) i) ≤
        A * (1 + (i : ℝ)) ^ r := by
    dsimp [schwartzDecayMajorant, schwartzSeminormWindow, A]
    calc
      2 ^ d *
          ((schwartzSeminormWindow d).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2)
            (DyninMityaginSpace.basis (E := ContinuumTestFunction d) i)
        ≤ 2 ^ d * (D * (1 + (i : ℝ)) ^ r) := by
            gcongr
            exact hD i
      _ = A * (1 + (i : ℝ)) ^ r := by ring
  have hmain :=
    schwartz_riemann_sum_bound_of_majorant
      (d := d) (N := N)
      (f := DyninMityaginSpace.basis (E := ContinuumTestFunction d) i)
      (S := A * (1 + (i : ℝ)) ^ r)
      hmajorant a ha ha1
  have hpow_nonneg : 0 ≤ (1 + (i : ℝ)) ^ (2 * r) := by positivity
  calc
    a ^ d * ∑ x : FinLatticeSites d N,
      (evalAtSite d N a (DyninMityaginSpace.basis i) x) ^ 2
      ≤ (A * (1 + (i : ℝ)) ^ r) ^ 2 * 3 ^ d := hmain
    _ = A ^ 2 * 3 ^ d * (1 + (i : ℝ)) ^ (2 * r) := by ring
    _ ≤ (A ^ 2 * 3 ^ d + 1) * (1 + (i : ℝ)) ^ (2 * r) := by
        have hA : A ^ 2 * 3 ^ d ≤ A ^ 2 * 3 ^ d + 1 := by linarith
        calc
          A ^ 2 * 3 ^ d * (1 + (i : ℝ)) ^ (2 * r)
            ≤ (A ^ 2 * 3 ^ d + 1) * (1 + (i : ℝ)) ^ (2 * r) :=
              mul_le_mul_of_nonneg_right hA hpow_nonneg

/-- The lattice Green form on the diagonal is controlled by any lattice
Riemann-sum bound for the corresponding test function. -/
private theorem latticeGreenBilinear_diag_bound_of_riemann_bound
    (mass : ℝ) (hmass : 0 < mass)
    (f : ContinuumTestFunction d) (C_f : ℝ)
    (hC : ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
      ∀ (N : ℕ) [NeZero N],
      a ^ d * ∑ x : FinLatticeSites d N, (evalAtSite d N a f x) ^ 2 ≤ C_f) :
    ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
      latticeGreenBilinear d N a mass f f ≤ mass⁻¹ ^ 2 * C_f := by
  intro a ha ha_le
  rw [← embeddedTwoPoint_eq_latticeGreenBilinear (d := d) (N := N) (a := a)
    (mass := mass) (ha := ha) (hmass := hmass) f f]
  set T := latticeCovariance d N a mass ha hmass
  set μ := latticeGaussianMeasure d N a mass ha hmass
  set h_f : FinLatticeField d N := fun x => a ^ d * evalAtSite d N a f x
  have hintegrand : ∀ ω : Configuration (FinLatticeField d N),
      (a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x) *
      (a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x) =
      (ω h_f) ^ 2 := by
    intro ω
    have hlin : ω h_f = a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x := by
      show ω h_f = a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x
      have : h_f = a ^ d • ∑ x : FinLatticeSites d N,
          evalAtSite d N a f x • Pi.single x (1 : ℝ) := by
        ext y; simp [h_f, Finset.sum_apply, Pi.single_apply]
      rw [this, map_smul, smul_eq_mul]
      congr 1
      rw [map_sum]
      congr 1; ext x
      rw [map_smul, smul_eq_mul, mul_comm]
    rw [hlin]
    ring
  rw [embeddedTwoPoint_eq_covariance (d := d) (N := N) (a := a)
    (mass := mass) (ha := ha) (hmass := hmass) f f]
  simp only [latticeEmbed_eval, latticeEmbedEval]
  have hintegrand_eq :
      (fun ω : Configuration (FinLatticeField d N) =>
        (a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x) *
        (a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x)) =
      fun ω => (ω h_f) ^ 2 := by
    ext ω
    exact hintegrand ω
  rw [hintegrand_eq]
  have hsecond :
      ∫ ω : Configuration (FinLatticeField d N), ω h_f ^ 2
        ∂latticeGaussianMeasure d N a mass ha hmass =
      GaussianField.covariance T h_f h_f := by
    simpa [T, latticeGaussianMeasure, GaussianField.covariance] using
      (GaussianField.second_moment_eq_covariance T h_f)
  rw [hsecond]
  calc
    GaussianField.covariance T h_f h_f
      ≤ mass⁻¹ ^ 2 * ∑ x, h_f x ^ 2 :=
        covariance_le_mass_inv_sq_norm d N a mass ha hmass h_f
    _ = mass⁻¹ ^ 2 * (a ^ d * a ^ d * ∑ x, (evalAtSite d N a f x) ^ 2) := by
        congr 1
        simp only [h_f, mul_pow, ← Finset.mul_sum]
        ring
    _ = mass⁻¹ ^ 2 * (a ^ d * (a ^ d * ∑ x, (evalAtSite d N a f x) ^ 2)) := by
        ring_nf
    _ ≤ mass⁻¹ ^ 2 * (1 * C_f) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply mul_le_mul _ (hC a ha ha_le N) (by positivity) (by positivity)
        exact pow_le_one₀ (le_of_lt ha) ha_le
    _ = mass⁻¹ ^ 2 * C_f := by ring

/-- Polynomial diagonal bound for the lattice Green form on DM basis vectors. -/
private theorem latticeGreenBilinear_basis_diag_bound [Fact (0 < d)]
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℕ, ∀ i (a : ℝ) (ha : 0 < a), a ≤ 1 →
      ∀ (N : ℕ) [NeZero N],
      latticeGreenBilinear d N a mass
        (DyninMityaginSpace.basis i)
        (DyninMityaginSpace.basis i) ≤
          C * (1 + (i : ℝ)) ^ r := by
  obtain ⟨C_f, hC_f_pos, r, hC_f⟩ := schwartz_riemann_sum_basis_bound (d := d)
  refine ⟨mass⁻¹ ^ 2 * C_f, mul_pos (sq_pos_of_pos (inv_pos.mpr hmass)) hC_f_pos, r, ?_⟩
  intro i a ha ha1 N _
  have h :=
    latticeGreenBilinear_diag_bound_of_riemann_bound
    (d := d) (N := N) mass hmass
    (DyninMityaginSpace.basis i)
    (C_f * (1 + (i : ℝ)) ^ r)
    (fun a ha ha1 N => hC_f i a ha ha1 N) a ha ha1
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-- Cross terms are controlled by diagonal lattice Green terms via
`2|xy| ≤ x² + y²` modewise in the spectral sum. -/
private theorem latticeGreenBilinear_abs_le_half_diag_add_diag
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : ContinuumTestFunction d) :
    |latticeGreenBilinear d N a mass f g| ≤
      (latticeGreenBilinear d N a mass f f +
        latticeGreenBilinear d N a mass g g) / 2 := by
  let Af : FinLatticeSites d N → ℝ := fun k =>
    ∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
      latticeTestField d N a f x
  let Ag : FinLatticeSites d N → ℝ := fun k =>
    ∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
      latticeTestField d N a g x
  unfold latticeGreenBilinear
  have hterm :
      ∀ k : FinLatticeSites d N,
        |(massEigenvalues d N a mass k)⁻¹ * Af k * Ag k| ≤
          (massEigenvalues d N a mass k)⁻¹ * ((Af k) ^ 2 + (Ag k) ^ 2) / 2 := by
    intro k
    have hLambda_nonneg : 0 ≤ (massEigenvalues d N a mass k)⁻¹ := by
      positivity [massOperatorMatrix_eigenvalues_pos d N a mass ha hmass k]
    have hxy_abs : 2 * (|Af k| * |Ag k|) ≤ |Af k| ^ 2 + |Ag k| ^ 2 := by
      nlinarith [sq_nonneg (|Af k| - |Ag k|)]
    have hxy : 2 * (|Af k| * |Ag k|) ≤ (Af k) ^ 2 + (Ag k) ^ 2 := by
      simpa [sq_abs] using hxy_abs
    have hscaled :
        (massEigenvalues d N a mass k)⁻¹ * (2 * (|Af k| * |Ag k|)) ≤
          (massEigenvalues d N a mass k)⁻¹ * ((Af k) ^ 2 + (Ag k) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hxy hLambda_nonneg
    have habs :
        2 * |(massEigenvalues d N a mass k)⁻¹ * Af k * Ag k| =
          (massEigenvalues d N a mass k)⁻¹ * (2 * (|Af k| * |Ag k|)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hLambda_nonneg]
      ring
    have hscaled' : 2 * |(massEigenvalues d N a mass k)⁻¹ * Af k * Ag k| ≤
        (massEigenvalues d N a mass k)⁻¹ * ((Af k) ^ 2 + (Ag k) ^ 2) := by
      rw [habs]
      exact hscaled
    have htwo_pos : (0 : ℝ) < 2 := by norm_num
    nlinarith
  calc
    |∑ k : FinLatticeSites d N, (massEigenvalues d N a mass k)⁻¹ * Af k * Ag k|
      ≤ ∑ k : FinLatticeSites d N,
          |(massEigenvalues d N a mass k)⁻¹ * Af k * Ag k| := by
            exact Finset.abs_sum_le_sum_abs (f := fun k : FinLatticeSites d N =>
              (massEigenvalues d N a mass k)⁻¹ * Af k * Ag k) (s := Finset.univ)
    _ ≤ ∑ k : FinLatticeSites d N,
          (massEigenvalues d N a mass k)⁻¹ * ((Af k) ^ 2 + (Ag k) ^ 2) / 2 := by
            exact Finset.sum_le_sum fun k _ => hterm k
    _ = ((∑ k : FinLatticeSites d N, (massEigenvalues d N a mass k)⁻¹ * Af k * Af k) +
          (∑ k : FinLatticeSites d N, (massEigenvalues d N a mass k)⁻¹ * Ag k * Ag k)) / 2 := by
        rw [show (fun k : FinLatticeSites d N =>
            (massEigenvalues d N a mass k)⁻¹ * ((Af k) ^ 2 + (Ag k) ^ 2) / 2) =
            fun k => ((massEigenvalues d N a mass k)⁻¹ * Af k * Af k +
              (massEigenvalues d N a mass k)⁻¹ * Ag k * Ag k) / 2 by
              ext k; ring]
        calc
          ∑ k : FinLatticeSites d N,
              ((massEigenvalues d N a mass k)⁻¹ * Af k * Af k +
                (massEigenvalues d N a mass k)⁻¹ * Ag k * Ag k) / 2
              = (1 / 2) * ∑ k : FinLatticeSites d N,
                  ((massEigenvalues d N a mass k)⁻¹ * Af k * Af k +
                    (massEigenvalues d N a mass k)⁻¹ * Ag k * Ag k) := by
                    rw [Finset.mul_sum]
                    congr 1
                    ext k
                    ring
          _ = (1 / 2) *
                ((∑ k : FinLatticeSites d N, (massEigenvalues d N a mass k)⁻¹ * Af k * Af k) +
                  (∑ k : FinLatticeSites d N, (massEigenvalues d N a mass k)⁻¹ * Ag k * Ag k)) := by
                    rw [Finset.sum_add_distrib]
          _ = ((∑ k : FinLatticeSites d N, (massEigenvalues d N a mass k)⁻¹ * Af k * Af k) +
                (∑ k : FinLatticeSites d N, (massEigenvalues d N a mass k)⁻¹ * Ag k * Ag k)) / 2 := by
                    ring
/-- Eventual polynomial basis-pair bound for the lattice Green form along any
continuum-limit sequence `a_n → 0`. -/
private theorem latticeGreenBilinear_basis_eventually_bound [Fact (0 < d)]
    (mass : ℝ) (hmass : 0 < mass)
    (a_seq : ℕ → ℝ) (ha_pos : ∀ n, 0 < a_seq n)
    (ha_lim : Tendsto a_seq atTop (nhds 0))
    (N_seq : ℕ → ℕ) [∀ n, NeZero (N_seq n)] :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℕ,
      ∀ᶠ n in atTop, ∀ i j,
        |latticeGreenBilinear d (N_seq n) (a_seq n) mass
          (DyninMityaginSpace.basis i)
          (DyninMityaginSpace.basis j)| ≤
            C * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := by
  obtain ⟨C, hC_pos, r, hdiag⟩ := latticeGreenBilinear_basis_diag_bound (d := d) mass hmass
  have ha_le_one : ∀ᶠ n in atTop, a_seq n ≤ 1 := by
    have hmem : Set.Iic (1 : ℝ) ∈ nhds (0 : ℝ) :=
      Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num)
    exact ha_lim hmem
  refine ⟨C, hC_pos, r, ?_⟩
  filter_upwards [ha_le_one] with n hn i j
  have hii := hdiag i (a_seq n) (ha_pos n) hn (N_seq n)
  have hjj := hdiag j (a_seq n) (ha_pos n) hn (N_seq n)
  have hcross :=
    latticeGreenBilinear_abs_le_half_diag_add_diag
      (d := d) (N := N_seq n) (a := a_seq n) (mass := mass)
      (ha := ha_pos n) (hmass := hmass)
      (DyninMityaginSpace.basis i) (DyninMityaginSpace.basis j)
  have hpow_i_nonneg : 0 ≤ (1 + (i : ℝ)) ^ r := by positivity
  have hpow_j_nonneg : 0 ≤ (1 + (j : ℝ)) ^ r := by positivity
  have hsum_le_prod :
      (C * (1 + (i : ℝ)) ^ r + C * (1 + (j : ℝ)) ^ r) / 2 ≤
        C * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := by
    have hi_one : 1 ≤ (1 + (i : ℝ)) ^ r := by
      apply one_le_pow₀
      linarith
    have hj_one : 1 ≤ (1 + (j : ℝ)) ^ r := by
      apply one_le_pow₀
      linarith
    have hleft :
        C * (1 + (i : ℝ)) ^ r ≤ C * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := by
      calc
        C * (1 + (i : ℝ)) ^ r = C * (1 + (i : ℝ)) ^ r * 1 := by ring
        _ ≤ C * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := by
            exact mul_le_mul_of_nonneg_left hj_one
              (mul_nonneg (le_of_lt hC_pos) hpow_i_nonneg)
    have hright :
        C * (1 + (j : ℝ)) ^ r ≤ C * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := by
      calc
        C * (1 + (j : ℝ)) ^ r = 1 * (C * (1 + (j : ℝ)) ^ r) := by ring
        _ ≤ (1 + (i : ℝ)) ^ r * (C * (1 + (j : ℝ)) ^ r) := by
            exact mul_le_mul_of_nonneg_right hi_one
              (mul_nonneg (le_of_lt hC_pos) hpow_j_nonneg)
        _ = C * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := by ring
    have hsum :
        C * (1 + (i : ℝ)) ^ r + C * (1 + (j : ℝ)) ^ r ≤
          2 * (C * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r) := by
      linarith
    nlinarith [hsum]
  calc
    |latticeGreenBilinear d (N_seq n) (a_seq n) mass
      (DyninMityaginSpace.basis i)
      (DyninMityaginSpace.basis j)|
      ≤ (latticeGreenBilinear d (N_seq n) (a_seq n) mass
            (DyninMityaginSpace.basis i)
            (DyninMityaginSpace.basis i) +
          latticeGreenBilinear d (N_seq n) (a_seq n) mass
            (DyninMityaginSpace.basis j)
            (DyninMityaginSpace.basis j)) / 2 := hcross
    _ ≤ (C * (1 + (i : ℝ)) ^ r + C * (1 + (j : ℝ)) ^ r) / 2 := by
        gcongr
    _ ≤ C * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := hsum_le_prod

/-- Uniform polynomial bound for the one-dimensional Hermite-slice Green form.
The effective mass dependence is exposed as `(sqrt massShift)^{-2}` so the
polynomial constant is independent of the slice mass parameter. -/
private theorem latticeHermiteSliceBilinear_effective_mass_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℕ, ∀ massShift : ℝ, 0 < massShift →
      ∀ i j (a : ℝ), 0 < a → a ≤ 1 →
      ∀ (N : ℕ) [NeZero N],
      |latticeHermiteSliceBilinear (N := N) a massShift i j| ≤
        C * (Real.sqrt massShift)⁻¹ ^ 2 *
          (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := by
  letI : Fact (0 < 1) := ⟨by positivity⟩
  obtain ⟨C, hC_pos, r, hC⟩ := schwartz_riemann_sum_basis_bound (d := 1)
  refine ⟨C, hC_pos, r, ?_⟩
  intro massShift hmassShift i j a ha ha1 N _
  have hsqrt : 0 < Real.sqrt massShift := Real.sqrt_pos.mpr hmassShift
  set K : ℝ := C * (Real.sqrt massShift)⁻¹ ^ 2
  have hK_pos : 0 < K := by
    simp only [inv_pow, K]
    positivity
  have hii :
      latticeGreenBilinear 1 N a (Real.sqrt massShift)
        (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i)
        (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i) ≤
      K * (1 + (i : ℝ)) ^ r := by
    have hdiag :=
      latticeGreenBilinear_diag_bound_of_riemann_bound
        (d := 1) (N := N) (mass := Real.sqrt massShift) hsqrt
        (f := DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i)
        (C_f := C * (1 + (i : ℝ)) ^ r)
        (hC := fun a ha ha1 N => hC i a ha ha1 N) a ha ha1
    simpa [K, mul_assoc, mul_left_comm, mul_comm] using hdiag
  have hjj :
      latticeGreenBilinear 1 N a (Real.sqrt massShift)
        (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) j)
        (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) j) ≤
      K * (1 + (j : ℝ)) ^ r := by
    have hdiag :=
      latticeGreenBilinear_diag_bound_of_riemann_bound
        (d := 1) (N := N) (mass := Real.sqrt massShift) hsqrt
        (f := DyninMityaginSpace.basis (E := ContinuumTestFunction 1) j)
        (C_f := C * (1 + (j : ℝ)) ^ r)
        (hC := fun a ha ha1 N => hC j a ha ha1 N) a ha ha1
    simpa [K, mul_assoc, mul_left_comm, mul_comm] using hdiag
  have hcross :=
    latticeGreenBilinear_abs_le_half_diag_add_diag
      (d := 1) (N := N) (a := a) (mass := Real.sqrt massShift)
      (ha := ha) (hmass := hsqrt)
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i)
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) j)
  have hpow_i_nonneg : 0 ≤ (1 + (i : ℝ)) ^ r := by positivity
  have hpow_j_nonneg : 0 ≤ (1 + (j : ℝ)) ^ r := by positivity
  have hsum_le_prod :
      (K * (1 + (i : ℝ)) ^ r + K * (1 + (j : ℝ)) ^ r) / 2 ≤
        K * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := by
    have hi_one : 1 ≤ (1 + (i : ℝ)) ^ r := by
      apply one_le_pow₀
      linarith
    have hj_one : 1 ≤ (1 + (j : ℝ)) ^ r := by
      apply one_le_pow₀
      linarith
    have hleft :
        K * (1 + (i : ℝ)) ^ r ≤ K * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := by
      calc
        K * (1 + (i : ℝ)) ^ r = K * (1 + (i : ℝ)) ^ r * 1 := by ring
        _ ≤ K * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := by
            exact mul_le_mul_of_nonneg_left hj_one
              (mul_nonneg (le_of_lt hK_pos) hpow_i_nonneg)
    have hright :
        K * (1 + (j : ℝ)) ^ r ≤ K * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := by
      calc
        K * (1 + (j : ℝ)) ^ r = 1 * (K * (1 + (j : ℝ)) ^ r) := by ring
        _ ≤ (1 + (i : ℝ)) ^ r * (K * (1 + (j : ℝ)) ^ r) := by
            exact mul_le_mul_of_nonneg_right hi_one
              (mul_nonneg (le_of_lt hK_pos) hpow_j_nonneg)
        _ = K * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := by ring
    have hsum :
        K * (1 + (i : ℝ)) ^ r + K * (1 + (j : ℝ)) ^ r ≤
          2 * (K * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r) := by
      linarith
    nlinarith [hsum]
  calc
    |latticeHermiteSliceBilinear (N := N) a massShift i j|
      = |latticeGreenBilinear 1 N a (Real.sqrt massShift)
          (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i)
          (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) j)| := by
            rw [latticeHermiteSliceBilinear_eq_latticeGreenBilinear_1d
              (N := N) (a := a) (massShift := massShift) ha hmassShift i j]
    _ ≤ (latticeGreenBilinear 1 N a (Real.sqrt massShift)
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i)
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i) +
          latticeGreenBilinear 1 N a (Real.sqrt massShift)
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) j)
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) j)) / 2 := hcross
    _ ≤ (K * (1 + (i : ℝ)) ^ r + K * (1 + (j : ℝ)) ^ r) / 2 := by
        gcongr
    _ ≤ K * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := hsum_le_prod
    _ = C * (Real.sqrt massShift)⁻¹ ^ 2 *
          (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r := by
        simp [K]

omit d N [NeZero N] in
/-- One-dimensional Hermite basis vectors admit a polynomial-in-index Schwartz
decay bound of order two. This is the exact numerator decay used to control the
peeled lattice Fourier coefficients. -/
private theorem schwartzHermiteBasis1D_decay_two :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℕ, ∀ n (x : ℝ),
      |schwartzHermiteBasis1D n x| ≤ C * (1 + (n : ℝ)) ^ r / (1 + |x|) ^ 2 := by
  letI : Fact (0 < 1) := ⟨by positivity⟩
  obtain ⟨D, hD_pos, r, hD⟩ :=
    finset_sup_poly_bound
      (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)
      (Finset.Iic ((2 : ℕ), (0 : ℕ)))
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1))
      (fun m _hm => by
        simpa using continuum_basis_seminorm_growth (d := 0) m.1 m.2)
  set A : ℝ := 2 ^ (2 : ℕ) * D
  refine ⟨A, by positivity, r, ?_⟩
  intro n x
  let y : ContinuumSpaceTime 1 := euclideanFin1MeasEquiv.symm x
  have hmajorant :
      2 ^ (2 : ℕ) *
          ((Finset.Iic ((2 : ℕ), (0 : ℕ))).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2)
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) n) ≤
        A * (1 + (n : ℝ)) ^ r := by
    dsimp [A]
    calc
      2 ^ (2 : ℕ) *
          ((Finset.Iic ((2 : ℕ), (0 : ℕ))).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2)
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) n)
        ≤ 2 ^ (2 : ℕ) * (D * (1 + (n : ℝ)) ^ r) := by
            gcongr
            exact hD n
      _ = A * (1 + (n : ℝ)) ^ r := by ring
  have hdecay :=
    SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℝ) (m := (2, 0)) (k := 2) (n := 0)
      (le_refl 2) (le_refl 0)
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) n) y
  simp only [norm_iteratedFDeriv_zero] at hdecay
  have hbasis :
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) n) y =
        schwartzHermiteBasis1D n x := by
    simpa [y, euclideanFin1MeasEquiv_apply] using
      continuum_basis_apply_eq_hermite1D (n := n) (x := y)
  have hy0 : y 0 = x := by
    have hxy : euclideanFin1MeasEquiv y = x := by simp [y]
    simpa [euclideanFin1MeasEquiv_apply] using hxy
  have hnorm : ‖y‖ = |x| := by
    calc
      ‖y‖ = Real.sqrt (‖y 0‖ ^ 2) := by
        simp only [EuclideanSpace.norm_eq, Fin.sum_univ_one]
      _ = Real.sqrt (x ^ 2) := by rw [hy0, Real.norm_eq_abs, sq_abs]
      _ = |x| := Real.sqrt_sq_eq_abs x
  have hpoint :
      (1 + |x|) ^ 2 * |schwartzHermiteBasis1D n x| ≤ A * (1 + (n : ℝ)) ^ r := by
    calc
      (1 + |x|) ^ 2 * |schwartzHermiteBasis1D n x|
        = (1 + ‖y‖) ^ 2 *
            ‖(DyninMityaginSpace.basis (E := ContinuumTestFunction 1) n) y‖ := by
              simp [hbasis, hnorm, Real.norm_eq_abs]
      _ ≤ 2 ^ (2 : ℕ) *
            ((Finset.Iic ((2 : ℕ), (0 : ℕ))).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2)
              (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) n) := hdecay
      _ ≤ A * (1 + (n : ℝ)) ^ r := hmajorant
  have hden_pos : 0 < (1 + |x|) ^ 2 := by positivity
  have hpoint' :
      |schwartzHermiteBasis1D n x| * (1 + |x|) ^ 2 ≤ A * (1 + (n : ℝ)) ^ r := by
    simpa [mul_comm] using hpoint
  exact (le_div_iff₀ hden_pos).2 hpoint'

omit d N [NeZero N] in
/-- The model tail `C / (|k|L)^2` is summable over `ℤ`. -/
private lemma summable_inv_int_sq_mul (C L : ℝ) :
    Summable (fun k : ℤ => C / ((↑|k| : ℝ) * L) ^ 2) := by
  have heq :
      (fun k : ℤ => C / ((↑|k| : ℝ) * L) ^ 2) =
        (fun k : ℤ => (C / L ^ 2) * (1 / (↑|k| : ℝ) ^ 2)) := by
    ext k
    ring
  rw [heq]
  apply Summable.mul_left
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨?_, ?_⟩ <;>
    exact ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)).congr
      fun n => by simp [abs_of_nonneg (Int.natCast_nonneg n), abs_neg]

omit d N [NeZero N] in
/-- Splitting off the `k = 0` term in the periodization sum isolates the
wrap-around tail. -/
private theorem periodizeFun_sub_eq_tsum_tail
    (L : ℝ) [Fact (0 < L)] (h : SchwartzMap ℝ ℝ) (t : ℝ) :
    periodizeFun L h t - h t =
      ∑' k : ℤ, if k = 0 then 0 else h (t + k * L) := by
  let g : ℤ → ℝ := fun k => if k = 0 then h t else 0
  let r : ℤ → ℝ := fun k => if k = 0 then 0 else h (t + k * L)
  have hs : Summable (fun k : ℤ => h (t + k * L)) := periodize_summable L h t
  have hg : Summable g := (hasSum_ite_eq (0 : ℤ) (h t)).summable
  have hr_eq : r = (fun k : ℤ => h (t + k * L)) - g := by
    funext k
    by_cases hk : k = 0 <;> simp [g, r, hk]
  have hr : Summable r := by
    rw [hr_eq]
    exact hs.sub hg
  unfold periodizeFun
  calc
    ∑' k : ℤ, h (t + k * L) - h t
      = (∑' k : ℤ, (g k + r k)) - h t := by
          rw [show (fun k : ℤ => h (t + k * L)) = fun k : ℤ => g k + r k from by
            funext k
            by_cases hk : k = 0 <;> simp [g, r, hk]]
    _ = (∑' k : ℤ, g k) + ∑' k : ℤ, r k - h t := by
          rw [← (hg.hasSum.add hr.hasSum).tsum_eq]
    _ = ∑' k : ℤ, r k := by
          simp [g, r, tsum_ite_eq]
    _ = ∑' k : ℤ, if k = 0 then 0 else h (t + k * L) := by
          rfl

omit d in
/-- Centered lattice samples lie in the fundamental window
`[-(Na)/2, (Na)/2]`. -/
private theorem abs_centered_sample_le_half_period
    (a : ℝ) (ha : 0 ≤ a) (z : ZMod N) :
    |a * (signedVal N z : ℝ)| ≤ ((N : ℝ) * a) / 2 := by
  rw [abs_mul, abs_of_nonneg ha]
  have h_abs : |(signedVal N z : ℝ)| = ((signedVal N z).natAbs : ℝ) := by
    symm
    simp
  rw [h_abs]
  have hhalf_nat : ((signedVal N z).natAbs : ℝ) ≤ (N : ℝ) / 2 := by
    rw [signedVal_natAbs_eq_min (N := N) z]
    have hmin_nat : 2 * min (ZMod.val z) (N - ZMod.val z) ≤ N := by
      have hleft :
          min (ZMod.val z) (N - ZMod.val z) ≤ ZMod.val z := Nat.min_le_left _ _
      have hright :
          min (ZMod.val z) (N - ZMod.val z) ≤ N - ZMod.val z := Nat.min_le_right _ _
      omega
    have hmin_real : (2 * min (ZMod.val z) (N - ZMod.val z) : ℝ) ≤ N := by
      exact_mod_cast hmin_nat
    nlinarith
  calc
    a * ((signedVal N z).natAbs : ℝ) ≤ a * ((N : ℝ) / 2) := by
      exact mul_le_mul_of_nonneg_left hhalf_nat ha
    _ = ((N : ℝ) * a) / 2 := by
          ring

omit d N [NeZero N] in
/-- If `t` lies in the centered fundamental window, every nonzero period shift
stays at least `|k|L/2` away from the origin. -/
private theorem centered_window_shift_abs_lower_bound
    {L t : ℝ} (hL : 0 < L) (ht : |t| ≤ L / 2)
    (k : ℤ) (hk : k ≠ 0) :
    ((↑|k| : ℝ) * L) / 2 ≤ |t + k * L| := by
  have hk_pos_nat : 0 < |k| := by
    simpa using Int.natAbs_pos.mpr hk
  have hk_ge_one : (1 : ℝ) ≤ (↑|k| : ℝ) := by
    exact_mod_cast hk_pos_nat
  have hhalf_le : L / 2 ≤ (↑|k| : ℝ) * L / 2 := by
    nlinarith
  have h_abs_kL : |(k : ℝ) * L| = (↑|k| : ℝ) * L := by
    rw [abs_mul, abs_of_pos hL]
    push_cast
    rfl
  have hmain : (↑|k| : ℝ) * L ≤ |t + k * L| + |t| := by
    calc
      (↑|k| : ℝ) * L = |(k : ℝ) * L| := h_abs_kL.symm
      _ = |(t + k * L) + (-t)| := by ring_nf
      _ ≤ |t + k * L| + |-t| := abs_add_le _ _
      _ = |t + k * L| + |t| := by rw [abs_neg]
  linarith

omit d N [NeZero N] in
/-- The universal square-summable tail constant over `ℤ`. -/
private noncomputable def intInvSqSum : ℝ :=
  ∑' k : ℤ, 1 / (↑|k| : ℝ) ^ 2

omit d N [NeZero N] in
private theorem intInvSqSum_nonneg : 0 ≤ intInvSqSum := by
  apply tsum_nonneg
  intro k
  positivity

omit d in
/-- The wrap-around error in periodizing a one-dimensional Hermite basis vector
at lattice scale `a` is quadratically small in the total period `N a`,
uniformly on centered lattice samples, provided a Schwartz decay bound of order
two is available. -/
private theorem periodizeFun_hermite_defect_abs_le_aux
    (Cψ : ℝ) (hCψ : 0 < Cψ) (r : ℕ)
    (hψ : ∀ n x,
      |schwartzHermiteBasis1D n x| ≤ Cψ * (1 + (n : ℝ)) ^ r / (1 + |x|) ^ 2)
    (n : ℕ) (a : ℝ) (ha : 0 < a) [Fact (0 < (N : ℝ) * a)] (z : ZMod N) :
    |periodizeFun ((N : ℝ) * a) (schwartzHermiteBasis1D n)
        (a * (signedVal N z : ℝ)) -
      schwartzHermiteBasis1D n (a * (signedVal N z : ℝ))| ≤
      (4 * Cψ * intInvSqSum + 1) * (1 + (n : ℝ)) ^ r / (((N : ℝ) * a) ^ 2) := by
  set L : ℝ := (N : ℝ) * a
  set t : ℝ := a * (signedVal N z : ℝ)
  have hL_pos : 0 < L := by
    dsimp [L]
    exact Fact.out
  have ht : |t| ≤ L / 2 := by
    dsimp [t, L]
    exact @abs_centered_sample_le_half_period N _ a ha.le z
  have hpt :
      ∀ k : ℤ,
        |if k = 0 then 0 else schwartzHermiteBasis1D n (t + k * L)| ≤
          4 * Cψ * (1 + (n : ℝ)) ^ r / ((↑|k| : ℝ) * L) ^ 2 := by
    intro k
    by_cases hk : k = 0
    · simp [hk]
    · have hk_pos_nat : 0 < |k| := by
        simpa using Int.natAbs_pos.mpr hk
      have hk_pos : 0 < (↑|k| : ℝ) := by
        exact_mod_cast hk_pos_nat
      have hshift :
          ((↑|k| : ℝ) * L) / 2 ≤ |t + k * L| := by
        exact centered_window_shift_abs_lower_bound hL_pos ht k hk
      have hbase :
          ((↑|k| : ℝ) * L) / 2 ≤ 1 + |t + k * L| := by
        linarith
      have hpow :
          (((↑|k| : ℝ) * L) / 2) ^ 2 ≤ (1 + |t + k * L|) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) hbase 2
      have hmain :
          |schwartzHermiteBasis1D n (t + k * L)| ≤
            4 * Cψ * (1 + (n : ℝ)) ^ r / ((↑|k| : ℝ) * L) ^ 2 := by
        calc
          |schwartzHermiteBasis1D n (t + k * L)| ≤
              Cψ * (1 + (n : ℝ)) ^ r / (1 + |t + k * L|) ^ 2 := by
                exact hψ n (t + k * L)
          _ ≤ Cψ * (1 + (n : ℝ)) ^ r / ((((↑|k| : ℝ) * L) / 2) ^ 2) := by
                apply div_le_div_of_nonneg_left
                · positivity
                · positivity
                · exact hpow
          _ = 4 * Cψ * (1 + (n : ℝ)) ^ r / ((↑|k| : ℝ) * L) ^ 2 := by
                have hkL_ne : ((↑|k| : ℝ) * L) ≠ 0 := by positivity
                field_simp [hkL_ne]
                ring
      simpa [hk] using hmain
  let F : ℤ → ℝ := fun k => if k = 0 then 0 else schwartzHermiteBasis1D n (t + k * L)
  have hdom_sum :
      Summable (fun k : ℤ => 4 * Cψ * (1 + (n : ℝ)) ^ r / ((↑|k| : ℝ) * L) ^ 2) :=
    summable_inv_int_sq_mul (4 * Cψ * (1 + (n : ℝ)) ^ r) L
  have hdom_sum' :
      Summable (fun k : ℤ => 4 * Cψ * (1 + (n : ℝ)) ^ r / ((abs (k : ℝ)) * L) ^ 2) := by
    simpa using hdom_sum
  have hnorm_sum :
      Summable (fun k : ℤ => ‖F k‖) := by
    apply Summable.of_nonneg_of_le
    · intro k
      exact norm_nonneg _
    · intro k
      simpa [F, Real.norm_eq_abs] using hpt k
    · exact hdom_sum'
  have htail :
      |periodizeFun L (schwartzHermiteBasis1D n) t - schwartzHermiteBasis1D n t| ≤
        ∑' k : ℤ, 4 * Cψ * (1 + (n : ℝ)) ^ r / ((↑|k| : ℝ) * L) ^ 2 := by
    rw [periodizeFun_sub_eq_tsum_tail (L := L) (h := schwartzHermiteBasis1D n) (t := t)]
    calc
      |∑' k : ℤ, F k| = ‖∑' k : ℤ, F k‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∑' k : ℤ, ‖F k‖ := norm_tsum_le_tsum_norm hnorm_sum
      _ ≤ ∑' k : ℤ, 4 * Cψ * (1 + (n : ℝ)) ^ r / ((↑|k| : ℝ) * L) ^ 2 := by
            apply Summable.tsum_le_tsum
            · intro k
              simpa [F, Real.norm_eq_abs] using hpt k
            · exact hnorm_sum
            · exact hdom_sum
  have hseries :
      ∑' k : ℤ, 4 * Cψ * (1 + (n : ℝ)) ^ r / ((↑|k| : ℝ) * L) ^ 2 =
        (4 * Cψ * (1 + (n : ℝ)) ^ r / L ^ 2) * intInvSqSum := by
    have heq :
        (fun k : ℤ => 4 * Cψ * (1 + (n : ℝ)) ^ r / ((↑|k| : ℝ) * L) ^ 2) =
          (fun k : ℤ => (4 * Cψ * (1 + (n : ℝ)) ^ r / L ^ 2) *
            (1 / (↑|k| : ℝ) ^ 2)) := by
      ext k
      ring
    rw [heq, tsum_mul_left]
    simp [intInvSqSum]
  calc
    |periodizeFun ((N : ℝ) * a) (schwartzHermiteBasis1D n)
        (a * (signedVal N z : ℝ)) -
      schwartzHermiteBasis1D n (a * (signedVal N z : ℝ))|
      = |periodizeFun L (schwartzHermiteBasis1D n) t -
          schwartzHermiteBasis1D n t| := by
            simp [L, t]
    _ ≤ ∑' k : ℤ, 4 * Cψ * (1 + (n : ℝ)) ^ r / ((↑|k| : ℝ) * L) ^ 2 := htail
    _ = (4 * Cψ * (1 + (n : ℝ)) ^ r / L ^ 2) * intInvSqSum := hseries
    _ = (4 * Cψ * intInvSqSum) * (1 + (n : ℝ)) ^ r / L ^ 2 := by ring
    _ ≤ (4 * Cψ * intInvSqSum + 1) * (1 + (n : ℝ)) ^ r / L ^ 2 := by
          apply div_le_div_of_nonneg_right
          · exact mul_le_mul_of_nonneg_right (by linarith [intInvSqSum_nonneg]) (by positivity)
          · positivity
    _ = (4 * Cψ * intInvSqSum + 1) * (1 + (n : ℝ)) ^ r / (((N : ℝ) * a) ^ 2) := by
          simp [L]

omit d N [NeZero N] in
/-- Uniform pointwise bound on the real lattice Fourier basis functions. -/
private theorem latticeFourierBasisFun_abs_le_sqrt_two_div
    (N : ℕ) [NeZero N] (m : ℕ) (z : ZMod N) :
    |latticeFourierBasisFun N m z| ≤ Real.sqrt (2 / N) := by
  cases m with
  | zero =>
      simp only [latticeFourierBasisFun]
      rw [abs_of_nonneg (by positivity)]
      calc
        1 / Real.sqrt ↑N
          = Real.sqrt 1 / Real.sqrt ↑N := by rw [Real.sqrt_one]
        _ ≤ Real.sqrt 2 / Real.sqrt ↑N := by
              exact div_le_div_of_nonneg_right
                (Real.sqrt_le_sqrt (by norm_num)) (Real.sqrt_nonneg _)
        _ = Real.sqrt (2 / ↑N) := by
              rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
  | succ n =>
      simp only [latticeFourierBasisFun]
      split
      · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.abs_cos_le_one _)
      · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.abs_sin_le_one _)

omit d N [NeZero N] in
/-- The coefficient-level wrap-around defect coming from periodization is
uniformly controlled by one inverse power of the total period `N a`. -/
private theorem latticeHermiteSlicePeriodizationDefect_abs_le :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℕ, ∀ (a : ℝ), 0 < a →
      ∀ (N : ℕ) [NeZero N] [Fact (0 < (N : ℝ) * a)] (n : ℕ) (m : Fin N),
        |latticeHermiteSlicePeriodizationDefect (N := N) a n m| ≤
          C * (1 + (n : ℝ)) ^ r * Real.sqrt (2 / N) / ((N : ℝ) * a) := by
  obtain ⟨Cψ, hCψ_pos, r, hψ⟩ := schwartzHermiteBasis1D_decay_two
  set Cδ : ℝ := 4 * Cψ * intInvSqSum + 1
  have hCδ_pos : 0 < Cδ := by
    dsimp [Cδ]
    nlinarith [hCψ_pos, intInvSqSum_nonneg]
  refine ⟨Cδ, hCδ_pos, r, ?_⟩
  intro a ha N _ _ n m
  set L : ℝ := (N : ℝ) * a
  unfold latticeHermiteSlicePeriodizationDefect
  calc
    |∑ z : ZMod N,
        a *
            (periodizeFun ((N : ℝ) * a) (schwartzHermiteBasis1D n)
                (a * (signedVal N z : ℝ)) -
              schwartzHermiteBasis1D n (a * (signedVal N z : ℝ))) *
          latticeFourierBasisFun N m z|
      ≤ ∑ z : ZMod N,
          |a *
              (periodizeFun ((N : ℝ) * a) (schwartzHermiteBasis1D n)
                  (a * (signedVal N z : ℝ)) -
                schwartzHermiteBasis1D n (a * (signedVal N z : ℝ))) *
            latticeFourierBasisFun N m z| := by
              exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z : ZMod N,
          a * (Cδ * (1 + (n : ℝ)) ^ r / (L ^ 2)) * Real.sqrt (2 / N) := by
            apply Finset.sum_le_sum
            intro z hz
            have hdiff :=
              periodizeFun_hermite_defect_abs_le_aux
                (N := N) Cψ hCψ_pos r hψ n a ha z
            have hφ := latticeFourierBasisFun_abs_le_sqrt_two_div N m z
            rw [abs_mul, abs_mul, abs_of_pos ha]
            have hstep1 :
                a *
                    |periodizeFun ((N : ℝ) * a) (schwartzHermiteBasis1D n)
                        (a * (signedVal N z : ℝ)) -
                      schwartzHermiteBasis1D n (a * (signedVal N z : ℝ))| ≤
                  a * (Cδ * (1 + (n : ℝ)) ^ r / (L ^ 2)) := by
              exact mul_le_mul_of_nonneg_left hdiff ha.le
            calc
              a *
                  |periodizeFun ((N : ℝ) * a) (schwartzHermiteBasis1D n)
                      (a * (signedVal N z : ℝ)) -
                    schwartzHermiteBasis1D n (a * (signedVal N z : ℝ))| *
                  |latticeFourierBasisFun N m z|
                ≤ (a * (Cδ * (1 + (n : ℝ)) ^ r / (L ^ 2))) *
                    |latticeFourierBasisFun N m z| := by
                      exact mul_le_mul_of_nonneg_right hstep1 (abs_nonneg _)
              _ ≤ (a * (Cδ * (1 + (n : ℝ)) ^ r / (L ^ 2))) *
                    Real.sqrt (2 / N) := by
                      exact mul_le_mul_of_nonneg_left hφ (by positivity)
              _ = a * (Cδ * (1 + (n : ℝ)) ^ r / (L ^ 2)) *
                    Real.sqrt (2 / N) := by
                      ring
    _ = (Finset.univ.card : ℝ) *
          (a * (Cδ * (1 + (n : ℝ)) ^ r / (L ^ 2)) * Real.sqrt (2 / N)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    _ = (N : ℝ) *
          (a * (Cδ * (1 + (n : ℝ)) ^ r / (L ^ 2)) * Real.sqrt (2 / N)) := by
            simp
    _ = Cδ * (1 + (n : ℝ)) ^ r * Real.sqrt (2 / N) / ((N : ℝ) * a) := by
          dsimp [L]
          have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
          have hL_ne : ((N : ℝ) * a) ≠ 0 := by positivity
          field_simp [hN_ne, hL_ne]

omit d N [NeZero N] in
/-- Along any mode sequence, the periodization defect tends to zero as the
total period `N a` diverges. -/
private theorem latticeHermiteSlicePeriodizationDefect_tendsto_zero
    (n : ℕ)
    (a_seq : ℕ → ℝ) (ha_pos : ∀ n, 0 < a_seq n)
    (N_seq : ℕ → ℕ) [∀ n, NeZero (N_seq n)]
    (hNa : Tendsto (fun n => (N_seq n : ℝ) * a_seq n) atTop atTop)
    (m_seq : ∀ n, Fin (N_seq n)) :
    Tendsto
      (fun n0 => show ℝ from by
        letI : Fact (0 < (N_seq n0 : ℝ) * a_seq n0) := by
          exact ⟨mul_pos (Nat.cast_pos.mpr (NeZero.pos (N_seq n0))) (ha_pos n0)⟩
        exact latticeHermiteSlicePeriodizationDefect (N := N_seq n0) (a_seq n0) n (m_seq n0))
      atTop (nhds 0) := by
  obtain ⟨Cδ, hCδ_pos, r, hδ⟩ := latticeHermiteSlicePeriodizationDefect_abs_le
  have h_inv :
      Tendsto (fun n0 => (((N_seq n0 : ℝ) * a_seq n0))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hNa
  have h_bound_tend :
      Tendsto
        (fun n0 =>
          Cδ * (1 + (n : ℝ)) ^ r * Real.sqrt 2 *
            (((N_seq n0 : ℝ) * a_seq n0))⁻¹)
        atTop (nhds 0) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      h_inv.const_mul (Cδ * (1 + (n : ℝ)) ^ r * Real.sqrt 2)
  apply squeeze_zero_norm
  · intro n0
    letI : Fact (0 < (N_seq n0 : ℝ) * a_seq n0) := by
      exact ⟨mul_pos (Nat.cast_pos.mpr (NeZero.pos (N_seq n0))) (ha_pos n0)⟩
    dsimp
    have hbase := hδ (a_seq n0) (ha_pos n0) (N_seq n0) n (m_seq n0)
    have hsqrt : Real.sqrt (2 / N_seq n0) ≤ Real.sqrt 2 := by
      have hdiv : (2 / (N_seq n0 : ℝ)) ≤ 2 := by
        have hN_pos : 0 < (N_seq n0 : ℝ) := Nat.cast_pos.mpr (NeZero.pos (N_seq n0))
        have hN_ge_one : (1 : ℝ) ≤ (N_seq n0 : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt (NeZero.pos (N_seq n0))
        rw [div_le_iff₀ hN_pos]
        nlinarith
      exact Real.sqrt_le_sqrt hdiv
    calc
      |latticeHermiteSlicePeriodizationDefect (N := N_seq n0) (a_seq n0) n (m_seq n0)|
        ≤ Cδ * (1 + (n : ℝ)) ^ r * Real.sqrt (2 / N_seq n0) /
            ((N_seq n0 : ℝ) * a_seq n0) := hbase
      _ = (Cδ * (1 + (n : ℝ)) ^ r * Real.sqrt (2 / N_seq n0)) *
            (((N_seq n0 : ℝ) * a_seq n0))⁻¹ := by
              rw [div_eq_mul_inv]
      _ ≤ (Cδ * (1 + (n : ℝ)) ^ r * Real.sqrt 2) *
            (((N_seq n0 : ℝ) * a_seq n0))⁻¹ := by
              apply mul_le_mul_of_nonneg_right
              · gcongr
              · exact inv_nonneg.mpr (le_of_lt (show 0 < (N_seq n0 : ℝ) * a_seq n0 from Fact.out))
  · simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      h_bound_tend

omit d N [NeZero N] in
/-- The sampled Hermite slice coefficient differs from the corresponding
large-period circle DFT coefficient by a term that vanishes as `N a → ∞`. -/
private theorem latticeDFTCoeff_periodizedHermite_sub_slice_tendsto_zero
    (n : ℕ)
    (a_seq : ℕ → ℝ) (ha_pos : ∀ n, 0 < a_seq n)
    (N_seq : ℕ → ℕ) [∀ n, NeZero (N_seq n)]
    (hNa : Tendsto (fun n => (N_seq n : ℝ) * a_seq n) atTop atTop)
    (m_seq : ∀ n, Fin (N_seq n)) :
    Tendsto
      (fun n0 => show ℝ from by
        letI : Fact (0 < (N_seq n0 : ℝ) * a_seq n0) := by
          exact ⟨mul_pos (Nat.cast_pos.mpr (NeZero.pos (N_seq n0))) (ha_pos n0)⟩
        exact
          latticeDFTCoeff1d ((N_seq n0 : ℝ) * a_seq n0) (N_seq n0)
            ((Real.sqrt (a_seq n0)) •
              periodizeCLM ((N_seq n0 : ℝ) * a_seq n0) (schwartzHermiteBasis1D n))
            (m_seq n0) -
          latticeHermiteSliceCoeff (N := N_seq n0) (a_seq n0) n (m_seq n0))
      atTop (nhds 0) := by
  have hdefect :=
    latticeHermiteSlicePeriodizationDefect_tendsto_zero
      (n := n) a_seq ha_pos N_seq hNa m_seq
  refine hdefect.congr' ?_
  filter_upwards with n0
  letI : Fact (0 < (N_seq n0 : ℝ) * a_seq n0) := by
    exact ⟨mul_pos (Nat.cast_pos.mpr (NeZero.pos (N_seq n0))) (ha_pos n0)⟩
  dsimp
  rw [latticeDFTCoeff_periodizedHermite_eq_slice_add_defect
    (N := N_seq n0) (a := a_seq n0) (ha := ha_pos n0) (n := n) (m := m_seq n0)]
  ring

omit d N [NeZero N] in
/-- The peeled one-dimensional Hermite slice DFT coefficients are uniformly
controlled by polynomial growth in the Hermite index and the expected
`N^{-1/2}` lattice normalization. -/
private theorem latticeHermiteSliceCoeff_abs_le :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℕ, ∀ (a : ℝ), 0 < a → a ≤ 1 →
      ∀ n (N : ℕ) [NeZero N] (m : Fin N),
        |latticeHermiteSliceCoeff (N := N) a n m| ≤
          C * (1 + (n : ℝ)) ^ r * Real.sqrt (2 / N) := by
  obtain ⟨Cψ, hCψ_pos, r, hψ⟩ := schwartzHermiteBasis1D_decay_two
  refine ⟨3 * Cψ, by positivity, r, ?_⟩
  intro a ha ha1 n N _ m
  have hsum := one_d_zmod_bound N a ha ha1
  unfold latticeHermiteSliceCoeff
  calc
    |∑ z : ZMod N,
        a * schwartzHermiteBasis1D n (a * (signedVal N z : ℝ)) *
          latticeFourierBasisFun N m z|
      ≤ ∑ z : ZMod N,
          |a * schwartzHermiteBasis1D n (a * (signedVal N z : ℝ)) *
            latticeFourierBasisFun N m z| := by
              exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z : ZMod N,
          Cψ * (1 + (n : ℝ)) ^ r *
            (a / (1 + a * ((signedVal N z).natAbs : ℝ)) ^ 2) *
            Real.sqrt (2 / N) := by
              apply Finset.sum_le_sum
              intro z hz
              have hψz :
                  |schwartzHermiteBasis1D n (a * (signedVal N z : ℝ))| ≤
                    Cψ * (1 + (n : ℝ)) ^ r /
                      (1 + a * ((signedVal N z).natAbs : ℝ)) ^ 2 := by
                have h_cast_abs : |(signedVal N z : ℝ)| = ((signedVal N z).natAbs : ℝ) := by
                  symm
                  simp
                have habs_arg : |a * (signedVal N z : ℝ)| = a * ((signedVal N z).natAbs : ℝ) := by
                  rw [abs_mul, abs_of_pos ha, h_cast_abs]
                simpa [habs_arg] using hψ n (a * (signedVal N z : ℝ))
              have hφz := latticeFourierBasisFun_abs_le_sqrt_two_div N m z
              rw [abs_mul, abs_mul, abs_of_pos ha]
              have hstep1 :
                  a * |schwartzHermiteBasis1D n (a * (signedVal N z : ℝ))| ≤
                    a * (Cψ * (1 + (n : ℝ)) ^ r /
                      (1 + a * ((signedVal N z).natAbs : ℝ)) ^ 2) := by
                exact mul_le_mul_of_nonneg_left hψz ha.le
              calc
                a * |schwartzHermiteBasis1D n (a * (signedVal N z : ℝ))| *
                    |latticeFourierBasisFun N m z|
                  ≤ (a * (Cψ * (1 + (n : ℝ)) ^ r /
                        (1 + a * ((signedVal N z).natAbs : ℝ)) ^ 2)) *
                      |latticeFourierBasisFun N m z| := by
                        exact mul_le_mul_of_nonneg_right hstep1 (abs_nonneg _)
                _ ≤ (a * (Cψ * (1 + (n : ℝ)) ^ r /
                      (1 + a * ((signedVal N z).natAbs : ℝ)) ^ 2)) *
                      Real.sqrt (2 / N) := by
                        exact mul_le_mul_of_nonneg_left hφz (by positivity)
                _ = Cψ * (1 + (n : ℝ)) ^ r *
                      (a / (1 + a * ((signedVal N z).natAbs : ℝ)) ^ 2) *
                      Real.sqrt (2 / N) := by
                        ring
    _ = ∑ z : ZMod N,
          (Cψ * (1 + (n : ℝ)) ^ r * Real.sqrt (2 / N)) *
            (a / (1 + a * ((signedVal N z).natAbs : ℝ)) ^ 2) := by
            apply Finset.sum_congr rfl
            intro z hz
            ring
    _ = Cψ * (1 + (n : ℝ)) ^ r * Real.sqrt (2 / N) *
          ∑ z : ZMod N, a / (1 + a * ((signedVal N z).natAbs : ℝ)) ^ 2 := by
            rw [← Finset.mul_sum]
    _ ≤ Cψ * (1 + (n : ℝ)) ^ r * Real.sqrt (2 / N) * 3 := by
          exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (3 * Cψ) * (1 + (n : ℝ)) ^ r * Real.sqrt (2 / N) := by
          ring

omit d N [NeZero N] in
/-- The purely outer Fourier spectral factor in the peeled two-dimensional
expression carries one full `N⁻¹` of lattice normalization. -/
private theorem latticeHermiteSliceSpectralFactor_abs_le_two_div_card :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℕ, ∀ (a : ℝ), 0 < a → a ≤ 1 →
      ∀ i j (N : ℕ) [NeZero N] (m : Fin N),
        |latticeHermiteSliceCoeff (N := N) a i m *
            latticeHermiteSliceCoeff (N := N) a j m /
            latticeFourierNormSq N m| ≤
          C * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r * (2 / N) := by
  obtain ⟨Cψ, hCψ_pos, r, hψ⟩ := latticeHermiteSliceCoeff_abs_le
  refine ⟨Cψ ^ 2, by positivity, r, ?_⟩
  intro a ha ha1 i j N _ m
  set ci : ℝ := latticeHermiteSliceCoeff (N := N) a i m
  set cj : ℝ := latticeHermiteSliceCoeff (N := N) a j m
  have hi := hψ a ha ha1 i N m
  have hj := hψ a ha ha1 j N m
  have hnorm_ge : 1 ≤ latticeFourierNormSq N m := latticeFourierNormSq_ge_one N m m.isLt
  have hdiv :
      |ci * cj / latticeFourierNormSq N m| ≤ |ci * cj| := by
    rw [abs_div]
    exact div_le_self (abs_nonneg _) (by
      rw [abs_of_nonneg (le_of_lt (latticeFourierNormSq_pos N m m.isLt))]
      exact hnorm_ge)
  have hsqrt_sq :
      Real.sqrt (2 / N) * Real.sqrt (2 / N) = 2 / N := by
    rw [← sq, Real.sq_sqrt]
    positivity
  calc
    |latticeHermiteSliceCoeff (N := N) a i m *
        latticeHermiteSliceCoeff (N := N) a j m /
        latticeFourierNormSq N m|
      = |ci * cj / latticeFourierNormSq N m| := by simp [ci, cj]
    _ ≤ |ci * cj| := hdiv
    _ = |ci| * |cj| := by rw [abs_mul]
    _ ≤ (Cψ * (1 + (i : ℝ)) ^ r * Real.sqrt (2 / N)) *
          (Cψ * (1 + (j : ℝ)) ^ r * Real.sqrt (2 / N)) := by
            exact mul_le_mul hi hj (abs_nonneg _) (by positivity)
    _ = Cψ * Cψ * ((1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r) *
          (Real.sqrt (2 / N) * Real.sqrt (2 / N)) := by
            ring
    _ = Cψ ^ 2 * (1 + (i : ℝ)) ^ r * (1 + (j : ℝ)) ^ r * (2 / N) := by
          rw [hsqrt_sq]
          ring

omit d N [NeZero N] in
/-- For fixed basis indices, each peeled outer effective-mass term is controlled
by the discrete massive kernel `(2/N) * (λ_m + m²)⁻¹`. This is the lattice
counterpart of the continuum kernel majorant proved later in the file. -/
private theorem latticeHermiteEffectiveMassTerm_abs_le_two_div_card_inv
    (mass : ℝ) (hmass : 0 < mass) (i j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ), 0 < a → a ≤ 1 →
      ∀ (N : ℕ) [NeZero N] (m0 : Fin N),
        |latticeHermiteEffectiveMassTerm (N := N) a mass i j m0| ≤
          C * (2 / N) * (latticeEigenvalue1d N a m0 + mass ^ 2)⁻¹ := by
  obtain ⟨Couter, hCouter_pos, router, houter⟩ :=
    latticeHermiteSliceSpectralFactor_abs_le_two_div_card
  obtain ⟨Cinner, hCinner_pos, rinner, hinner⟩ :=
    latticeHermiteSliceBilinear_effective_mass_bound
  set K : ℝ :=
    Couter * (1 + ((Nat.unpair i).1 : ℝ)) ^ router *
      (1 + ((Nat.unpair j).1 : ℝ)) ^ router *
      (Cinner * (1 + ((Nat.unpair i).2 : ℝ)) ^ rinner *
        (1 + ((Nat.unpair j).2 : ℝ)) ^ rinner)
  refine ⟨K, by
    dsimp [K]
    positivity, ?_⟩
  intro a ha ha1 N _ m0
  set shift : ℝ := latticeEigenvalue1d N a m0 + mass ^ 2
  have hshift_pos : 0 < shift := by
    dsimp [shift]
    exact add_pos_of_nonneg_of_pos
      (latticeEigenvalue1d_nonneg N a m0) (sq_pos_of_pos hmass)
  have houter' :=
    houter a ha ha1 (Nat.unpair i).1 (Nat.unpair j).1 N m0
  have hinner' :=
    hinner shift hshift_pos (Nat.unpair i).2 (Nat.unpair j).2 a ha ha1 N
  have hinner_eq :
      latticeHermiteSliceBilinear (N := N) a shift (Nat.unpair i).2 (Nat.unpair j).2 =
        latticeGreenBilinear 1 N a (Real.sqrt shift)
          (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).2)
          (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).2) := by
    exact latticeHermiteSliceBilinear_eq_latticeGreenBilinear_1d
      (N := N) (a := a) (massShift := shift) ha hshift_pos
      (Nat.unpair i).2 (Nat.unpair j).2
  have hinner_green :
      |latticeGreenBilinear 1 N a (Real.sqrt shift)
          (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).2)
          (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).2)| ≤
        Cinner * (Real.sqrt shift)⁻¹ ^ 2 *
          (1 + ((Nat.unpair i).2 : ℝ)) ^ rinner *
          (1 + ((Nat.unpair j).2 : ℝ)) ^ rinner := by
    simpa [shift, hinner_eq] using
      hinner'
  have hsqrt_inv : (Real.sqrt shift)⁻¹ ^ 2 = shift⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hshift_pos.le]
  calc
    |latticeHermiteEffectiveMassTerm (N := N) a mass i j m0|
      = |(latticeHermiteSliceCoeff (N := N) a (Nat.unpair i).1 m0 *
            latticeHermiteSliceCoeff (N := N) a (Nat.unpair j).1 m0 /
            latticeFourierNormSq N m0) *
          latticeGreenBilinear 1 N a (Real.sqrt shift)
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).2)
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).2)| := by
              simp [latticeHermiteEffectiveMassTerm, shift]
    _ = |latticeHermiteSliceCoeff (N := N) a (Nat.unpair i).1 m0 *
            latticeHermiteSliceCoeff (N := N) a (Nat.unpair j).1 m0 /
            latticeFourierNormSq N m0| *
          |latticeGreenBilinear 1 N a (Real.sqrt shift)
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).2)
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).2)| := by
              rw [abs_mul]
    _ ≤ (Couter * (1 + ((Nat.unpair i).1 : ℝ)) ^ router *
            (1 + ((Nat.unpair j).1 : ℝ)) ^ router * (2 / N)) *
          (Cinner * (Real.sqrt shift)⁻¹ ^ 2 *
            (1 + ((Nat.unpair i).2 : ℝ)) ^ rinner *
            (1 + ((Nat.unpair j).2 : ℝ)) ^ rinner) := by
              exact mul_le_mul houter' hinner_green (abs_nonneg _) (by positivity)
    _ = K * (2 / N) * shift⁻¹ := by
          rw [hsqrt_inv]
          dsimp [K]
          ring
    _ = K * (2 / N) * (latticeEigenvalue1d N a m0 + mass ^ 2)⁻¹ := by
          simp [shift]

omit d N [NeZero N] in
/-- The peeled outer mode sum is uniformly absolutely bounded once the
`N⁻¹` spectral factor is combined with the mass lower bound `λ_m + m² ≥ m²`. -/
private theorem latticeHermiteEffectiveMassSum_abs_uniform
    (mass : ℝ) (hmass : 0 < mass) (i j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ), 0 < a → a ≤ 1 →
      ∀ (N : ℕ) [NeZero N],
        ∑ m0 : Fin N, |latticeHermiteEffectiveMassTerm (N := N) a mass i j m0| ≤ C := by
  obtain ⟨K, hK_pos, hK⟩ :=
    latticeHermiteEffectiveMassTerm_abs_le_two_div_card_inv (mass := mass) hmass i j
  refine ⟨2 * K * mass⁻¹ ^ 2 + 1, by positivity, ?_⟩
  intro a ha ha1 N _ 
  have hm2_pos : 0 < mass ^ 2 := sq_pos_of_pos hmass
  have hm2_inv : (mass ^ 2)⁻¹ = mass⁻¹ ^ 2 := by
    rw [sq, mul_inv_rev, pow_two]
  have hterm :
      ∀ m0 : Fin N,
        |latticeHermiteEffectiveMassTerm (N := N) a mass i j m0| ≤
          K * (2 / N) * mass⁻¹ ^ 2 := by
    intro m0
    have hbase := hK a ha ha1 N m0
    have hshift_ge : mass ^ 2 ≤ latticeEigenvalue1d N a m0 + mass ^ 2 := by
      nlinarith [latticeEigenvalue1d_nonneg N a m0]
    have hshift_inv :
        (latticeEigenvalue1d N a m0 + mass ^ 2)⁻¹ ≤ mass⁻¹ ^ 2 := by
      calc
        (latticeEigenvalue1d N a m0 + mass ^ 2)⁻¹ ≤ (mass ^ 2)⁻¹ := by
          simpa [one_div] using one_div_le_one_div_of_le hm2_pos hshift_ge
        _ = mass⁻¹ ^ 2 := hm2_inv
    calc
      |latticeHermiteEffectiveMassTerm (N := N) a mass i j m0|
        ≤ K * (2 / N) * (latticeEigenvalue1d N a m0 + mass ^ 2)⁻¹ := hbase
      _ ≤ K * (2 / N) * mass⁻¹ ^ 2 := by
            exact mul_le_mul_of_nonneg_left hshift_inv (by positivity)
  calc
    ∑ m0 : Fin N, |latticeHermiteEffectiveMassTerm (N := N) a mass i j m0|
      ≤ ∑ m0 : Fin N, K * (2 / N) * mass⁻¹ ^ 2 := by
          exact Finset.sum_le_sum fun m0 _ => hterm m0
    _ = (Finset.univ.card : ℝ) * (K * (2 / N) * mass⁻¹ ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (N : ℝ) * (K * (2 / N) * mass⁻¹ ^ 2) := by
          simp
    _ = 2 * K * mass⁻¹ ^ 2 := by
          have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
          field_simp [hN_ne]
    _ ≤ 2 * K * mass⁻¹ ^ 2 + 1 := by
          linarith

/-! ### Right-continuous bilinear forms for the DM extension theorem -/

private noncomputable def continuumEvalCLM (x : EuclideanSpace ℝ (Fin d)) :
    ContinuumTestFunction d →L[ℝ] ℝ :=
  SchwartzMap.mkCLMtoNormedSpace (fun f => f x)
    (fun f g => by simp [SchwartzMap.add_apply])
    (fun a f => by simp [SchwartzMap.smul_apply])
    ⟨{(0, 0)}, 1, zero_le_one, fun f => by
      simp only [one_mul, Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply]
      exact SchwartzMap.norm_le_seminorm ℝ f x⟩

@[simp] private theorem continuumEvalCLM_apply
    (x : EuclideanSpace ℝ (Fin d)) (f : ContinuumTestFunction d) :
    continuumEvalCLM (d := d) x f = f x := by
  simp [continuumEvalCLM, SchwartzMap.mkCLMtoNormedSpace]

private noncomputable def latticeModeCoeffCLM (a mass : ℝ)
    (k : FinLatticeSites d N) :
    ContinuumTestFunction d →L[ℝ] ℝ :=
  ∑ x : FinLatticeSites d N,
    (a ^ d * (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) •
      continuumEvalCLM (d := d) (physicalPosition d N a x)

@[simp] private theorem latticeModeCoeffCLM_apply
    (a mass : ℝ) (k : FinLatticeSites d N) (f : ContinuumTestFunction d) :
    latticeModeCoeffCLM (d := d) (N := N) a mass k f =
      ∑ x : FinLatticeSites d N,
        (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
          latticeTestField d N a f x := by
  simp [latticeModeCoeffCLM, latticeTestField, evalAtSite, continuumEvalCLM_apply, smul_eq_mul,
    mul_assoc]
  apply Finset.sum_congr rfl
  intro x hx
  ring

private noncomputable def latticeGreenBilinearRightCLM
    (a mass : ℝ) (f : ContinuumTestFunction d) :
    ContinuumTestFunction d →L[ℝ] ℝ :=
  ∑ k : FinLatticeSites d N,
    ((massEigenvalues d N a mass k)⁻¹ *
      (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
        latticeTestField d N a f x)) •
      latticeModeCoeffCLM (d := d) (N := N) a mass k

@[simp] private theorem latticeGreenBilinearRightCLM_apply
    (a mass : ℝ) (f g : ContinuumTestFunction d) :
    latticeGreenBilinearRightCLM (d := d) (N := N) a mass f g =
      latticeGreenBilinear d N a mass f g := by
  simp [latticeGreenBilinearRightCLM, latticeGreenBilinear, latticeModeCoeffCLM_apply, mul_assoc,
    mul_left_comm, mul_comm]

private theorem latticeGreenBilinear_symm
    (a mass : ℝ) (f g : ContinuumTestFunction d) :
    latticeGreenBilinear d N a mass f g =
      latticeGreenBilinear d N a mass g f := by
  unfold latticeGreenBilinear
  congr 1
  ext k
  ring

private def continuumKernel (mass : ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun k =>
    (2 * Real.pi) ^ (-(d : ℤ)) / (‖k‖ ^ 2 + mass ^ 2)

private theorem continuumKernel_eq_scaled (mass : ℝ) (hmass : 0 < mass) :
    continuumKernel d mass =
      fun k =>
        (2 * Real.pi) ^ (-(d : ℤ)) * mass⁻¹ ^ 2 *
          (1 + ‖(mass⁻¹ : ℝ) • k‖ ^ 2) ^ (-1 : ℝ) := by
  funext k
  have hmass_ne : mass ≠ 0 := ne_of_gt hmass
  have hnorm : ‖(mass⁻¹ : ℝ) • k‖ ^ 2 = mass⁻¹ ^ 2 * ‖k‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmass)]
    ring
  unfold continuumKernel
  rw [hnorm]
  have haux : 1 + mass⁻¹ ^ 2 * ‖k‖ ^ 2 = (mass ^ 2 + ‖k‖ ^ 2) / mass ^ 2 := by
    field_simp [hmass_ne]
  rw [haux]
  field_simp [hmass_ne]
  ring_nf

private theorem continuumKernel_hasTemperateGrowth (mass : ℝ) (hmass : 0 < mass) :
    (continuumKernel d mass).HasTemperateGrowth := by
  rw [continuumKernel_eq_scaled (d := d) mass hmass]
  have hconst :
      (fun _ : EuclideanSpace ℝ (Fin d) =>
        (2 * Real.pi) ^ (-(d : ℤ)) * mass⁻¹ ^ 2).HasTemperateGrowth := by
    fun_prop
  have hbase :
      (fun x : EuclideanSpace ℝ (Fin d) => (1 + ‖x‖ ^ 2) ^ (-1 : ℝ)).HasTemperateGrowth := by
    fun_prop
  have hscale :
      (fun k : EuclideanSpace ℝ (Fin d) => (mass⁻¹ : ℝ) • k).HasTemperateGrowth := by
    fun_prop
  exact hconst.mul (hbase.comp hscale)

private def continuumGreenWeight (mass : ℝ) (f : ContinuumTestFunction d) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun k => continuumKernel d mass k * f k

private theorem continuumGreenWeight_hasTemperateGrowth
    (mass : ℝ) (hmass : 0 < mass) (f : ContinuumTestFunction d) :
    (continuumGreenWeight d mass f).HasTemperateGrowth := by
  unfold continuumGreenWeight
  exact (continuumKernel_hasTemperateGrowth (d := d) mass hmass).mul f.hasTemperateGrowth

private noncomputable def continuumGreenBilinearRightCLM
    (mass : ℝ) (hmass : 0 < mass) (f : ContinuumTestFunction d) :
    ContinuumTestFunction d →L[ℝ] ℝ :=
  (SchwartzMap.integralCLM ℝ
      (volume : Measure (EuclideanSpace ℝ (Fin d)))).comp
    (SchwartzMap.smulLeftCLM ℝ (continuumGreenWeight d mass f))

@[simp] private theorem continuumGreenBilinearRightCLM_apply
    (mass : ℝ) (hmass : 0 < mass) (f g : ContinuumTestFunction d) :
    continuumGreenBilinearRightCLM (d := d) mass hmass f g =
      continuumGreenBilinear d mass f g := by
  rw [continuumGreenBilinearRightCLM, ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply,
    SchwartzMap.smulLeftCLM_apply (continuumGreenWeight_hasTemperateGrowth (d := d) mass hmass f)]
  unfold continuumGreenWeight continuumGreenBilinear continuumKernel
  have hpointwise :
      (fun x : EuclideanSpace ℝ (Fin d) =>
        ((2 * Real.pi) ^ (-(d : ℤ)) / (‖x‖ ^ 2 + mass ^ 2) * f x) • g x) =
      fun x => (2 * Real.pi) ^ (-(d : ℤ)) * (f x * g x / (‖x‖ ^ 2 + mass ^ 2)) := by
    funext x
    have hden : ‖x‖ ^ 2 + mass ^ 2 ≠ 0 := by
      nlinarith [sq_nonneg ‖x‖, sq_pos_of_pos hmass]
    simp [smul_eq_mul]
    field_simp [hden]
  rw [hpointwise, integral_const_mul]
  rfl

private theorem continuumGreenBilinear_symm
    (mass : ℝ) (f g : ContinuumTestFunction d) :
    continuumGreenBilinear d mass f g =
      continuumGreenBilinear d mass g f := by
  unfold continuumGreenBilinear
  congr 1
  apply integral_congr_ae
  filter_upwards with k
  ring

omit d N [NeZero N] in
/-- Snoc followed by init recovers the original Euclidean point in the lower
dimension. -/
private theorem euclideanInit_euclideanSnoc_succ
    (d : ℕ) (y : ContinuumSpaceTime (d + 1)) (t : ℝ) :
    euclideanInit (d + 1) (euclideanSnoc (d + 1) y t) = y := by
  apply (WithLp.equiv 2 _).injective
  simp [euclideanInit, euclideanSnoc, Fin.snoc_castSucc]

omit d N [NeZero N] in
/-- The Euclidean norm of a snoc'd point splits into the lower-dimensional norm
square plus the last-coordinate square. -/
private theorem euclideanSnoc_norm_sq_succ
    (d : ℕ) (y : ContinuumSpaceTime (d + 1)) (t : ℝ) :
    ‖euclideanSnoc (d + 1) y t‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2 := by
  have hlast : (euclideanSnoc (d + 1) y t) (Fin.last (d + 1)) = t := by
    simp [euclideanSnoc, WithLp.equiv_symm_apply, Fin.snoc]
  have hcast : ∀ j : Fin (d + 1), (euclideanSnoc (d + 1) y t) (Fin.castSucc j) = y j := by
    intro j
    simp [euclideanSnoc, WithLp.equiv_symm_apply, Fin.snoc_castSucc]
  simp only [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  rw [show ∑ i : Fin (d + 2), ‖(euclideanSnoc (d + 1) y t) i‖ ^ 2 =
      (∑ j : Fin (d + 1), ‖(euclideanSnoc (d + 1) y t) (Fin.castSucc j)‖ ^ 2) +
        ‖(euclideanSnoc (d + 1) y t) (Fin.last (d + 1))‖ ^ 2 from
      Fin.sum_univ_castSucc _]
  rw [hlast, Real.norm_eq_abs, sq_abs]
  have hsum :
      ∑ j : Fin (d + 1), ‖(euclideanSnoc (d + 1) y t) (Fin.castSucc j)‖ ^ 2 =
        ∑ j : Fin (d + 1), ‖y j‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hcast]
  rw [hsum]

omit d N [NeZero N] in
/-- Under the `Fin.snoc` splitting of coordinates, the `(d+2)`-dimensional
continuum basis vector factors into its lower-dimensional basis part and a
one-dimensional Hermite factor. -/
private theorem continuumBasisSuccSucc_apply_snoc_succ
    (d : ℕ) (n : ℕ) (y : ContinuumSpaceTime (d + 1)) (t : ℝ) :
    continuumBasisSuccSucc d n (euclideanSnoc (d + 1) y t) =
      DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 1)) (Nat.unpair n).1 y *
        schwartzHermiteBasis1D (Nat.unpair n).2 t := by
  letI : Fact (0 < d + 1) := ⟨by positivity⟩
  letI : Fact (0 < d + 2) := ⟨by positivity⟩
  have hmain :
      DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 2)) n
        (euclideanSnoc (d + 1) y t) =
        hermiteFunctionNd (d + 2) ((multiIndexEquiv (d + 1)).symm n)
          (euclideanSnoc (d + 1) y t) := by
    simpa using
      (continuum_basis_apply_eq_hermite
        (d := d + 1) (n := n) (x := euclideanSnoc (d + 1) y t))
  have hmain' :
      continuumBasisSuccSucc d n (euclideanSnoc (d + 1) y t) =
        hermiteFunctionNd (d + 2) ((multiIndexEquiv (d + 1)).symm n)
          (euclideanSnoc (d + 1) y t) := by
    simpa [continuumBasisSuccSucc] using hmain
  rw [hmain', hermiteFunctionNd_unpair (d := d)]
  rw [euclideanInit_euclideanSnoc_succ (d := d)]
  have hy :
      hermiteFunctionNd (d + 1) ((multiIndexEquiv d).symm (Nat.unpair n).1) y =
        DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 1)) (Nat.unpair n).1 y := by
    simpa using
      (continuum_basis_apply_eq_hermite
        (d := d) (n := (Nat.unpair n).1) (x := y)).symm
  have hlast : (euclideanSnoc (d + 1) y t) (Fin.last (d + 1)) = t := by
    simp [euclideanSnoc, WithLp.equiv_symm_apply, Fin.snoc]
  rw [hy, hlast]
  rw [schwartzHermiteBasis1D_apply]
  rfl

omit d N [NeZero N] in
/-- In one Euclidean dimension, the norm square is the square of the unique
coordinate. -/
private theorem continuumSpaceTime_one_norm_sq (x : ContinuumSpaceTime 1) :
    ‖x‖ ^ 2 = (x 0) ^ 2 := by
  simp only [EuclideanSpace.norm_eq, Fin.sum_univ_one]
  rw [Real.sq_sqrt]
  · simp [Real.norm_eq_abs]
  · positivity

omit d N [NeZero N] in
/-- Snoc followed by init recovers the original one-dimensional Euclidean point. -/
private theorem euclideanInit_euclideanSnoc_one
    (y : ContinuumSpaceTime 1) (t : ℝ) :
    euclideanInit 1 (euclideanSnoc 1 y t) = y := by
  apply (WithLp.equiv 2 _).injective
  simp [euclideanInit, euclideanSnoc, Fin.snoc_castSucc]

omit d N [NeZero N] in
/-- The Euclidean norm of a snoc'd two-dimensional point splits into the
first-coordinate norm square plus the last-coordinate square. -/
private theorem euclideanSnoc_norm_sq_one
    (y : ContinuumSpaceTime 1) (t : ℝ) :
    ‖euclideanSnoc 1 y t‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2 := by
  have hlast : (euclideanSnoc 1 y t) (Fin.last 1) = t := by
    simp [euclideanSnoc, WithLp.equiv_symm_apply, Fin.snoc]
  have hcast : ∀ j : Fin 1, (euclideanSnoc 1 y t) (Fin.castSucc j) = y j := by
    intro j
    simp [euclideanSnoc, WithLp.equiv_symm_apply, Fin.snoc_castSucc]
  simp only [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  rw [show ∑ i : Fin 2, ‖(euclideanSnoc 1 y t) i‖ ^ 2 =
      (∑ j : Fin 1, ‖(euclideanSnoc 1 y t) (Fin.castSucc j)‖ ^ 2) +
        ‖(euclideanSnoc 1 y t) (Fin.last 1)‖ ^ 2 from
      Fin.sum_univ_castSucc _]
  rw [hlast, Real.norm_eq_abs, sq_abs]
  have hsum :
      ∑ j : Fin 1, ‖(euclideanSnoc 1 y t) (Fin.castSucc j)‖ ^ 2 =
        ∑ j : Fin 1, ‖y j‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hcast]
  rw [hsum]

omit d N [NeZero N] in
/-- On points written as `(y,t)`, the two-dimensional basis vector factors into
the first Hermite block evaluated at `y` and the last 1D Hermite factor
evaluated at `t`. -/
private theorem continuumBasisSuccSucc_apply_snoc
    (n : ℕ) (y : ContinuumSpaceTime 1) (t : ℝ) :
    continuumBasisSuccSucc 0 n (euclideanSnoc 1 y t) =
      DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair n).1 y *
        schwartzHermiteBasis1D (Nat.unpair n).2 t := by
  letI : Fact (0 < 1) := ⟨by positivity⟩
  letI : Fact (0 < 2) := ⟨by positivity⟩
  have hmain :
      DyninMityaginSpace.basis (E := ContinuumTestFunction 2) n
        (euclideanSnoc 1 y t) =
        hermiteFunctionNd 2 ((multiIndexEquiv 1).symm n) (euclideanSnoc 1 y t) := by
    simpa using
      (continuum_basis_apply_eq_hermite (d := 1) (n := n) (x := euclideanSnoc 1 y t))
  have hmain' :
      continuumBasisSuccSucc 0 n (euclideanSnoc 1 y t) =
        hermiteFunctionNd 2 ((multiIndexEquiv 1).symm n) (euclideanSnoc 1 y t) := by
    simpa [continuumBasisSuccSucc] using hmain
  rw [hmain']
  rw [hermiteFunctionNd_unpair (d := 0)]
  rw [euclideanInit_euclideanSnoc_one]
  have hy :
      hermiteFunctionNd 1 ((multiIndexEquiv 0).symm (Nat.unpair n).1) y =
        DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair n).1 y := by
    simpa [hermiteFunctionNd, multiIndexEquiv, schwartzHermiteBasis1D_apply] using
      (continuum_basis_apply_eq_hermite1D (n := (Nat.unpair n).1) (x := y)).symm
  have hlast : (euclideanSnoc 1 y t) (Fin.last 1) = t := by
    simp [euclideanSnoc, WithLp.equiv_symm_apply, Fin.snoc]
  rw [hy, hlast]
  simp [schwartzHermiteBasis1D_apply]

omit d N [NeZero N] in
/-- The one-dimensional continuum basis Green form is the weighted real-line
integral against the classical Hermite basis. -/
private theorem continuumGreenBilinear_basis_eq_weighted_real_integral_1d
    (mass : ℝ) (i j : ℕ) :
    continuumGreenBilinear 1 mass
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i)
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) j) =
      ∫ t : ℝ,
        (2 * Real.pi) ^ (-(1 : ℤ)) *
          (schwartzHermiteBasis1D i t * schwartzHermiteBasis1D j t /
            (t ^ 2 + mass ^ 2)) := by
  letI : Fact (0 < 1) := ⟨by positivity⟩
  unfold continuumGreenBilinear
  rw [← integral_const_mul]
  rw [← euclideanFin1MeasEquiv_mp.integral_comp']
  congr 1
  ext x
  rw [continuumSpaceTime_one_norm_sq]
  change (2 * Real.pi) ^ (-(1 : ℤ)) *
      ((DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i x) *
        (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) j x) /
        (x 0 ^ 2 + mass ^ 2)) =
    (2 * Real.pi) ^ (-(1 : ℤ)) *
      (schwartzHermiteBasis1D i (euclideanFin1MeasEquiv x) *
        schwartzHermiteBasis1D j (euclideanFin1MeasEquiv x) /
        (euclideanFin1MeasEquiv x ^ 2 + mass ^ 2))
  have hi :
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i) x =
        schwartzHermiteBasis1D i (euclideanFin1MeasEquiv x) := by
    simpa [euclideanFin1MeasEquiv_apply] using
      (continuum_basis_apply_eq_hermite1D (n := i) (x := x))
  have hj :
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) j) x =
        schwartzHermiteBasis1D j (euclideanFin1MeasEquiv x) := by
    simpa [euclideanFin1MeasEquiv_apply] using
      (continuum_basis_apply_eq_hermite1D (n := j) (x := x))
  rw [hi, hj]
  simp [euclideanFin1MeasEquiv_apply]

omit d N [NeZero N] in
/-- The continuum analogue of `latticeBasisIteratedSliceSum`: after peeling one
coordinate, the `(d+2)`-dimensional basis Green form becomes an outer
`(d+1)`-dimensional basis factor times a one-dimensional effective-mass Green
form. -/
private def continuumBasisIteratedSliceIntegrand
    (d : ℕ) [Fact (0 < d + 1)] (mass : ℝ) (i j : ℕ)
    (y : ContinuumSpaceTime (d + 1)) : ℝ :=
  (2 * Real.pi) ^ (-(((d + 1 : ℕ) : ℤ))) *
    DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 1)) (Nat.unpair i).1 y *
    DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 1)) (Nat.unpair j).1 y *
    continuumGreenBilinear 1 (Real.sqrt (‖y‖ ^ 2 + mass ^ 2))
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).2)
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).2)

omit d N [NeZero N] in
/-- Continuum `Fin.snoc` recursion for basis Green forms in full generality.
This is the continuum counterpart of
`latticeGreenBilinear_basis_eq_iterated_slice_sum`. -/
private theorem continuumGreenBilinear_basis_eq_effective_mass_integral_succsucc
    (d : ℕ) [Fact (0 < d + 1)] (mass : ℝ) (hmass : 0 < mass) (i j : ℕ) :
    continuumGreenBilinear (d + 2) mass
      (continuumBasisSuccSucc d i)
      (continuumBasisSuccSucc d j) =
      ∫ y : ContinuumSpaceTime (d + 1),
        continuumBasisIteratedSliceIntegrand d mass i j y := by
  letI : Fact (0 < d + 2) := ⟨by positivity⟩
  let f : ContinuumTestFunction (d + 2) := continuumBasisSuccSucc d i
  let g : ContinuumTestFunction (d + 2) := continuumBasisSuccSucc d j
  let Ψ : ContinuumTestFunction (d + 2) :=
    (SchwartzMap.smulLeftCLM ℝ (continuumGreenWeight (d := d + 2) mass f)) g
  have hΨ_int : Integrable (⇑Ψ) volume := Ψ.integrable
  have hΨ_eq :
      continuumGreenBilinear (d + 2) mass f g =
        ∫ x : ContinuumSpaceTime (d + 2), Ψ x := by
    rw [← continuumGreenBilinearRightCLM_apply (d := d + 2) (mass := mass) hmass f g]
    unfold continuumGreenBilinearRightCLM Ψ
    rw [ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply,
      SchwartzMap.smulLeftCLM_apply (continuumGreenWeight_hasTemperateGrowth
        (d := d + 2) mass hmass f)]
  rw [hΨ_eq, integral_euclidean_snoc d (fun x : ContinuumSpaceTime (d + 2) => Ψ x) hΨ_int]
  apply integral_congr_ae
  filter_upwards with y
  set P : ℝ :=
    DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 1)) (Nat.unpair i).1 y *
      DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 1)) (Nat.unpair j).1 y
  set M : ℝ := Real.sqrt (‖y‖ ^ 2 + mass ^ 2)
  have hM_sq : M ^ 2 = ‖y‖ ^ 2 + mass ^ 2 := by
    rw [show M = Real.sqrt (‖y‖ ^ 2 + mass ^ 2) by rfl, Real.sq_sqrt]
    positivity
  have hpow :
      (2 * Real.pi) ^ (-(((d + 2 : ℕ) : ℤ))) =
        (2 * Real.pi) ^ (-(((d + 1 : ℕ) : ℤ))) * (2 * Real.pi) ^ (-(1 : ℤ)) := by
    rw [show (-((d + 2 : ℕ) : ℤ)) = (-((d + 1 : ℕ) : ℤ)) + (-(1 : ℤ)) by omega,
      zpow_add₀]
    positivity
  have hinner :
      ∫ t : ℝ, Ψ (euclideanSnoc (d + 1) y t) =
        ∫ t : ℝ,
          (2 * Real.pi) ^ (-(((d + 2 : ℕ) : ℤ))) * P *
            (schwartzHermiteBasis1D (Nat.unpair i).2 t *
              schwartzHermiteBasis1D (Nat.unpair j).2 t /
              (t ^ 2 + (‖y‖ ^ 2 + mass ^ 2))) := by
    apply integral_congr_ae
    filter_upwards with t
    unfold Ψ
    rw [SchwartzMap.smulLeftCLM_apply (continuumGreenWeight_hasTemperateGrowth
      (d := d + 2) mass hmass f)]
    unfold continuumGreenWeight continuumKernel
    dsimp [f, g]
    rw [continuumBasisSuccSucc_apply_snoc_succ (d := d) (n := i) (y := y) (t := t),
      continuumBasisSuccSucc_apply_snoc_succ (d := d) (n := j) (y := y) (t := t),
      euclideanSnoc_norm_sq_succ (d := d) (y := y) (t := t)]
    have hshift : ‖y‖ ^ 2 + t ^ 2 + mass ^ 2 = t ^ 2 + (‖y‖ ^ 2 + mass ^ 2) := by
      ring
    rw [hshift]
    have hden : t ^ 2 + (‖y‖ ^ 2 + mass ^ 2) ≠ 0 := by
      positivity
    field_simp [hden]
    rw [show P =
        DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 1)) (Nat.unpair i).1 y *
          DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 1)) (Nat.unpair j).1 y by
        rfl]
    ac_rfl
  calc
    ∫ t : ℝ, Ψ (euclideanSnoc (d + 1) y t)
      = ∫ t : ℝ,
          (2 * Real.pi) ^ (-(((d + 2 : ℕ) : ℤ))) * P *
            (schwartzHermiteBasis1D (Nat.unpair i).2 t *
              schwartzHermiteBasis1D (Nat.unpair j).2 t /
              (t ^ 2 + (‖y‖ ^ 2 + mass ^ 2))) := hinner
    _ = ((2 * Real.pi) ^ (-(((d + 1 : ℕ) : ℤ))) * P) *
          ∫ t : ℝ,
            (2 * Real.pi) ^ (-(1 : ℤ)) *
              (schwartzHermiteBasis1D (Nat.unpair i).2 t *
                schwartzHermiteBasis1D (Nat.unpair j).2 t /
                (t ^ 2 + (‖y‖ ^ 2 + mass ^ 2))) := by
          rw [← integral_const_mul]
          congr 1
          ext t
          rw [hpow]
          ring
    _ = ((2 * Real.pi) ^ (-(((d + 1 : ℕ) : ℤ))) * P) *
          continuumGreenBilinear 1 M
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).2)
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).2) := by
          congr 1
          simpa [M, hM_sq] using
            (continuumGreenBilinear_basis_eq_weighted_real_integral_1d
              (mass := M) (i := (Nat.unpair i).2) (j := (Nat.unpair j).2)).symm
    _ = continuumBasisIteratedSliceIntegrand d mass i j y := by
          unfold continuumBasisIteratedSliceIntegrand
          rw [show P =
              DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 1)) (Nat.unpair i).1 y *
                DyninMityaginSpace.basis (E := ContinuumTestFunction (d + 1)) (Nat.unpair j).1 y by
              rfl,
            show M = Real.sqrt (‖y‖ ^ 2 + mass ^ 2) by rfl]
          ring

omit d N [NeZero N] in
/-- The two-dimensional continuum basis Green form peels into an iterated
integral along the first coordinate and a one-dimensional effective-mass
resolvent integral in the second coordinate. -/
private theorem continuumGreenBilinear_basis_eq_iterated_real_integral_2d
    (mass : ℝ) (hmass : 0 < mass) (i j : ℕ) :
    continuumGreenBilinear 2 mass
      (continuumBasisSuccSucc 0 i)
      (continuumBasisSuccSucc 0 j) =
      ∫ y : ContinuumSpaceTime 1, ∫ t : ℝ,
        (2 * Real.pi) ^ (-(2 : ℤ)) *
          (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).1 y *
            DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).1 y) *
          (schwartzHermiteBasis1D (Nat.unpair i).2 t *
            schwartzHermiteBasis1D (Nat.unpair j).2 t /
            (t ^ 2 + (‖y‖ ^ 2 + mass ^ 2))) := by
  letI : Fact (0 < 1) := ⟨by positivity⟩
  letI : Fact (0 < 2) := ⟨by positivity⟩
  let f : ContinuumTestFunction 2 := continuumBasisSuccSucc 0 i
  let g : ContinuumTestFunction 2 := continuumBasisSuccSucc 0 j
  let Ψ : ContinuumTestFunction 2 :=
    (SchwartzMap.smulLeftCLM ℝ (continuumGreenWeight (d := 2) mass f)) g
  have hΨ_int : Integrable (⇑Ψ) volume := Ψ.integrable
  have hΨ_eq :
      continuumGreenBilinear 2 mass f g =
        ∫ x : ContinuumSpaceTime 2, Ψ x := by
    rw [← continuumGreenBilinearRightCLM_apply (d := 2) (mass := mass) hmass f g]
    unfold continuumGreenBilinearRightCLM Ψ
    rw [ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply,
      SchwartzMap.smulLeftCLM_apply (continuumGreenWeight_hasTemperateGrowth
        (d := 2) mass hmass f)]
  rw [hΨ_eq, integral_euclidean_snoc 0 (fun x : ContinuumSpaceTime 2 => Ψ x) hΨ_int]
  congr 1
  ext y
  apply integral_congr_ae
  filter_upwards with t
  unfold Ψ
  rw [SchwartzMap.smulLeftCLM_apply (continuumGreenWeight_hasTemperateGrowth
    (d := 2) mass hmass f)]
  unfold continuumGreenWeight continuumKernel
  dsimp [f, g]
  rw [continuumBasisSuccSucc_apply_snoc (n := i) (y := y) (t := t),
    continuumBasisSuccSucc_apply_snoc (n := j) (y := y) (t := t),
    euclideanSnoc_norm_sq_one (y := y) (t := t)]
  have hshift :
      ‖y‖ ^ 2 + t ^ 2 + mass ^ 2 = t ^ 2 + (‖y‖ ^ 2 + mass ^ 2) := by
    ring
  rw [hshift]
  have hden : t ^ 2 + (‖y‖ ^ 2 + mass ^ 2) ≠ 0 := by
    positivity
  field_simp [hden]

omit d N [NeZero N] in
/-- The peeled two-dimensional continuum basis Green form is an outer
one-dimensional integral of effective-mass one-dimensional continuum Green
forms. -/
private theorem continuumGreenBilinear_basis_eq_effective_mass_integral_2d
    (mass : ℝ) (hmass : 0 < mass) (i j : ℕ) :
    continuumGreenBilinear 2 mass
      (continuumBasisSuccSucc 0 i)
      (continuumBasisSuccSucc 0 j) =
      ∫ y : ContinuumSpaceTime 1,
        (2 * Real.pi) ^ (-(1 : ℤ)) *
          (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).1 y *
            DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).1 y) *
          continuumGreenBilinear 1 (Real.sqrt (‖y‖ ^ 2 + mass ^ 2))
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).2)
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).2) := by
  letI : Fact (0 < 1) := ⟨by positivity⟩
  simpa [continuumBasisIteratedSliceIntegrand, mul_assoc, mul_left_comm, mul_comm] using
    (continuumGreenBilinear_basis_eq_effective_mass_integral_succsucc
      (d := 0) (mass := mass) hmass i j)

omit d N [NeZero N] in
/-- The explicit continuum effective-mass outer integrand for the peeled
two-dimensional basis Green form, written in scalar coordinates. -/
private def continuumHermiteEffectiveMassIntegrand
    (mass : ℝ) (i j : ℕ) (x : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(1 : ℤ)) *
    schwartzHermiteBasis1D (Nat.unpair i).1 x *
    schwartzHermiteBasis1D (Nat.unpair j).1 x *
    continuumGreenBilinear 1 (Real.sqrt (x ^ 2 + mass ^ 2))
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).2)
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).2)

omit d N [NeZero N] in
/-- Scalar-coordinate version of the effective-mass outer integral for the
two-dimensional continuum basis Green form. -/
private theorem continuumGreenBilinear_basis_eq_effective_mass_real_integral_2d
    (mass : ℝ) (hmass : 0 < mass) (i j : ℕ) :
    continuumGreenBilinear 2 mass
      (continuumBasisSuccSucc 0 i)
      (continuumBasisSuccSucc 0 j) =
      ∫ x : ℝ, continuumHermiteEffectiveMassIntegrand mass i j x := by
  letI : Fact (0 < 1) := ⟨by positivity⟩
  letI : Fact (0 < 2) := ⟨by positivity⟩
  rw [continuumGreenBilinear_basis_eq_effective_mass_integral_2d (mass := mass) hmass i j]
  rw [← euclideanFin1MeasEquiv_mp.integral_comp']
  congr 1
  ext y
  unfold continuumHermiteEffectiveMassIntegrand
  rw [continuumSpaceTime_one_norm_sq]
  have hi :
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).1) y =
        schwartzHermiteBasis1D (Nat.unpair i).1 (euclideanFin1MeasEquiv y) := by
    simpa [euclideanFin1MeasEquiv_apply] using
      (continuum_basis_apply_eq_hermite1D (n := (Nat.unpair i).1) (x := y))
  have hj :
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).1) y =
        schwartzHermiteBasis1D (Nat.unpair j).1 (euclideanFin1MeasEquiv y) := by
    simpa [euclideanFin1MeasEquiv_apply] using
      (continuum_basis_apply_eq_hermite1D (n := (Nat.unpair j).1) (x := y))
  rw [hi, hj]
  simp [euclideanFin1MeasEquiv_apply, mul_assoc, mul_left_comm, mul_comm]

omit d N [NeZero N] in
/-- The remaining `d = 2` propagator axiom is equivalent to convergence of the
peeled effective-mass outer mode sum to the matching effective-mass outer
continuum integral. This is the explicit analytic core left after the algebraic
rewrites on both the lattice and continuum sides. -/
private theorem latticeGreenBilinear_basis_tendsto_continuum_2d_reduced
    (mass : ℝ) (hmass : 0 < mass)
    (a_seq : ℕ → ℝ) (ha_pos : ∀ n, 0 < a_seq n)
    (ha_lim : Tendsto a_seq atTop (nhds 0))
    (N_seq : ℕ → ℕ) [∀ n, NeZero (N_seq n)]
    (hNa : Tendsto (fun n => (N_seq n : ℝ) * a_seq n) atTop atTop)
    (i j : ℕ) :
    Tendsto
      (fun n =>
        ∑ m0 : Fin (N_seq n),
          latticeHermiteEffectiveMassTerm (N := N_seq n) (a_seq n) mass i j m0)
      atTop
      (nhds
        (∫ y : ContinuumSpaceTime 1,
          (2 * Real.pi) ^ (-(1 : ℤ)) *
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).1 y *
              DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).1 y) *
            continuumGreenBilinear 1 (Real.sqrt (‖y‖ ^ 2 + mass ^ 2))
              (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).2)
              (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).2))) := by
  letI : Fact (0 < 2) := ⟨by positivity⟩
  have h :=
    latticeGreenBilinear_basis_tendsto_continuum
      (d := 2) mass hmass a_seq ha_pos ha_lim N_seq hNa i j
  convert h using 1
  · ext n
    simpa [continuumBasisSuccSucc] using
      (latticeGreenBilinear_basis_eq_effective_mass_sum_2d
        (N := N_seq n) (a := a_seq n) (mass := mass) (ha := ha_pos n) hmass i j).symm
  · simpa [continuumBasisSuccSucc] using
      (continuumGreenBilinear_basis_eq_effective_mass_integral_2d
        (mass := mass) hmass i j).symm

omit d N [NeZero N] in
/-- Full-generality recursive reduction of the basis-pair propagator axiom.
This is the abstract continuum/lattice matching statement behind the `d = 2`
specialization used in the physical theory. -/
private theorem latticeGreenBilinear_basis_tendsto_continuum_succsucc_reduced
    (d : ℕ) [Fact (0 < d + 1)] (mass : ℝ) (hmass : 0 < mass)
    (a_seq : ℕ → ℝ) (ha_pos : ∀ n, 0 < a_seq n)
    (ha_lim : Tendsto a_seq atTop (nhds 0))
    (N_seq : ℕ → ℕ) [∀ n, NeZero (N_seq n)]
    (hNa : Tendsto (fun n => (N_seq n : ℝ) * a_seq n) atTop atTop)
    (i j : ℕ) :
    Tendsto
      (fun n =>
        latticeBasisIteratedSliceSum (N := N_seq n) d (a_seq n) mass i j)
      atTop
      (nhds
        (∫ y : ContinuumSpaceTime (d + 1),
          continuumBasisIteratedSliceIntegrand d mass i j y)) := by
  letI : Fact (0 < d + 2) := ⟨by positivity⟩
  have h :=
    latticeGreenBilinear_basis_tendsto_continuum
      (d := d + 2) mass hmass a_seq ha_pos ha_lim N_seq hNa i j
  convert h using 1
  · ext n
    simpa [continuumBasisSuccSucc] using
      (latticeGreenBilinear_basis_eq_iterated_slice_sum
        (N := N_seq n) (d := d) (a := a_seq n) (mass := mass) (ha := ha_pos n) hmass i j).symm
  · simpa [continuumBasisSuccSucc, continuumBasisIteratedSliceIntegrand] using
      (continuumGreenBilinear_basis_eq_effective_mass_integral_succsucc
        (d := d) (mass := mass) hmass i j).symm

omit d N [NeZero N] in
/-- Scalar-coordinate version of the explicit `d = 2` propagator reduction:
the remaining analytic core is convergence of the lattice effective-mass outer
sum to the matching scalar real-line integral. -/
private theorem latticeGreenBilinear_basis_tendsto_continuum_2d_reduced_real
    (mass : ℝ) (hmass : 0 < mass)
    (a_seq : ℕ → ℝ) (ha_pos : ∀ n, 0 < a_seq n)
    (ha_lim : Tendsto a_seq atTop (nhds 0))
    (N_seq : ℕ → ℕ) [∀ n, NeZero (N_seq n)]
    (hNa : Tendsto (fun n => (N_seq n : ℝ) * a_seq n) atTop atTop)
    (i j : ℕ) :
    Tendsto
      (fun n =>
        ∑ m0 : Fin (N_seq n),
          latticeHermiteEffectiveMassTerm (N := N_seq n) (a_seq n) mass i j m0)
      atTop
      (nhds (∫ x : ℝ, continuumHermiteEffectiveMassIntegrand mass i j x)) := by
  have htarget :
      (∫ x : ℝ, continuumHermiteEffectiveMassIntegrand mass i j x) =
        ∫ y : ContinuumSpaceTime 1,
          (2 * Real.pi) ^ (-(1 : ℤ)) *
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).1 y *
              DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).1 y) *
            continuumGreenBilinear 1 (Real.sqrt (‖y‖ ^ 2 + mass ^ 2))
              (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).2)
              (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).2) := by
    calc
      (∫ x : ℝ, continuumHermiteEffectiveMassIntegrand mass i j x) =
          continuumGreenBilinear 2 mass
            (continuumBasisSuccSucc 0 i) (continuumBasisSuccSucc 0 j) := by
              symm
              exact continuumGreenBilinear_basis_eq_effective_mass_real_integral_2d
                (mass := mass) hmass i j
      _ = ∫ y : ContinuumSpaceTime 1,
            (2 * Real.pi) ^ (-(1 : ℤ)) *
              (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).1 y *
                DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).1 y) *
              continuumGreenBilinear 1 (Real.sqrt (‖y‖ ^ 2 + mass ^ 2))
                (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).2)
                (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).2) := by
            exact continuumGreenBilinear_basis_eq_effective_mass_integral_2d
              (mass := mass) hmass i j
  convert latticeGreenBilinear_basis_tendsto_continuum_2d_reduced
    (mass := mass) hmass a_seq ha_pos ha_lim N_seq hNa i j using 1
  simp [htarget]

/-- Extend basis-pair convergence of the lattice Green form to arbitrary
Schwartz test functions via the generic Dynin-Mityagin bilinear theorem. -/
theorem latticeGreenBilinear_tendsto_continuum [Fact (0 < d)]
    (mass : ℝ) (hmass : 0 < mass)
    (f g : ContinuumTestFunction d)
    (a_seq : ℕ → ℝ) (ha_pos : ∀ n, 0 < a_seq n)
    (ha_lim : Tendsto a_seq atTop (nhds 0))
    (N_seq : ℕ → ℕ) [∀ n, NeZero (N_seq n)]
    (hNa : Tendsto (fun n => (N_seq n : ℝ) * a_seq n) atTop atTop) :
    Tendsto
      (fun n => latticeGreenBilinear d (N_seq n) (a_seq n) mass f g)
      atTop
      (nhds (continuumGreenBilinear d mass f g)) := by
  obtain ⟨C, hC_pos, r, hbound⟩ :=
    latticeGreenBilinear_basis_eventually_bound (d := d) mass hmass a_seq ha_pos ha_lim N_seq
  simpa [latticeGreenBilinearRightCLM_apply, continuumGreenBilinearRightCLM_apply] using
    (GaussianField.tendsto_of_symmetric_basis_tendsto
      (l := atTop)
      (B_seq := fun n f =>
        latticeGreenBilinearRightCLM (d := d) (N := N_seq n) (a := a_seq n) (mass := mass) f)
      (B := fun f => continuumGreenBilinearRightCLM (d := d) (mass := mass) hmass f)
      (h_symm_seq := by
        intro n f g
        simpa [latticeGreenBilinearRightCLM_apply] using latticeGreenBilinear_symm
          (d := d) (N := N_seq n) (a := a_seq n) (mass := mass) f g)
      (h_symm := by
        intro f g
        simpa [continuumGreenBilinearRightCLM_apply] using
          continuumGreenBilinear_symm (d := d) (mass := mass) f g)
      (h_basis_bound := by
        refine ⟨C, hC_pos, r, r, ?_⟩
        filter_upwards [hbound] with n hn i j
        simpa [latticeGreenBilinearRightCLM_apply] using hn i j)
      (h_basis_tendsto := by
        intro i j
        simpa [latticeGreenBilinearRightCLM_apply, continuumGreenBilinearRightCLM_apply] using
          latticeGreenBilinear_basis_tendsto_continuum
            (d := d) mass hmass a_seq ha_pos ha_lim N_seq hNa i j)
      f g)

/-- The original propagator-convergence statement, now proved by combining the
spectral rewrite with the generic Dynin-Mityagin bilinear extension theorem. -/
theorem propagator_convergence [Fact (0 < d)]
    (mass : ℝ) (hmass : 0 < mass)
    (f g : ContinuumTestFunction d)
    (a_seq : ℕ → ℝ) (ha_pos : ∀ n, 0 < a_seq n)
    (ha_lim : Tendsto a_seq atTop (nhds 0))
    (N_seq : ℕ → ℕ) [∀ n, NeZero (N_seq n)]
    (hNa : Tendsto (fun n => (N_seq n : ℝ) * a_seq n) atTop atTop) :
    Tendsto
      (fun n => embeddedTwoPoint d (N_seq n) (a_seq n) mass (ha_pos n) hmass f g)
      atTop
      (nhds (continuumGreenBilinear d mass f g)) := by
  have hgreen := latticeGreenBilinear_tendsto_continuum
    (d := d) (mass := mass) hmass f g a_seq ha_pos ha_lim N_seq hNa
  simpa [embeddedTwoPoint_eq_latticeGreenBilinear] using hgreen

theorem embeddedTwoPoint_uniform_bound (mass : ℝ) (hmass : 0 < mass)
    (f : ContinuumTestFunction d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    embeddedTwoPoint d N a mass ha hmass f f ≤ C := by
  -- Get the Schwartz Riemann sum bound
  obtain ⟨C_f, hC_pos, hC_bound⟩ := schwartz_riemann_sum_bound d f
  refine ⟨mass⁻¹ ^ 2 * C_f, mul_pos (sq_pos_of_pos (inv_pos.mpr hmass)) hC_pos, ?_⟩
  intro a ha ha_le
  -- Step 1: Rewrite as integral over lattice configurations
  rw [embeddedTwoPoint_eq_covariance]
  -- Step 2: Unfold latticeEmbed to latticeEmbedEval
  simp only [latticeEmbed_eval, latticeEmbedEval]
  -- The integrand is (a^d * Σ_x ω(e_x) f(ax))^2
  -- This is (ω(h_f))^2 where h_f(x) = a^d * f(ax), by linearity of ω
  set T := latticeCovariance d N a mass ha hmass
  set μ := latticeGaussianMeasure d N a mass ha hmass
  set h_f : FinLatticeField d N := fun x => a ^ d * evalAtSite d N a f x
  -- Show the integrand equals (ω h_f)^2
  have hintegrand : ∀ ω : Configuration (FinLatticeField d N),
      (a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x) *
      (a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x) =
      (ω h_f) ^ 2 := by
    intro ω
    -- ω is a CLM, so ω(Σ_x c_x e_x) = Σ_x c_x ω(e_x) by linearity
    have hlin : ω h_f = a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x := by
      show ω h_f = a ^ d * ∑ x, ω (Pi.single x 1) * evalAtSite d N a f x
      have : h_f = a ^ d • ∑ x : FinLatticeSites d N,
          evalAtSite d N a f x • Pi.single x (1 : ℝ) := by
        ext y; simp [h_f, Finset.sum_apply, Pi.single_apply]
      rw [this, map_smul, smul_eq_mul]
      congr 1
      rw [map_sum]
      congr 1; ext x
      rw [map_smul, smul_eq_mul, mul_comm]
    rw [hlin]; ring
  simp_rw [hintegrand]
  -- Step 3: Apply second moment = covariance
  -- μ = latticeGaussianMeasure = GaussianField.measure T, unfold so rw can match
  have hμ_eq : μ = GaussianField.measure T := rfl
  rw [hμ_eq, GaussianField.second_moment_eq_covariance T h_f]
  -- Now goal: @inner ℝ _ _ (T h_f) (T h_f) ≤ mass⁻¹ ^ 2 * C_f
  -- Unfold inner to covariance
  rw [← GaussianField.covariance]
  -- Step 4: Apply covariance upper bound
  calc GaussianField.covariance T h_f h_f
      ≤ mass⁻¹ ^ 2 * ∑ x, h_f x ^ 2 :=
        covariance_le_mass_inv_sq_norm d N a mass ha hmass h_f
    _ = mass⁻¹ ^ 2 * (a ^ d * a ^ d * ∑ x, (evalAtSite d N a f x) ^ 2) := by
        congr 1; simp only [h_f, mul_pow, ← Finset.mul_sum]; ring
    _ = mass⁻¹ ^ 2 * (a ^ d * (a ^ d * ∑ x, (evalAtSite d N a f x) ^ 2)) := by
        ring_nf
    _ ≤ mass⁻¹ ^ 2 * (1 * C_f) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply mul_le_mul _ (hC_bound a ha ha_le N) (by positivity) (by positivity)
        exact pow_le_one₀ (le_of_lt ha) ha_le
    _ = mass⁻¹ ^ 2 * C_f := by ring

/-- **Positivity of the continuum Green's function.**

  `G(f, f) > 0` for nonzero f ∈ S(ℝ^d)

The Fourier-space integrand `|f̂(k)|² / (|k|² + m²)` is nonneg, and
strictly positive on a set of positive measure (since f̂ ≠ 0 for f ≠ 0
in Schwartz space — the Fourier transform is injective on S). -/
theorem continuumGreenBilinear_pos (mass : ℝ) (hmass : 0 < mass)
    (f : ContinuumTestFunction d) (hf : f ≠ 0) :
    0 < continuumGreenBilinear d mass f f := by
  unfold continuumGreenBilinear
  -- Factor as positive_constant * positive_integral
  apply mul_pos
  · -- (2π)^(-d) > 0
    exact zpow_pos (by positivity) _
  · -- ∫ f(k)² / (‖k‖² + m²) dk > 0
    -- Abbreviate the integrand
    set g := fun k : EuclideanSpace ℝ (Fin d) =>
      f.toFun k * f.toFun k / (‖k‖ ^ 2 + mass ^ 2)
    -- The denominator is positive everywhere
    have hden_pos : ∀ k : EuclideanSpace ℝ (Fin d), 0 < ‖k‖ ^ 2 + mass ^ 2 :=
      fun k => add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hmass)
    -- g is nonneg
    have hg_nonneg : 0 ≤ g := fun k =>
      div_nonneg (mul_self_nonneg (a := f.toFun k)) (le_of_lt (hden_pos k))
    -- g is continuous
    have hg_cont : Continuous g := by
      apply Continuous.div (f.continuous.mul f.continuous)
        ((continuous_norm.pow 2).add continuous_const)
      intro k; exact ne_of_gt (hden_pos k)
    -- g is integrable (bounded by f²/m², and f² is integrable since f ∈ L²)
    have hf_sq_int : Integrable (fun k => (f k) ^ 2)
        (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))) :=
      (f.memLp 2).integrable_sq
    have hg_int : Integrable g := by
      apply (hf_sq_int.div_const (mass ^ 2)).mono hg_cont.aestronglyMeasurable
      apply Filter.Eventually.of_forall; intro k
      rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg k)]
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
      -- g(k) = f(k)^2 / (||k||^2 + m^2) ≤ f(k)^2 / m^2 since ||k||^2 + m^2 ≥ m^2
      change f.toFun k * f.toFun k / (‖k‖ ^ 2 + mass ^ 2) ≤ f k ^ 2 / mass ^ 2
      have hfk : f.toFun k = f k := rfl
      rw [hfk, ← sq]
      apply div_le_div_of_nonneg_left (sq_nonneg (f k)) (by positivity)
      linarith [sq_nonneg ‖k‖]
    -- f ≠ 0 gives k₀ with f(k₀) ≠ 0
    obtain ⟨k₀, hk₀⟩ := DFunLike.ne_iff.mp hf
    -- g(k₀) ≠ 0
    have hg_k₀ : g k₀ ≠ 0 := by
      simp only [g]
      exact ne_of_gt (div_pos (mul_self_pos.mpr hk₀) (hden_pos k₀))
    -- Integral positive by `integral_pos_of_integrable_nonneg_nonzero`
    exact integral_pos_of_integrable_nonneg_nonzero hg_cont hg_int hg_nonneg hg_k₀

/-- **Mass-gap upper bound on the continuum Green quadratic form.**

Since `‖k‖² + m² ≥ m²`, the covariance kernel is pointwise bounded by `m⁻²`.
Therefore
`G(f,f) ≤ (2π)^(-d) * m⁻² * ∫ f(x)^2 dx`.

This is the deterministic L²-side of the OS1 regularity estimate. -/
theorem continuumGreenBilinear_le_mass_inv_sq (mass : ℝ) (_hmass : 0 < mass)
    (f : ContinuumTestFunction d) :
    continuumGreenBilinear d mass f f ≤
      (2 * Real.pi) ^ (-(d : ℤ)) * (mass ^ 2)⁻¹ *
        ∫ k : EuclideanSpace ℝ (Fin d), (f k) ^ 2 := by
  unfold continuumGreenBilinear
  have hconst_nonneg : 0 ≤ (2 * Real.pi) ^ (-(d : ℤ)) := by positivity
  have hf_sq_int : Integrable (fun k : EuclideanSpace ℝ (Fin d) => (f k) ^ 2)
      (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    (f.memLp 2).integrable_sq
  have hint_upper : Integrable
      (fun k : EuclideanSpace ℝ (Fin d) => (mass ^ 2)⁻¹ * (f k) ^ 2) := by
    exact hf_sq_int.const_mul _
  have h_int_le :
      ∫ k : EuclideanSpace ℝ (Fin d), f.toFun k * f.toFun k / (‖k‖ ^ 2 + mass ^ 2) ≤
        ∫ k : EuclideanSpace ℝ (Fin d), (mass ^ 2)⁻¹ * (f k) ^ 2 := by
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun k =>
        div_nonneg (mul_self_nonneg (a := f.toFun k))
          (by positivity : 0 ≤ ‖k‖ ^ 2 + mass ^ 2))
    · exact hint_upper
    · exact ae_of_all _ (fun k => by
        change f k * f k / (‖k‖ ^ 2 + mass ^ 2) ≤ (mass ^ 2)⁻¹ * (f k) ^ 2
        rw [← sq]
        calc
          f k ^ 2 / (‖k‖ ^ 2 + mass ^ 2) ≤ f k ^ 2 / mass ^ 2 := by
            apply div_le_div_of_nonneg_left (sq_nonneg (f k)) (by positivity)
            nlinarith [sq_nonneg ‖k‖]
          _ = (mass ^ 2)⁻¹ * (f k) ^ 2 := by rw [div_eq_mul_inv, mul_comm])
  calc
    (2 * Real.pi) ^ (-(d : ℤ)) *
        ∫ k : EuclideanSpace ℝ (Fin d), f.toFun k * f.toFun k / (‖k‖ ^ 2 + mass ^ 2)
      ≤ (2 * Real.pi) ^ (-(d : ℤ)) *
          ∫ k : EuclideanSpace ℝ (Fin d), (mass ^ 2)⁻¹ * (f k) ^ 2 :=
        mul_le_mul_of_nonneg_left h_int_le hconst_nonneg
    _ = (2 * Real.pi) ^ (-(d : ℤ)) * (mass ^ 2)⁻¹ *
          ∫ k : EuclideanSpace ℝ (Fin d), (f k) ^ 2 := by
        rw [integral_const_mul]
        ring

omit N [NeZero N] in
/-- Continuum Green cross-terms are controlled by the average of the two diagonal
terms, using positivity of the quadratic form on `f ± g`. -/
private theorem continuumGreenBilinear_abs_le_half_diag_add_diag
    (mass : ℝ) (hmass : 0 < mass)
    (f g : ContinuumTestFunction d) :
    |continuumGreenBilinear d mass f g| ≤
      (continuumGreenBilinear d mass f f +
        continuumGreenBilinear d mass g g) / 2 := by
  have hnonneg :
      ∀ h : ContinuumTestFunction d, 0 ≤ continuumGreenBilinear d mass h h := by
    intro h
    by_cases hh : h = 0
    · subst hh
      unfold continuumGreenBilinear
      have hzero_fun :
          (fun k : EuclideanSpace ℝ (Fin d) =>
            SchwartzMap.toFun (0 : ContinuumTestFunction d) k *
              SchwartzMap.toFun (0 : ContinuumTestFunction d) k / (‖k‖ ^ 2 + mass ^ 2)) =
            fun _ => (0 : ℝ) := by
        funext k
        change (0 : ℝ) * 0 / (‖k‖ ^ 2 + mass ^ 2) = 0
        simp
      have hzero :
          ∫ k : EuclideanSpace ℝ (Fin d),
            SchwartzMap.toFun (0 : ContinuumTestFunction d) k *
              SchwartzMap.toFun (0 : ContinuumTestFunction d) k / (‖k‖ ^ 2 + mass ^ 2) = 0 := by
        rw [hzero_fun, integral_zero]
      rw [hzero]
      positivity
    · exact le_of_lt (continuumGreenBilinear_pos (d := d) mass hmass h hh)
  have hadd_right :
      ∀ u v w : ContinuumTestFunction d,
        continuumGreenBilinear d mass u (v + w) =
          continuumGreenBilinear d mass u v +
            continuumGreenBilinear d mass u w := by
    intro u v w
    rw [← continuumGreenBilinearRightCLM_apply (d := d) (mass := mass) hmass u (v + w),
      ← continuumGreenBilinearRightCLM_apply (d := d) (mass := mass) hmass u v,
      ← continuumGreenBilinearRightCLM_apply (d := d) (mass := mass) hmass u w]
    exact (continuumGreenBilinearRightCLM (d := d) (mass := mass) hmass u).map_add v w
  have hsub_right :
      ∀ u v w : ContinuumTestFunction d,
        continuumGreenBilinear d mass u (v - w) =
          continuumGreenBilinear d mass u v -
            continuumGreenBilinear d mass u w := by
    intro u v w
    rw [← continuumGreenBilinearRightCLM_apply (d := d) (mass := mass) hmass u (v - w),
      ← continuumGreenBilinearRightCLM_apply (d := d) (mass := mass) hmass u v,
      ← continuumGreenBilinearRightCLM_apply (d := d) (mass := mass) hmass u w]
    exact (continuumGreenBilinearRightCLM (d := d) (mass := mass) hmass u).map_sub v w
  have hadd_left :
      ∀ u v w : ContinuumTestFunction d,
        continuumGreenBilinear d mass (u + v) w =
          continuumGreenBilinear d mass u w +
            continuumGreenBilinear d mass v w := by
    intro u v w
    rw [continuumGreenBilinear_symm (d := d) (mass := mass) (f := u + v) (g := w),
      continuumGreenBilinear_symm (d := d) (mass := mass) (f := u) (g := w),
      continuumGreenBilinear_symm (d := d) (mass := mass) (f := v) (g := w)]
    exact hadd_right w u v
  have hsub_left :
      ∀ u v w : ContinuumTestFunction d,
        continuumGreenBilinear d mass (u - v) w =
          continuumGreenBilinear d mass u w -
            continuumGreenBilinear d mass v w := by
    intro u v w
    rw [continuumGreenBilinear_symm (d := d) (mass := mass) (f := u - v) (g := w),
      continuumGreenBilinear_symm (d := d) (mass := mass) (f := u) (g := w),
      continuumGreenBilinear_symm (d := d) (mass := mass) (f := v) (g := w)]
    exact hsub_right w u v
  have hplus_expand :
      continuumGreenBilinear d mass (f + g) (f + g) =
        continuumGreenBilinear d mass f f +
          2 * continuumGreenBilinear d mass f g +
          continuumGreenBilinear d mass g g := by
    calc
      continuumGreenBilinear d mass (f + g) (f + g)
          = continuumGreenBilinear d mass (f + g) f +
              continuumGreenBilinear d mass (f + g) g := hadd_right (f + g) f g
      _ = (continuumGreenBilinear d mass f f + continuumGreenBilinear d mass g f) +
            (continuumGreenBilinear d mass f g + continuumGreenBilinear d mass g g) := by
              rw [hadd_left f g f, hadd_left f g g]
      _ = continuumGreenBilinear d mass f f +
            2 * continuumGreenBilinear d mass f g +
            continuumGreenBilinear d mass g g := by
              rw [continuumGreenBilinear_symm (d := d) (mass := mass) (f := g) (g := f)]
              ring
  have hminus_expand :
      continuumGreenBilinear d mass (f - g) (f - g) =
        continuumGreenBilinear d mass f f -
          2 * continuumGreenBilinear d mass f g +
          continuumGreenBilinear d mass g g := by
    calc
      continuumGreenBilinear d mass (f - g) (f - g)
          = continuumGreenBilinear d mass (f - g) f -
              continuumGreenBilinear d mass (f - g) g := hsub_right (f - g) f g
      _ = (continuumGreenBilinear d mass f f - continuumGreenBilinear d mass g f) -
            (continuumGreenBilinear d mass f g - continuumGreenBilinear d mass g g) := by
              rw [hsub_left f g f, hsub_left f g g]
      _ = continuumGreenBilinear d mass f f -
            2 * continuumGreenBilinear d mass f g +
            continuumGreenBilinear d mass g g := by
              rw [continuumGreenBilinear_symm (d := d) (mass := mass) (f := g) (g := f)]
              ring
  have hplus :
      0 ≤ continuumGreenBilinear d mass f f +
        2 * continuumGreenBilinear d mass f g +
        continuumGreenBilinear d mass g g := by
    simpa [hplus_expand] using hnonneg (f + g)
  have hminus :
      0 ≤ continuumGreenBilinear d mass f f -
        2 * continuumGreenBilinear d mass f g +
        continuumGreenBilinear d mass g g := by
    simpa [hminus_expand] using hnonneg (f - g)
  have hlower :
      -((continuumGreenBilinear d mass f f + continuumGreenBilinear d mass g g) / 2) ≤
        continuumGreenBilinear d mass f g := by
    linarith
  have hupper :
      continuumGreenBilinear d mass f g ≤
        (continuumGreenBilinear d mass f f + continuumGreenBilinear d mass g g) / 2 := by
    linarith
  exact abs_le.mpr ⟨hlower, hupper⟩

omit d N [NeZero N] in
/-- The one-dimensional continuum DM basis has unit L² norm. -/
private theorem continuumBasis_l2_sq_1d (i : ℕ) :
    ∫ k : ContinuumSpaceTime 1,
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i k) ^ 2 = 1 := by
  letI : Fact (0 < 1) := ⟨by positivity⟩
  calc
    ∫ k : ContinuumSpaceTime 1,
        (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i k) ^ 2
      = ∫ t : ℝ,
          (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i
            (euclideanFin1MeasEquiv.symm t)) ^ 2 := by
              simpa using
                euclideanFin1MeasEquiv_mp.integral_comp'
                  (fun t : ℝ =>
                    (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i
                      (euclideanFin1MeasEquiv.symm t)) ^ 2)
    ∫ t : ℝ,
        (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i
          (euclideanFin1MeasEquiv.symm t)) ^ 2
      = ∫ t : ℝ, hermiteFunction i t * hermiteFunction i t := by
          congr 1
          ext t
          have hi :
              DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i
                (euclideanFin1MeasEquiv.symm t) =
                schwartzHermiteBasis1D i t := by
            simpa [euclideanFin1MeasEquiv_apply] using
              (continuum_basis_apply_eq_hermite1D
                (n := i) (x := euclideanFin1MeasEquiv.symm t))
          rw [hi, schwartzHermiteBasis1D_apply]
          ring
    _ = 1 := by
          simpa using (hermiteFunction_orthonormal i i)

omit d N [NeZero N] in
/-- Diagonal one-dimensional continuum basis Green forms are bounded by the
mass-gap kernel `(2π)⁻¹ m⁻²`. -/
private theorem continuumGreenBilinear_basis_diag_le_mass_inv_sq_1d
    (mass : ℝ) (hmass : 0 < mass) (i : ℕ) :
    continuumGreenBilinear 1 mass
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i)
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i) ≤
      (2 * Real.pi) ^ (-(1 : ℤ)) * (mass ^ 2)⁻¹ := by
  letI : Fact (0 < 1) := ⟨by positivity⟩
  have h :=
    continuumGreenBilinear_le_mass_inv_sq (d := 1) mass hmass
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i)
  calc
    continuumGreenBilinear 1 mass
        (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i)
        (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i)
      ≤ (2 * Real.pi) ^ (-(1 : ℤ)) * (mass ^ 2)⁻¹ *
          ∫ k : ContinuumSpaceTime 1,
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i k) ^ 2 := h
    _ = (2 * Real.pi) ^ (-(1 : ℤ)) * (mass ^ 2)⁻¹ := by
          rw [continuumBasis_l2_sq_1d (i := i), mul_one]

omit d N [NeZero N] in
/-- Off-diagonal one-dimensional continuum basis Green forms satisfy the same
mass-gap bound, via the quadratic-form polarization estimate. -/
private theorem continuumGreenBilinear_basis_abs_le_mass_inv_sq_1d
    (mass : ℝ) (hmass : 0 < mass) (i j : ℕ) :
    |continuumGreenBilinear 1 mass
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i)
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) j)| ≤
      (2 * Real.pi) ^ (-(1 : ℤ)) * (mass ^ 2)⁻¹ := by
  letI : Fact (0 < 1) := ⟨by positivity⟩
  have habs :=
    continuumGreenBilinear_abs_le_half_diag_add_diag (d := 1) mass hmass
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i)
      (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) j)
  have hii := continuumGreenBilinear_basis_diag_le_mass_inv_sq_1d mass hmass i
  have hjj := continuumGreenBilinear_basis_diag_le_mass_inv_sq_1d mass hmass j
  calc
    |continuumGreenBilinear 1 mass
        (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i)
        (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) j)|
      ≤ (continuumGreenBilinear 1 mass
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i)
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) i) +
          continuumGreenBilinear 1 mass
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) j)
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) j)) / 2 := habs
    _ ≤ (((2 * Real.pi) ^ (-(1 : ℤ)) * (mass ^ 2)⁻¹) +
          ((2 * Real.pi) ^ (-(1 : ℤ)) * (mass ^ 2)⁻¹)) / 2 := by
          gcongr
    _ = (2 * Real.pi) ^ (-(1 : ℤ)) * (mass ^ 2)⁻¹ := by
          ring

omit d N [NeZero N] in
/-- The peeled physical effective-mass integrand is bounded by an explicit
Hermite-product numerator over the massive rational kernel `x² + m²`. -/
private theorem continuumHermiteEffectiveMassIntegrand_abs_le_kernel
    (mass : ℝ) (hmass : 0 < mass) (i j : ℕ) (x : ℝ) :
    |continuumHermiteEffectiveMassIntegrand mass i j x| ≤
      ((2 * Real.pi) ^ (-(1 : ℤ)) * (2 * Real.pi) ^ (-(1 : ℤ))) *
        (|schwartzHermiteBasis1D (Nat.unpair i).1 x| *
          |schwartzHermiteBasis1D (Nat.unpair j).1 x|) /
        (x ^ 2 + mass ^ 2) := by
  let M : ℝ := Real.sqrt (x ^ 2 + mass ^ 2)
  have hM_pos : 0 < M := by
    rw [show M = Real.sqrt (x ^ 2 + mass ^ 2) by rfl]
    positivity
  have hinner :
      |continuumGreenBilinear 1 M
        (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).2)
        (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).2)| ≤
      (2 * Real.pi) ^ (-(1 : ℤ)) * (M ^ 2)⁻¹ := by
    exact continuumGreenBilinear_basis_abs_le_mass_inv_sq_1d
      (mass := M) hM_pos (Nat.unpair i).2 (Nat.unpair j).2
  have hM_sq : M ^ 2 = x ^ 2 + mass ^ 2 := by
    rw [show M = Real.sqrt (x ^ 2 + mass ^ 2) by rfl, Real.sq_sqrt]
    positivity
  unfold continuumHermiteEffectiveMassIntegrand
  calc
    |(2 * Real.pi) ^ (-(1 : ℤ)) * schwartzHermiteBasis1D (Nat.unpair i).1 x *
        schwartzHermiteBasis1D (Nat.unpair j).1 x *
        continuumGreenBilinear 1 (Real.sqrt (x ^ 2 + mass ^ 2))
          (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).2)
          (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).2)|
      = (2 * Real.pi) ^ (-(1 : ℤ)) *
        (|schwartzHermiteBasis1D (Nat.unpair i).1 x| *
          (|schwartzHermiteBasis1D (Nat.unpair j).1 x| *
            |continuumGreenBilinear 1 (Real.sqrt (x ^ 2 + mass ^ 2))
              (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).2)
              (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).2)|)) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity)]
            ring
    _ =
      (2 * Real.pi) ^ (-(1 : ℤ)) * |schwartzHermiteBasis1D (Nat.unpair i).1 x| *
        |schwartzHermiteBasis1D (Nat.unpair j).1 x| *
        |continuumGreenBilinear 1 (Real.sqrt (x ^ 2 + mass ^ 2))
          (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).2)
          (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).2)| := by
            ring
    _ ≤ (2 * Real.pi) ^ (-(1 : ℤ)) *
          |schwartzHermiteBasis1D (Nat.unpair i).1 x| *
          |schwartzHermiteBasis1D (Nat.unpair j).1 x| *
          ((2 * Real.pi) ^ (-(1 : ℤ)) * (M ^ 2)⁻¹) := by
            gcongr
    _ = ((2 * Real.pi) ^ (-(1 : ℤ)) * (2 * Real.pi) ^ (-(1 : ℤ))) *
          (|schwartzHermiteBasis1D (Nat.unpair i).1 x| *
            |schwartzHermiteBasis1D (Nat.unpair j).1 x|) /
          (x ^ 2 + mass ^ 2) := by
            rw [hM_sq, div_eq_mul_inv]
            ring

omit d N [NeZero N] in
/-- Consequently, the peeled physical effective-mass integrand admits a pure
kernel majorant `C_ij / (x² + m²)` with explicit polynomial dependence on the
outer Hermite indices. -/
private theorem continuumHermiteEffectiveMassIntegrand_kernel_bound
    (mass : ℝ) (hmass : 0 < mass) (i j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      |continuumHermiteEffectiveMassIntegrand mass i j x| ≤ C / (x ^ 2 + mass ^ 2) := by
  obtain ⟨Cψ, s, hCψ_pos, hs_nonneg, hsup⟩ := hermiteFunction_sup_bound
  set K : ℝ := (2 * Real.pi) ^ (-(1 : ℤ)) * (2 * Real.pi) ^ (-(1 : ℤ))
  set A : ℝ := Cψ * (1 + ((Nat.unpair i).1 : ℝ)) ^ s
  set B : ℝ := Cψ * (1 + ((Nat.unpair j).1 : ℝ)) ^ s
  set C : ℝ := K * A * B
  refine ⟨C, by positivity, ?_⟩
  intro x
  have hi :
      |schwartzHermiteBasis1D (Nat.unpair i).1 x| ≤ A := by
    simpa [A, schwartzHermiteBasis1D_apply] using hsup (Nat.unpair i).1 x
  have hj :
      |schwartzHermiteBasis1D (Nat.unpair j).1 x| ≤ B := by
    simpa [A, B, schwartzHermiteBasis1D_apply] using hsup (Nat.unpair j).1 x
  have hkernel := continuumHermiteEffectiveMassIntegrand_abs_le_kernel mass hmass i j x
  have hK_nonneg : 0 ≤ K := by
    positivity
  have hstep1 :
      K * (|schwartzHermiteBasis1D (Nat.unpair i).1 x| *
            |schwartzHermiteBasis1D (Nat.unpair j).1 x|) ≤
        (K * A) * B := by
    have h1 : K * |schwartzHermiteBasis1D (Nat.unpair i).1 x| ≤ K * A := by
      exact mul_le_mul_of_nonneg_left hi hK_nonneg
    calc
      K * (|schwartzHermiteBasis1D (Nat.unpair i).1 x| *
            |schwartzHermiteBasis1D (Nat.unpair j).1 x|) =
          (K * |schwartzHermiteBasis1D (Nat.unpair i).1 x|) *
            |schwartzHermiteBasis1D (Nat.unpair j).1 x| := by
              ring
      _ ≤ (K * A) * |schwartzHermiteBasis1D (Nat.unpair j).1 x| := by
            exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ (K * A) * B := by
            exact mul_le_mul_of_nonneg_left hj (by positivity)
  have hden_pos : 0 < x ^ 2 + mass ^ 2 := by positivity
  calc
    |continuumHermiteEffectiveMassIntegrand mass i j x|
      ≤ (K *
            (|schwartzHermiteBasis1D (Nat.unpair i).1 x| *
              |schwartzHermiteBasis1D (Nat.unpair j).1 x|)) /
          (x ^ 2 + mass ^ 2) := hkernel
    _ ≤ ((K * A) * B) /
          (x ^ 2 + mass ^ 2) := by
            exact div_le_div_of_nonneg_right hstep1 (le_of_lt hden_pos)
    _ = C / (x ^ 2 + mass ^ 2) := by
          simp [C, K, mul_assoc]

omit d N [NeZero N] in
/-- The one-dimensional massive kernel `1 / (x² + m²)` is integrable on `ℝ`
for every positive mass. We compare it to mathlib's model kernel
`1 / (1 + x²)` using the uniform lower bound
`min(1,m²) * (1 + x²) ≤ x² + m²`. -/
private theorem integrable_massiveKernel1D
    (mass : ℝ) (hmass : 0 < mass) :
    Integrable (fun x : ℝ => (x ^ 2 + mass ^ 2)⁻¹) := by
  let c : ℝ := min 1 (mass ^ 2)
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hmeas :
      AEStronglyMeasurable (fun x : ℝ => (x ^ 2 + mass ^ 2)⁻¹) := by
    have hcont : Continuous (fun x : ℝ => (x ^ 2 + mass ^ 2)⁻¹) := by
      apply Continuous.inv₀
      · exact (continuous_pow 2).add continuous_const
      · intro x
        positivity
    exact hcont.aestronglyMeasurable
  refine (integrable_inv_one_add_sq.const_mul c⁻¹).mono' hmeas (ae_of_all _ fun x => ?_)
  have hnorm_nonneg : 0 ≤ (x ^ 2 + mass ^ 2)⁻¹ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnorm_nonneg]
  have hc_le_one : c ≤ 1 := by
    exact min_le_left _ _
  have hc_le_mass : c ≤ mass ^ 2 := by
    exact min_le_right _ _
  have hx_le : c * x ^ 2 ≤ x ^ 2 := by
    calc
      c * x ^ 2 ≤ 1 * x ^ 2 := by
        exact mul_le_mul_of_nonneg_right hc_le_one (sq_nonneg x)
      _ = x ^ 2 := by ring
  have hden_le : c * (1 + x ^ 2) ≤ x ^ 2 + mass ^ 2 := by
    calc
      c * (1 + x ^ 2) = c + c * x ^ 2 := by ring
      _ ≤ mass ^ 2 + x ^ 2 := add_le_add hc_le_mass hx_le
      _ = x ^ 2 + mass ^ 2 := by ring
  have hcomp : (x ^ 2 + mass ^ 2)⁻¹ ≤ (c * (1 + x ^ 2))⁻¹ := by
    have hc_mul_pos : 0 < c * (1 + x ^ 2) := by positivity
    simpa [one_div] using one_div_le_one_div_of_le hc_mul_pos hden_le
  calc
    (x ^ 2 + mass ^ 2)⁻¹ ≤ (c * (1 + x ^ 2))⁻¹ := hcomp
    _ = c⁻¹ * (1 + x ^ 2)⁻¹ := by
          rw [mul_inv_rev, mul_comm]

omit d N [NeZero N] in
/-- Multiplying the massive one-dimensional kernel by a constant preserves
integrability. This is the exact shape used for dominated convergence on the
peeled physical effective-mass integrand. -/
private theorem integrable_const_massiveKernel1D
    (C mass : ℝ) (hmass : 0 < mass) :
    Integrable (fun x : ℝ => C / (x ^ 2 + mass ^ 2)) := by
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (integrable_massiveKernel1D (mass := mass) hmass).const_mul C

omit d N [NeZero N] in
/-- The peeled physical effective-mass integrand admits an explicit integrable
majorant. This is the domination package needed for the next convergence step. -/
private theorem continuumHermiteEffectiveMassIntegrand_has_integrable_majorant
    (mass : ℝ) (hmass : 0 < mass) (i j : ℕ) :
    ∃ g : ℝ → ℝ, Integrable g ∧
      ∀ x : ℝ, 0 ≤ g x ∧
        |continuumHermiteEffectiveMassIntegrand mass i j x| ≤ g x := by
  rcases continuumHermiteEffectiveMassIntegrand_kernel_bound mass hmass i j with
    ⟨C, hC_pos, hbound⟩
  refine ⟨fun x : ℝ => C / (x ^ 2 + mass ^ 2), ?_, ?_⟩
  · exact integrable_const_massiveKernel1D C mass hmass
  · intro x
    refine ⟨by positivity, hbound x⟩

omit d N [NeZero N] in
/-- The peeled physical effective-mass integrand can be written as an explicit
two-variable kernel integrated in the second variable. -/
private def continuumHermiteEffectiveMassTwoVarIntegrand
    (mass : ℝ) (i j : ℕ) (p : ℝ × ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(1 : ℤ)) *
    (2 * Real.pi) ^ (-(1 : ℤ)) *
    schwartzHermiteBasis1D (Nat.unpair i).1 p.1 *
    schwartzHermiteBasis1D (Nat.unpair j).1 p.1 *
    (schwartzHermiteBasis1D (Nat.unpair i).2 p.2 *
      schwartzHermiteBasis1D (Nat.unpair j).2 p.2 /
      (p.2 ^ 2 + (p.1 ^ 2 + mass ^ 2)))

omit d N [NeZero N] in
/-- Pointwise identification of the peeled effective-mass integrand with the
integral of its explicit two-variable kernel. -/
private theorem continuumHermiteEffectiveMassIntegrand_eq_integral_twoVar
    (mass : ℝ) (i j : ℕ) (x : ℝ) :
    continuumHermiteEffectiveMassIntegrand mass i j x =
      ∫ t : ℝ, continuumHermiteEffectiveMassTwoVarIntegrand mass i j (x, t) := by
  set M : ℝ := Real.sqrt (x ^ 2 + mass ^ 2)
  have hM_sq : M ^ 2 = x ^ 2 + mass ^ 2 := by
    rw [show M = Real.sqrt (x ^ 2 + mass ^ 2) by rfl, Real.sq_sqrt]
    positivity
  unfold continuumHermiteEffectiveMassIntegrand continuumHermiteEffectiveMassTwoVarIntegrand
  calc
    (2 * Real.pi) ^ (-(1 : ℤ)) *
        schwartzHermiteBasis1D (Nat.unpair i).1 x *
        schwartzHermiteBasis1D (Nat.unpair j).1 x *
        continuumGreenBilinear 1 (Real.sqrt (x ^ 2 + mass ^ 2))
          (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).2)
          (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).2)
      = ((2 * Real.pi) ^ (-(1 : ℤ)) *
          schwartzHermiteBasis1D (Nat.unpair i).1 x *
          schwartzHermiteBasis1D (Nat.unpair j).1 x) *
          continuumGreenBilinear 1 M
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair i).2)
            (DyninMityaginSpace.basis (E := ContinuumTestFunction 1) (Nat.unpair j).2) := by
              simp [M, mul_assoc]
    _ = ((2 * Real.pi) ^ (-(1 : ℤ)) *
          schwartzHermiteBasis1D (Nat.unpair i).1 x *
          schwartzHermiteBasis1D (Nat.unpair j).1 x) *
          ∫ t : ℝ,
            (2 * Real.pi) ^ (-(1 : ℤ)) *
              (schwartzHermiteBasis1D (Nat.unpair i).2 t *
                schwartzHermiteBasis1D (Nat.unpair j).2 t /
                (t ^ 2 + (x ^ 2 + mass ^ 2))) := by
              congr 1
              simpa [M, hM_sq] using
                (continuumGreenBilinear_basis_eq_weighted_real_integral_1d
                  (mass := M) (i := (Nat.unpair i).2) (j := (Nat.unpair j).2))
    _ = ∫ t : ℝ, continuumHermiteEffectiveMassTwoVarIntegrand mass i j (x, t) := by
          rw [← integral_const_mul]
          congr 1
          ext t
          unfold continuumHermiteEffectiveMassTwoVarIntegrand
          ring

omit d N [NeZero N] in
/-- The explicit two-variable kernel for the peeled physical effective-mass
integrand is continuous on `ℝ × ℝ`. -/
private theorem continuous_continuumHermiteEffectiveMassTwoVarIntegrand
    (mass : ℝ) (hmass : 0 < mass) (i j : ℕ) :
    Continuous (continuumHermiteEffectiveMassTwoVarIntegrand mass i j) := by
  let f₁ : ℝ × ℝ → ℝ := fun p => schwartzHermiteBasis1D (Nat.unpair i).1 p.1
  let f₂ : ℝ × ℝ → ℝ := fun p => schwartzHermiteBasis1D (Nat.unpair j).1 p.1
  let g₁ : ℝ × ℝ → ℝ := fun p => schwartzHermiteBasis1D (Nat.unpair i).2 p.2
  let g₂ : ℝ × ℝ → ℝ := fun p => schwartzHermiteBasis1D (Nat.unpair j).2 p.2
  have hf₁ : Continuous f₁ := by
    exact (schwartzHermiteBasis1D (Nat.unpair i).1).continuous.comp continuous_fst
  have hf₂ : Continuous f₂ := by
    exact (schwartzHermiteBasis1D (Nat.unpair j).1).continuous.comp continuous_fst
  have hg₁ : Continuous g₁ := by
    exact (schwartzHermiteBasis1D (Nat.unpair i).2).continuous.comp continuous_snd
  have hg₂ : Continuous g₂ := by
    exact (schwartzHermiteBasis1D (Nat.unpair j).2).continuous.comp continuous_snd
  have hnum : Continuous (fun p : ℝ × ℝ =>
      (2 * Real.pi) ^ (-(1 : ℤ)) *
        ((2 * Real.pi) ^ (-(1 : ℤ)) * (f₁ p * (f₂ p * (g₁ p * g₂ p)))) ) := by
    exact continuous_const.mul <|
      (continuous_const.mul <| hf₁.mul <| hf₂.mul <| hg₁.mul hg₂)
  have hden : Continuous (fun p : ℝ × ℝ => p.2 ^ 2 + (p.1 ^ 2 + mass ^ 2)) := by
    exact (continuous_snd.pow 2).add ((continuous_fst.pow 2).add continuous_const)
  have hdiv : Continuous (fun p : ℝ × ℝ =>
      ((2 * Real.pi) ^ (-(1 : ℤ)) *
        ((2 * Real.pi) ^ (-(1 : ℤ)) * (f₁ p * (f₂ p * (g₁ p * g₂ p))))) /
        (p.2 ^ 2 + (p.1 ^ 2 + mass ^ 2))) := by
    apply Continuous.div hnum hden
    intro p
    have hpos : 0 < p.2 ^ 2 + (p.1 ^ 2 + mass ^ 2) := by
      positivity
    exact hpos.ne'
  convert hdiv using 1
  funext p
  unfold continuumHermiteEffectiveMassTwoVarIntegrand f₁ f₂ g₁ g₂
  field_simp

omit d N [NeZero N] in
/-- The peeled physical effective-mass integrand is a.e.-strongly measurable,
because it is the Bochner integral in the second variable of a continuous
two-variable kernel. -/
private theorem aestronglyMeasurable_continuumHermiteEffectiveMassIntegrand
    (mass : ℝ) (hmass : 0 < mass) (i j : ℕ) :
    AEStronglyMeasurable (continuumHermiteEffectiveMassIntegrand mass i j) := by
  let F : ℝ × ℝ → ℝ := continuumHermiteEffectiveMassTwoVarIntegrand mass i j
  have hF_meas : AEStronglyMeasurable F (volume.prod volume) := by
    exact
      (continuous_continuumHermiteEffectiveMassTwoVarIntegrand mass hmass i j).aestronglyMeasurable
  convert hF_meas.integral_prod_right' (μ := volume) (ν := volume) using 1
  funext x
  exact continuumHermiteEffectiveMassIntegrand_eq_integral_twoVar mass i j x

omit d N [NeZero N] in
/-- The peeled physical effective-mass integrand is integrable on `ℝ`, by the
explicit kernel majorant proved above. -/
private theorem integrable_continuumHermiteEffectiveMassIntegrand
    (mass : ℝ) (hmass : 0 < mass) (i j : ℕ) :
    Integrable (continuumHermiteEffectiveMassIntegrand mass i j) := by
  rcases continuumHermiteEffectiveMassIntegrand_has_integrable_majorant mass hmass i j with
    ⟨g, hg_int, hg_bound⟩
  exact hg_int.mono'
    (aestronglyMeasurable_continuumHermiteEffectiveMassIntegrand mass hmass i j)
    (ae_of_all _ fun x => (hg_bound x).2)

omit d N [NeZero N] in
/-- The integral of the peeled physical effective-mass integrand can be recovered
from symmetric compact windows `[-R, R]` as `R → ∞`. -/
private theorem tendsto_intervalIntegral_continuumHermiteEffectiveMassIntegrand
    (mass : ℝ) (hmass : 0 < mass) (i j : ℕ) :
    Tendsto
      (fun R : ℕ =>
        ∫ x in (-(R : ℝ))..(R : ℝ),
          continuumHermiteEffectiveMassIntegrand mass i j x)
      atTop
      (nhds (∫ x : ℝ, continuumHermiteEffectiveMassIntegrand mass i j x)) := by
  have ha : Tendsto (fun R : ℕ => -(R : ℝ)) atTop atBot := by
    refine tendsto_atBot.2 ?_
    intro b
    refine Filter.eventually_atTop.2 ?_
    refine ⟨Nat.ceil (-b), ?_⟩
    intro R hR
    have hRb : (-b) ≤ (R : ℝ) := by
      exact le_trans (Nat.le_ceil (-b)) (Nat.cast_le.mpr hR)
    linarith
  exact MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_continuumHermiteEffectiveMassIntegrand mass hmass i j)
    ha tendsto_natCast_atTop_atTop

end Pphi2

end
