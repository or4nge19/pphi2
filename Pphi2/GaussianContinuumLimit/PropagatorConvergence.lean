/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lattice Propagator Convergence

The main analytical content of the Gaussian continuum limit: the lattice
Green's function converges to the continuum Green's function as a → 0.

## Main results

- `propagator_convergence` — (axiom) lattice Riemann sum → continuum integral
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

noncomputable section

open GaussianField MeasureTheory Filter

namespace Pphi2

variable (d N : ℕ) [NeZero N]

/-! ## Propagator convergence -/

/-- **Lattice propagator converges to continuum Green's function.**

For Schwartz test functions f, g and lattice parameters a → 0 with Na → ∞:

  `embeddedTwoPoint d N a mass f g → continuumGreenBilinear d mass f g`

Mathematically, this says the Riemann sum:

  `a^{2d} Σ_{x,y ∈ Λ} C_a(x,y) f(ax) g(ay)`

converges to:

  `∫ f̂(k) ĝ(k) / (|k|² + m²) dk / (2π)^d`

The proof has three ingredients:
1. In Fourier space, the lattice eigenvalues `(4/a²)sin²(πk/N) + m²`
   approximate `|k|² + m²` for each mode k.
2. The Riemann sum over lattice momenta approximates the Fourier integral.
3. Schwartz decay of f̂, ĝ provides dominated convergence (the tails
   are uniformly bounded by `C · |k|^{-M}` for any M).

Reference: Glimm-Jaffe §6.1, Simon Ch. I. -/
axiom propagator_convergence
    (mass : ℝ) (hmass : 0 < mass)
    (f g : ContinuumTestFunction d)
    -- Sequence of lattice spacings tending to 0
    (a_seq : ℕ → ℝ) (ha_pos : ∀ n, 0 < a_seq n)
    (ha_lim : Tendsto a_seq atTop (nhds 0))
    -- Sequence of lattice sizes with N_n · a_n → ∞
    (N_seq : ℕ → ℕ) [∀ n, NeZero (N_seq n)]
    (hNa : Tendsto (fun n => (N_seq n : ℝ) * a_seq n) atTop atTop) :
    Tendsto
      (fun n => embeddedTwoPoint d (N_seq n) (a_seq n) mass (ha_pos n) hmass f g)
      atTop
      (nhds (continuumGreenBilinear d mass f g))

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
            simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
              star_trivial] at hinner
            -- hinner: ∑ i, e_k(i) * e_j(i) = if j = k then 1 else 0
            rw [← hinner]
            apply Finset.sum_congr rfl; intro x _; ring
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

/-- **Schwartz Riemann sum bound.**

For a Schwartz function f : S(ℝ^d) and the lattice (ℤ/Nℤ)^d with spacing a,
the weighted sum `a^d · Σ_{x} |f(a·x)|²` is bounded uniformly in a ∈ (0,1] and N.

This is a standard fact: the Riemann sum approximates `‖f‖²_{L²(ℝ^d)}`, and since
f is Schwartz (hence rapidly decaying), the sum converges uniformly and is bounded
by a constant depending only on f.

More precisely: `|f(y)| ≤ C_n (1+|y|)^{-n}` for all n, so
`a^d Σ_x f(ax)² ≤ C² · a^d Σ_x (1+a|x|)^{-2n}`, and for 2n > d the sum converges
to at most `∫ (1+|y|)^{-2n} dy < ∞`. -/
private axiom schwartz_riemann_sum_bound
    (f : ContinuumTestFunction d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∀ (N : ℕ) [NeZero N],
    a ^ d * ∑ x : FinLatticeSites d N, (evalAtSite d N a f x) ^ 2 ≤ C

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

end Pphi2

end
