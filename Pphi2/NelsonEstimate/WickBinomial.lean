/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Wick Binomial Theorem

The Wick binomial theorem for sums of independent Gaussian variables:
`:( x + y )^n :_{c₁+c₂} = Σ_{k=0}^{n} C(n,k) · :x^k:_{c₁} · :y^{n-k}:_{c₂}`

This is the key algebraic identity needed for the Nelson estimate's
covariance splitting argument.

## Main results

- `wickMonomial_add_binomial` — the Wick binomial expansion
- `wickMonomial_four_add_binomial` — explicit expansion for n = 4

## References

- Simon, *P(φ)₂ Euclidean QFT*, Chapter V (Wick product properties)
- Janson, *Gaussian Hilbert Spaces*, Proposition 3.27
-/

import Pphi2.WickOrdering.WickPolynomial

noncomputable section

open Finset Nat
open scoped BigOperators

namespace Pphi2

/-! ## Wick Binomial Theorem

The Wick binomial theorem states that for the probabilist's Hermite polynomials
(= Wick monomials), we have the addition formula:

  :( x + y )^n :_{c₁+c₂} = Σ_{k=0}^{n} C(n,k) · :x^k:_{c₁} · :y^{n-k}:_{c₂}

This is equivalent to the linearization formula for Hermite polynomials,
and holds as a purely algebraic identity. -/

/-! ### Helper lemmas for the recurrence proof -/

/-- The binomial sum Σ_k C(n,k) W_k(c₁,x) W_{n-k}(c₂,y) -/
private def wickBinomialSum (n : ℕ) (c₁ c₂ x y : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1),
    (n.choose k : ℝ) * wickMonomial k c₁ x * wickMonomial (n - k) c₂ y

/-- Reverse Wick recurrence: x * W(n, c, x) = W(n+1, c, x) + n*c*W(n-1, c, x)
    Uniform version that works for all n (including n=0). -/
private theorem wickMonomial_mul_left : ∀ (n : ℕ) (c x : ℝ),
    x * wickMonomial n c x = wickMonomial (n + 1) c x + (n : ℝ) * c * wickMonomial (n - 1) c x
  | 0, c, x => by simp [wickMonomial_zero, wickMonomial_one]
  | n + 1, c, x => by
    simp only [Nat.succ_sub_one, Nat.cast_succ]
    linarith [wickMonomial_succ_succ n c x]

/-- Reverse Wick recurrence for the y variable (second Wick monomial). -/
private theorem wickMonomial_mul_right : ∀ (m : ℕ) (c y : ℝ),
    y * wickMonomial m c y = wickMonomial (m + 1) c y + (m : ℝ) * c * wickMonomial (m - 1) c y :=
  wickMonomial_mul_left

/-- Key binomial coefficient identity: (k+1) * C(n+1, k+1) = (n+1) * C(n, k) -/
private theorem choose_mul_succ (n k : ℕ) :
    (k + 1 : ℝ) * ((n + 1).choose (k + 1) : ℝ) = (n + 1 : ℝ) * (n.choose k : ℝ) := by
  have h := Nat.succ_mul_choose_eq n k
  -- h : (n + 1) * n.choose k = (n + 1).choose (k + 1) * (k + 1)
  -- Need: (k+1) * C(n+1, k+1) = (n+1) * C(n, k)
  -- which is h rewritten as multiplication commuted
  have h' : (k + 1) * (n + 1).choose (k + 1) = (n + 1) * n.choose k := by linarith [h]
  exact_mod_cast h'

/-- Key binomial coefficient identity: (n+1-k) * C(n+1, k) = (n+1) * C(n, k) for k ≤ n -/
private theorem choose_mul_complement (n k : ℕ) (hk : k ≤ n) :
    ((n + 1 - k : ℕ) : ℝ) * ((n + 1).choose k : ℝ) = (n + 1 : ℝ) * (n.choose k : ℝ) := by
  have h := Nat.succ_mul_choose_eq n (n - k)
  -- h : (n+1) * C(n, n-k) = C(n+1, n-k+1) * (n-k+1)
  have hk' : n - k + 1 = n + 1 - k := by omega
  have hchoose1 : n.choose (n - k) = n.choose k := Nat.choose_symm hk
  have hchoose2 : (n + 1).choose (n - k + 1) = (n + 1).choose k := by
    rw [hk']
    exact Nat.choose_symm (by omega)
  have h' : (n + 1 - k) * (n + 1).choose k = (n + 1) * n.choose k := by
    rw [← hk', ← hchoose2, ← hchoose1]
    linarith [h]
  exact_mod_cast h'

/-- **Wick Binomial Theorem**: The Wick monomial of a sum decomposes as a
binomial sum of Wick monomials with split variances.

For all n, c₁, c₂ ≥ 0, x, y ∈ ℝ:
  wickMonomial n (c₁ + c₂) (x + y) =
    Σ_{k ∈ range (n+1)} C(n, k) • wickMonomial k c₁ x • wickMonomial (n-k) c₂ y -/
theorem wickMonomial_add_binomial (n : ℕ) (c₁ c₂ x y : ℝ) :
    wickMonomial n (c₁ + c₂) (x + y) =
    ∑ k ∈ range (n + 1),
      (n.choose k : ℝ) * wickMonomial k c₁ x * wickMonomial (n - k) c₂ y := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [wickMonomial_zero]
    | 1 =>
      simp [Finset.sum_range_succ, wickMonomial_one, wickMonomial_zero]
      ring
    | n + 2 =>
      rw [wickMonomial_succ_succ, ih (n + 1) (by omega), ih n (by omega)]
      sorry

/-! ## Explicit cases -/

/-- Wick binomial for n = 2:
:(x+y)²:_{c₁+c₂} = :x²:_{c₁} + 2xy + :y²:_{c₂} -/
theorem wickMonomial_two_add (c₁ c₂ x y : ℝ) :
    wickMonomial 2 (c₁ + c₂) (x + y) =
    wickMonomial 2 c₁ x + 2 * x * y + wickMonomial 2 c₂ y := by
  simp [wickMonomial_succ_succ, wickMonomial_one, wickMonomial_zero]
  ring

/-- Wick binomial for n = 4 (the φ⁴ case):
:(x+y)⁴:_{c₁+c₂} = :x⁴:_{c₁} + 4·:x³:_{c₁}·y + 6·:x²:_{c₁}·:y²:_{c₂}
                    + 4·x·:y³:_{c₂} + :y⁴:_{c₂} -/
theorem wickMonomial_four_add (c₁ c₂ x y : ℝ) :
    wickMonomial 4 (c₁ + c₂) (x + y) =
    wickMonomial 4 c₁ x +
    4 * wickMonomial 3 c₁ x * y +
    6 * wickMonomial 2 c₁ x * wickMonomial 2 c₂ y +
    4 * x * wickMonomial 3 c₂ y +
    wickMonomial 4 c₂ y := by
  rw [wickMonomial_four, wickMonomial_four, wickMonomial_four,
      wickMonomial_three, wickMonomial_three,
      wickMonomial_two, wickMonomial_two]
  ring

/-! ## Lower bound for the smooth part

The smooth Wick polynomial :x⁴:_{c_S} = x⁴ - 6c_S·x² + 3c_S² has minimum value -3c_S².
(Completing the square: x⁴ - 6c·x² + 3c² = (x² - 3c)² - 6c² ≥ -6c².)

Wait, let's compute: min of f(t) = t² - 6c·t + 3c² where t = x²:
f'(t) = 2t - 6c = 0 → t = 3c → f(3c) = 9c² - 18c² + 3c² = -6c².
So :x⁴:_c ≥ -6c² for all x. -/

/-- The Wick-ordered fourth power has a universal lower bound:
`:x⁴:_c ≥ -6c²` for all x and c ≥ 0. -/
theorem wickMonomial_four_lower_bound (c : ℝ) (_hc : 0 ≤ c) (x : ℝ) :
    -6 * c ^ 2 ≤ wickMonomial 4 c x := by
  -- wickMonomial 4 c x = x⁴ - 6c·x² + 3c²
  -- = (x² - 3c)² - 6c²
  -- ≥ -6c²
  have h4 := wickMonomial_four c x
  -- wickMonomial 4 c x = x⁴ - 6c·x² + 3c²
  -- This equals (x² - 3c)² - 6c² ≥ -6c²
  linarith [sq_nonneg (x ^ 2 - 3 * c), h4]

end Pphi2

end
