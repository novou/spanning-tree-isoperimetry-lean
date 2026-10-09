import SpanningTreeIsoperimetry.JacobiPolynomials

/-! The signed Euclidean chain of a positive Jacobi fraction, proved from
local polynomial division and finite products. -/
namespace SpanningTreeIsoperimetry.SignedJacobiChain

open scoped BigOperators
open Polynomial JacobiPolynomials
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def signedRemainders {K : Type*} [Field K] (P q : Polynomial K) : ℕ → Polynomial K
  | 0 => P
  | 1 => q
  | n + 2 => -(signedRemainders P q n % signedRemainders P q (n + 1))

noncomputable def quotientLeading {K : Type*} [Field K] (P q : Polynomial K) (n : ℕ) : K :=
  (signedRemainders P q n / signedRemainders P q (n + 1)).leadingCoeff

noncomputable def beta (h : ℕ → ℝ) (n : ℕ) : ℝ := h n / h (n - 1)

noncomputable def scale (h : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => h 0
  | n + 2 => scale h n * beta h (n + 1)

noncomputable def weight (h : ℕ → ℝ) (n : ℕ) : ℝ := scale h n / scale h (n + 1)

theorem scale_pos {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (n : ℕ) : 0 < scale h n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [scale]
  | one => exact hh 0
  | more n ih ih1 => exact mul_pos ih (div_pos (hh _) (hh _))

theorem scale_product {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (n : ℕ) :
    scale h n * scale h (n + 1) = h n := by
  induction n with
  | zero => simp [scale]
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by omega, scale]
    simp only [beta, Nat.add_sub_cancel]
    calc
      _ = (scale h n * scale h (n + 1)) * (h (n + 1) / h n) := by ring
      _ = h (n + 1) := by rw [ih]; field_simp [(hh n).ne'] <;> ring

theorem weight_pos {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (n : ℕ) : 0 < weight h n :=
  div_pos (scale_pos hh n) (scale_pos hh (n + 1))

theorem prod_weight_inv {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (k : ℕ) :
    (∏ j ∈ Finset.range k, (weight h j)⁻¹) = scale h k := by
  induction k with
  | zero => simp [scale]
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, weight]
    field_simp [(scale_pos hh k).ne', (scale_pos hh (k + 1)).ne'] <;> ring

theorem norm_eq_weight {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (k : ℕ) :
    h k = scale h k ^ 2 * (weight h k)⁻¹ := by
  rw [← scale_product hh k, weight]
  field_simp [(scale_pos hh k).ne', (scale_pos hh (k + 1)).ne']
  <;> ring

/-- The exponents in the manuscript follow from telescoping the successive
squared norms. -/
theorem norm_product {h : ℕ → ℝ} (hh : ∀ n, 0 < h n) (k : ℕ) :
    (∏ j ∈ Finset.range k, h j) =
      ∏ j ∈ Finset.range k, (weight h j)⁻¹ ^ (2 * k - 2 * j - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ]
    symm
    calc
      _ = (∏ j ∈ Finset.range k, (weight h j)⁻¹ ^ ((2 * k - 2 * j - 1) + 2)) *
          (weight h k)⁻¹ := by
        rw [Finset.prod_range_succ,
          show 2 * (k + 1) - 2 * k - 1 = 1 by omega, pow_one]
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        congr 1
        have := Finset.mem_range.mp hj
        omega
      _ = ((∏ j ∈ Finset.range k, (weight h j)⁻¹ ^ (2 * k - 2 * j - 1)) *
          (∏ j ∈ Finset.range k, (weight h j)⁻¹ ^ 2)) * (weight h k)⁻¹ := by
        simp_rw [pow_add]
        rw [Finset.prod_mul_distrib]
      _ = (∏ j ∈ Finset.range k, h j) * (scale h k ^ 2 * (weight h k)⁻¹) := by
        rw [Finset.prod_pow, prod_weight_inv hh, ← ih]
        ring
      _ = _ := by rw [← norm_eq_weight hh]

/-- All nonterminal signed remainders are the expected positively scaled
trailing characteristic polynomials. -/
theorem signedRemainders_eq {h : ℕ → ℝ} (hh : ∀ n, 0 < h n)
    (a : ℕ → ℝ) {w : ℕ} (hw : 0 < w) (n : ℕ) (hn : n ≤ w) :
    signedRemainders (tailPolynomial a (beta h) w)
      (C (h 0) * tailPolynomial (fun i => a (i + 1)) (fun i => beta h (i + 1)) (w - 1)) n =
      C (scale h n) * tailPolynomial (fun i => a (i + n)) (fun i => beta h (i + n)) (w - n) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [signedRemainders, scale]
  | one => simp [signedRemainders, scale]
  | more n ih ih1 =>
    rw [signedRemainders, ih (by omega), ih1 (by omega)]
    let m := w - (n + 2)
    have hm0 : w - n = m + 2 := by dsimp [m]; omega
    have hm1 : w - (n + 1) = m + 1 := by dsimp [m]; omega
    rw [hm0, hm1]
    have he := scaled_remainder (fun i => a (i + n)) (fun i => beta h (i + n)) m
      (scale h n) (scale h (n + 1)) (scale_pos hh _).ne'
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, scale] using he

/-- The positive weights are the leading coefficients of the actual
polynomial quotients in the signed Euclidean chain. -/
theorem quotientLeading_eq_weight {h : ℕ → ℝ} (hh : ∀ n, 0 < h n)
    (a : ℕ → ℝ) {w : ℕ} (hw : 0 < w) (n : ℕ) (hn : n < w) :
    quotientLeading (tailPolynomial a (beta h) w)
      (C (h 0) * tailPolynomial (fun i => a (i + 1)) (fun i => beta h (i + 1)) (w - 1)) n =
      weight h n := by
  rw [quotientLeading, signedRemainders_eq hh a hw n hn.le,
    signedRemainders_eq hh a hw (n + 1) (by omega)]
  let m := w - (n + 1)
  have hm : w - n = m + 1 := by dsimp [m]; omega
  rw [hm]
  have he := scaled_quotient_leadingCoeff (fun i => a (i + n))
    (fun i => beta h (i + n)) m (scale h n) (scale h (n + 1))
    (scale_pos hh _).ne' (scale_pos hh _).ne'
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, weight] using he

theorem signedRemainders_natDegree {h : ℕ → ℝ} (hh : ∀ n, 0 < h n)
    (a : ℕ → ℝ) {w : ℕ} (hw : 0 < w) (n : ℕ) (hn : n ≤ w) :
    (signedRemainders (tailPolynomial a (beta h) w)
      (C (h 0) * tailPolynomial (fun i => a (i + 1)) (fun i => beta h (i + 1)) (w - 1)) n).natDegree =
      w - n := by
  rw [signedRemainders_eq hh a hw n hn, natDegree_C_mul (scale_pos hh n).ne',
    tailPolynomial_natDegree]

theorem quotient_natDegree {h : ℕ → ℝ} (hh : ∀ n, 0 < h n)
    (a : ℕ → ℝ) {w : ℕ} (hw : 0 < w) (n : ℕ) (hn : n < w) :
    (signedRemainders (tailPolynomial a (beta h) w)
      (C (h 0) * tailPolynomial (fun i => a (i + 1)) (fun i => beta h (i + 1)) (w - 1)) n /
      signedRemainders (tailPolynomial a (beta h) w)
        (C (h 0) * tailPolynomial (fun i => a (i + 1)) (fun i => beta h (i + 1)) (w - 1))
          (n + 1)).natDegree = 1 := by
  rw [signedRemainders_eq hh a hw n hn.le,
    signedRemainders_eq hh a hw (n + 1) (by omega)]
  let m := w - (n + 1)
  have hm : w - n = m + 1 := by dsimp [m]; omega
  rw [hm]
  have he := scaled_quotient_natDegree (fun i => a (i + n))
    (fun i => beta h (i + n)) m (scale h n) (scale h (n + 1))
    (scale_pos hh _).ne' (scale_pos hh _).ne'
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using he

theorem signedRemainders_map {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (P q : Polynomial K) (n : ℕ) :
    (signedRemainders P q n).map f = signedRemainders (P.map f) (q.map f) n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih ih1 => simp only [signedRemainders, Polynomial.map_neg, Polynomial.map_mod, ih, ih1]

theorem quotientLeading_map {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (P q : Polynomial K) (n : ℕ) :
    f (quotientLeading P q n) = quotientLeading (P.map f) (q.map f) n := by
  simp only [quotientLeading, ← Polynomial.leadingCoeff_map f, Polynomial.map_div,
    signedRemainders_map]

end SpanningTreeIsoperimetry.SignedJacobiChain
