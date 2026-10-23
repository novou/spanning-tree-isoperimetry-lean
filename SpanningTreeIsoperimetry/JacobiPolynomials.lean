module

public import SpanningTreeIsoperimetry.ScalarResolvent
public import Mathlib.Algebra.Polynomial.FieldDivision

@[expose] public section

set_option backward.privateInPublic true

/-! Local tridiagonal determinant and Euclidean-division identities. -/
namespace SpanningTreeIsoperimetry.JacobiPolynomials

open scoped BigOperators Matrix Classical
open Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Ring
variable {K : Type*} [CommRing K]

/-- Tridiagonal matrix with arbitrary diagonal, upper weights, and unit lower
weights. The upper weight at column j is b j. -/
def tri (a b : ℕ → K) (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  fun i j => if i = j then a i.1 else if i.1 + 1 = j.1 then b j.1
    else if j.1 + 1 = i.1 then 1 else 0

theorem tri_tail (a b : ℕ → K) (n : ℕ) :
    (tri a b (n + 1)).submatrix Fin.succ Fin.succ =
      tri (fun i => a (i + 1)) (fun i => b (i + 1)) n := by
  ext i j
  simp [tri, Matrix.submatrix_apply, Fin.ext_iff]

private theorem skipOne_zero (n : ℕ) : (1 : Fin (n + 2)).succAbove 0 = 0 := by
  apply Fin.succAbove_ne_zero_zero
  intro h
  have hh : (1 : ℕ) = 0 := congrArg Fin.val h
  omega

private theorem skipOne_succ {n : ℕ} (i : Fin n) :
    (1 : Fin (n + 2)).succAbove i.succ = i.succ.succ := by
  apply Fin.succAbove_of_le_castSucc
  change 1 ≤ i.1 + 1
  omega

private theorem tri_far (a b : ℕ → K) {n : ℕ} (i j : Fin n)
    (h : i.1 + 1 < j.1 ∨ j.1 + 1 < i.1) : tri a b n i j = 0 := by
  unfold tri
  split_ifs with he ha hb
  · have hv := congrArg Fin.val he; omega
  · omega
  · omega
  · rfl

private theorem tri_second_minor (a b : ℕ → K) (n : ℕ) :
    ((tri a b (n + 2)).submatrix Fin.succ (Fin.succAbove 1)).det =
      (tri (fun i => a (i + 2)) (fun i => b (i + 2)) n).det := by
  let M := (tri a b (n + 2)).submatrix Fin.succ (Fin.succAbove 1)
  have h00 : M 0 0 = 1 := by simp [M, skipOne_zero, tri, Fin.ext_iff]
  have hzero (i : Fin n) : M i.succ 0 = 0 := by
    change tri a b (n + 2) i.succ.succ ((1 : Fin (n + 2)).succAbove 0) = 0
    rw [skipOne_zero]
    apply tri_far
    right
    change 0 + 1 < i.1 + 1 + 1
    omega
  have hminor : M.submatrix Fin.succ Fin.succ =
      tri (fun i => a (i + 2)) (fun i => b (i + 2)) n := by
    ext i j
    change tri a b (n + 2) i.succ.succ ((1 : Fin (n + 2)).succAbove j.succ) = _
    rw [skipOne_succ]
    simp [tri, Fin.ext_iff]
  change M.det = _
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h00, hzero, hminor]

/-- Two checked Laplace expansions give the weighted determinant recurrence. -/
theorem tri_det_recurrence (a b : ℕ → K) (n : ℕ) :
    (tri a b (n + 2)).det =
      a 0 * (tri (fun i => a (i + 1)) (fun i => b (i + 1)) (n + 1)).det -
        b 1 * (tri (fun i => a (i + 2)) (fun i => b (i + 2)) n).det := by
  have h00 : tri a b (n + 2) 0 0 = a 0 := by simp [tri]
  have h01 : tri a b (n + 2) 0 1 = b 1 := by simp [tri, Fin.ext_iff]
  have hzero (i : Fin n) : tri a b (n + 2) 0 i.succ.succ = 0 := by
    apply tri_far
    left
    change 0 + 1 < i.1 + 1 + 1
    omega
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [h00, h01, hzero, tri_tail, tri_second_minor, sub_eq_add_neg]

end Ring

noncomputable def jacobiMatrix (a b : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  -tri (fun i => -a i) b n

noncomputable def tailPolynomial (a b : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  (tri (fun i => X - C (a i)) (fun i => C (b i)) n).det

theorem jacobiMatrix_charmatrix (a b : ℕ → ℝ) (n : ℕ) :
    (jacobiMatrix a b n).charmatrix =
      tri (fun i => X - C (a i)) (fun i => C (b i)) n := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.charmatrix, Matrix.scalar, Matrix.diagonal_apply, jacobiMatrix, tri]
  · simp only [Matrix.charmatrix_apply_ne _ _ _ hij, jacobiMatrix, Matrix.neg_apply,
      tri, hij, ite_false]
    split_ifs <;> simp

theorem tailPolynomial_eq_charpoly (a b : ℕ → ℝ) (n : ℕ) :
    tailPolynomial a b n = (jacobiMatrix a b n).charpoly := by
  rw [Matrix.charpoly, jacobiMatrix_charmatrix]
  rfl

theorem tailPolynomial_monic (a b : ℕ → ℝ) (n : ℕ) : (tailPolynomial a b n).Monic := by
  rw [tailPolynomial_eq_charpoly]
  exact Matrix.charpoly_monic _

@[simp] theorem tailPolynomial_leadingCoeff (a b : ℕ → ℝ) (n : ℕ) :
    (tailPolynomial a b n).leadingCoeff = 1 :=
  (tailPolynomial_monic a b n).leadingCoeff

theorem tailPolynomial_natDegree (a b : ℕ → ℝ) (n : ℕ) :
    (tailPolynomial a b n).natDegree = n := by
  rw [tailPolynomial_eq_charpoly, Matrix.charpoly_natDegree_eq_dim]
  simp

@[simp] theorem tailPolynomial_zero (a b : ℕ → ℝ) : tailPolynomial a b 0 = 1 := by
  simp [tailPolynomial, Matrix.det_isEmpty]

@[simp] theorem tailPolynomial_one (a b : ℕ → ℝ) : tailPolynomial a b 1 = X - C (a 0) := by
  simp [tailPolynomial, Matrix.det_fin_one, tri]

theorem tailPolynomial_recurrence (a b : ℕ → ℝ) (n : ℕ) :
    tailPolynomial a b (n + 2) =
      (X - C (a 0)) * tailPolynomial (fun i => a (i + 1)) (fun i => b (i + 1)) (n + 1) -
        C (b 1) * tailPolynomial (fun i => a (i + 2)) (fun i => b (i + 2)) n :=
  tri_det_recurrence _ _ n

theorem tailPolynomial_eval (a b : ℕ → ℝ) (n : ℕ) (z : ℝ) :
    (tailPolynomial a b n).eval z = (tri (fun i => z - a i) b n).det := by
  change (Polynomial.evalRingHom z) (tri (fun i => X - C (a i)) (fun i => C (b i)) n).det = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  change (tri (fun i => X - C (a i)) (fun i => C (b i)) n i j).eval z = _
  simp only [tri]
  split_ifs <;> simp

theorem shifted_jacobiMatrix (a b : ℕ → ℝ) (n : ℕ) (z : ℝ) :
    z • (1 : Matrix (Fin n) (Fin n) ℝ) - jacobiMatrix a b n =
      tri (fun i => z - a i) b n := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [jacobiMatrix, tri, Matrix.one_apply]
  · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, hij, ite_false, mul_zero, jacobiMatrix, Matrix.neg_apply,
      zero_sub, neg_neg, tri]

/-- Cofactor calculation of the endpoint resolvent for the weighted
tridiagonal matrix, valid for Lean's total inverse as well. -/
theorem endpoint_resolvent (a b : ℕ → ℝ) (n : ℕ) (z : ℝ) :
    ((z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) - jacobiMatrix a b (n + 1))⁻¹) 0 0 =
      (tailPolynomial (fun i => a (i + 1)) (fun i => b (i + 1)) n).eval z /
        (tailPolynomial a b (n + 1)).eval z := by
  rw [shifted_jacobiMatrix, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_zero, zero_add, pow_zero, one_mul, Fin.succAbove_zero,
    tri_tail, Ring.inverse_eq_inv, tailPolynomial_eval]
  ring

/-- The signed Euclidean remainder is precisely the next weighted trailing
characteristic polynomial. No continued-fraction identity is assumed. -/
theorem scaled_remainder (a b : ℕ → ℝ) (n : ℕ) (c d : ℝ) (hd : d ≠ 0) :
    -(C c * tailPolynomial a b (n + 2) %
        (C d * tailPolynomial (fun i => a (i + 1)) (fun i => b (i + 1)) (n + 1))) =
      C (c * b 1) * tailPolynomial (fun i => a (i + 2)) (fun i => b (i + 2)) n := by
  let Q := tailPolynomial (fun i => a (i + 1)) (fun i => b (i + 1)) (n + 1)
  let T := tailPolynomial (fun i => a (i + 2)) (fun i => b (i + 2)) n
  have hQ : C d * Q ≠ 0 := mul_ne_zero (C_ne_zero.mpr hd)
    (tailPolynomial_monic _ _ _).ne_zero
  have hsmall : (-C (c * b 1) * T).degree < (C d * Q).degree := by
    apply degree_lt_degree
    calc
      (-C (c * b 1) * T).natDegree ≤ T.natDegree := by
        rw [neg_mul, natDegree_neg]
        exact natDegree_C_mul_le _ _
      _ < (C d * Q).natDegree := by
        rw [natDegree_C_mul hd]
        simp only [Q, T, tailPolynomial_natDegree]
        omega
  have hcd : C d * C (c / d) = C c := by
    rw [← C_mul]
    congr 1
    field_simp [hd]
  have hdiv : C d * Q ∣ C c * tailPolynomial a b (n + 2) - (-C (c * b 1) * T) := by
    refine ⟨C (c / d) * (X - C (a 0)), ?_⟩
    rw [tailPolynomial_recurrence]
    change C c * ((X - C (a 0)) * Q - C (b 1) * T) - (-C (c * b 1) * T) = _
    rw [map_mul]
    calc
      _ = C c * ((X - C (a 0)) * Q) := by ring
      _ = (C d * Q) * (C (c / d) * (X - C (a 0))) := by rw [← hcd]; ring
  have hm := Polynomial.mod_eq_of_dvd_sub hdiv
  rw [(Polynomial.mod_eq_self_iff hQ).mpr hsmall] at hm
  rw [hm]
  simp only [neg_mul, neg_neg]
  rfl

theorem scaled_quotient_leadingCoeff (a b : ℕ → ℝ) (n : ℕ) (c d : ℝ)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    (C c * tailPolynomial a b (n + 1) /
      (C d * tailPolynomial (fun i => a (i + 1)) (fun i => b (i + 1)) n)).leadingCoeff = c / d := by
  rw [Polynomial.leadingCoeff_div]
  · simp only [leadingCoeff_mul, leadingCoeff_C, tailPolynomial_leadingCoeff, mul_one]
  · rw [degree_C_mul hc, degree_C_mul hd]
    exact (degree_lt_degree (by simp only [tailPolynomial_natDegree]; omega)).le

theorem scaled_quotient_natDegree (a b : ℕ → ℝ) (n : ℕ) (c d : ℝ)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    (C c * tailPolynomial a b (n + 1) /
      (C d * tailPolynomial (fun i => a (i + 1)) (fun i => b (i + 1)) n)).natDegree = 1 := by
  rw [Polynomial.div_C_mul, natDegree_C_mul (inv_ne_zero hd),
    ← Polynomial.divByMonic_eq_div _ (tailPolynomial_monic _ _ _),
    natDegree_divByMonic _ (tailPolynomial_monic _ _ _), natDegree_C_mul hc,
    tailPolynomial_natDegree, tailPolynomial_natDegree]
  omega

end SpanningTreeIsoperimetry.JacobiPolynomials
