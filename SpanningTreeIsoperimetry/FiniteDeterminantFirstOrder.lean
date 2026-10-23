module

public import SpanningTreeIsoperimetry.FiniteDeterminantContinuity
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Degree

@[expose] public section

/-! A dimension-independent first-order determinant remainder, using the
actual principal-minor coefficient formula and the checked row-sum bound. -/
namespace SpanningTreeIsoperimetry.FiniteDeterminantFirstOrder
open FiniteDeterminantContinuity Matrix Polynomial
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem abs_eval_one_le {p q : ℝ[X]} (h : ∀ k,|p.coeff k|≤q.coeff k) :
    |p.eval 1|≤q.eval 1 := by
  let N := max p.natDegree q.natDegree+1
  have hp := Polynomial.eval_eq_sum_range' (p := p) (n := N) (by dsimp [N]; omega) (1 : ℝ)
  have hq := Polynomial.eval_eq_sum_range' (p := q) (n := N) (by dsimp [N]; omega) (1 : ℝ)
  rw [hp,hq]
  simp only [one_pow,mul_one]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => h k))

private theorem rowMass_principal_le (M : Matrix ι ι ℝ) (s : Finset ι) (i : s) :
    rowMass (M.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)) i≤rowMass M i.val := by
  let r : ι → ℝ := fun j => |M i.val j|
  change (∑ j : s,r j.val)≤∑ j : ι,r j
  rw [Finset.sum_coe_sort]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    (fun j _ _ => show 0≤r j from abs_nonneg _)

def massDiagonal (M : Matrix ι ι ℝ) : Matrix ι ι ℝ := Matrix.diagonal (rowMass M)

private theorem principal_diag_det (M : Matrix ι ι ℝ) (s : Finset ι) :
    ((massDiagonal M).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)).det=
      ∏ i : s,rowMass M i.val := by
  have he : (massDiagonal M).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)=
      Matrix.diagonal (fun i : s => rowMass M i.val) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp [massDiagonal,Matrix.submatrix_apply]
    · have hv : i.val≠j.val := fun h => hij (Subtype.ext h)
      simp [massDiagonal,Matrix.submatrix_apply,Matrix.diagonal_apply,hij,hv]
  rw [he,Matrix.det_diagonal]

theorem principal_det_bound (M : Matrix ι ι ℝ) (s : Finset ι) :
    |(M.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)).det|≤
      ((massDiagonal M).submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)).det := by
  rw [principal_diag_det]
  apply (abs_det_le_prod_rowMass _).trans
  apply Finset.prod_le_prod₀
  · intro i _
    exact rowMass_nonneg _ i
  · intro i _
    exact rowMass_principal_le M s i

def detPolynomial (M : Matrix ι ι ℝ) : ℝ[X] :=
  (1+(X : ℝ[X]) • M.map C).det

theorem coefficient_bound (M : Matrix ι ι ℝ) (k : ℕ) :
    |(detPolynomial M).coeff k|≤(detPolynomial (massDiagonal M)).coeff k := by
  rw [detPolynomial,detPolynomial,Matrix.coeff_det_one_add_X_smul_eq_sum_minors,
    Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun s _ => principal_det_bound M s))

private theorem massDiagonal_trace (M : Matrix ι ι ℝ) : (massDiagonal M).trace=mass M := by
  rw [massDiagonal,Matrix.trace_diagonal]
  rfl

private theorem massDiagonal_det (M : Matrix ι ι ℝ) :
    (1+massDiagonal M).det=∏ i,(1+rowMass M i) := by
  have he : (1+massDiagonal M : Matrix ι ι ℝ)=Matrix.diagonal (fun i => 1+rowMass M i) := by
    ext i j
    by_cases hij : i=j <;> simp [massDiagonal,Matrix.add_apply,Matrix.one_apply,Matrix.diagonal_apply,hij]
  rw [he,Matrix.det_diagonal]

private theorem product_mass_le_exp (M : Matrix ι ι ℝ) :
    (∏ i,(1+rowMass M i))≤Real.exp (mass M) := by
  calc
    (∏ i,(1+rowMass M i))≤∏ i,Real.exp (rowMass M i) := by
      apply Finset.prod_le_prod₀
      · intro i _
        linarith [rowMass_nonneg M i]
      · intro i _
        simpa only [add_comm] using Real.add_one_le_exp (rowMass M i)
    _=Real.exp (mass M) := by rw [← Real.exp_sum]; rfl

/-- No factor depending on the number of rows appears in the remainder. -/
theorem determinant_first_order (M : Matrix ι ι ℝ) :
    |(1+M).det-1-M.trace|≤Real.exp (mass M)-1-mass M := by
  let p := detPolynomial M
  let q := detPolynomial (massDiagonal M)
  have hp : (1+M).det=1+M.trace+p.divX.divX.eval 1 := by
    simpa only [one_smul,mul_one,one_pow,p,detPolynomial] using Matrix.det_one_add_smul (1 : ℝ) M
  have hq : (1+massDiagonal M).det=1+(massDiagonal M).trace+q.divX.divX.eval 1 := by
    simpa only [one_smul,mul_one,one_pow,q,detPolynomial] using Matrix.det_one_add_smul (1 : ℝ) (massDiagonal M)
  have hb : |p.divX.divX.eval 1|≤q.divX.divX.eval 1 := by
    apply abs_eval_one_le
    intro k
    simpa only [Polynomial.coeff_divX,p,q] using coefficient_bound M (k+1+1)
  have he : (1+M).det-1-M.trace=p.divX.divX.eval 1 := by linarith only [hp]
  rw [he]
  apply hb.trans
  rw [massDiagonal_trace,massDiagonal_det] at hq
  linarith only [hq,product_mass_le_exp M]

end
end SpanningTreeIsoperimetry.FiniteDeterminantFirstOrder
