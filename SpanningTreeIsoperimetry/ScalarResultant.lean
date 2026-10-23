module

public import SpanningTreeIsoperimetry.ScalarModular
public import SpanningTreeIsoperimetry.LayerDeterminant
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

@[expose] public section

set_option backward.privateInPublic true

/-! The rectangle factor is the exact polynomial resultant used by the
counting algorithm. -/
namespace SpanningTreeIsoperimetry.ScalarResultant

open scoped BigOperators Matrix Classical
open Polynomial ScalarResolvent ScalarModular
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem aeval_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (p : Polynomial ℝ) :
    aeval (Matrix.diagonal d) p = Matrix.diagonal (fun i => p.eval (d i)) := by
  have h := Polynomial.aeval_algHom_apply (Matrix.diagonalAlgHom (R := ℝ) (α := ℝ) (n := ι)) d p
  change aeval (Matrix.diagonal d) p = Matrix.diagonal (aeval d p) at h
  rw [h]
  congr 1
  funext i
  rw [Polynomial.aeval_pi_apply]
  rfl

/-- Spectral conjugation computes the determinant of every evaluated polynomial. -/
theorem det_aeval_eq_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (p : Polynomial ℝ) :
    (aeval A p).det = ∏ i, p.eval (hA.eigenvalues i) := by
  let D : Matrix ι ι ℝ := Matrix.diagonal hA.eigenvalues
  let U := hA.eigenvectorUnitary
  let φ := Unitary.conjStarAlgAut ℝ _ U
  have hs : A = φ D := by simpa [φ, U, D, Function.comp_def] using hA.spectral_theorem
  conv_lhs => rw [hs]
  rw [Polynomial.aeval_algHom_apply, aeval_diagonal]
  rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul]
  have hu := congrArg Matrix.det (Unitary.coe_mul_star_self U)
  rw [Matrix.det_mul, Matrix.det_one] at hu
  change (U : Matrix ι ι ℝ).det * (star (U : Matrix ι ι ℝ)).det = 1 at hu
  calc
    _ = (Matrix.diagonal (fun i => p.eval (hA.eigenvalues i))).det *
        ((U : Matrix ι ι ℝ).det * (star (U : Matrix ι ι ℝ)).det) := by ring
    _ = _ := by rw [hu, mul_one, Matrix.det_diagonal]

/-- The resultant with a real Hermitian characteristic polynomial is its
polynomial-evaluation determinant. -/
theorem det_aeval_eq_resultant {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (p : Polynomial ℝ) :
    (aeval A p).det = A.charpoly.resultant p := by
  rw [det_aeval_eq_prod hA, hA.charpoly_eq]
  rw [Polynomial.resultant_prod_left Finset.univ _ p p.natDegree (by simp) le_rfl]
  simp only [Polynomial.natDegree_X_sub_C, Polynomial.resultant_X_sub_C_left _ _ _ le_rfl,
    RCLike.ofReal_real_eq_id, id_eq]

theorem rectangleDirichlet_det_eq_resultant (R w : ℕ) :
    (rectangleDirichlet R w).det =
      (pathPolynomial w).resultant (SmallCases.continuant (X : Polynomial ℝ) R) := by
  have hB : (pathOperator w).IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.IsSymm, Matrix.conjTranspose_eq_transpose_of_trivial] using
      pathOperator_isSymm w
  rw [LayerDeterminant.rectangleDirichlet_det_eq_continuant, operatorContinuant_eq_aeval,
    det_aeval_eq_resultant hB, pathOperator_charpoly]

noncomputable def rectangleFactor (R w : ℕ) : ℚ :=
  (rationalPathPolynomial w).resultant (SmallCases.continuant (X : Polynomial ℚ) R)

theorem rectangleFactor_cast (R w : ℕ) :
    (algebraMap ℚ ℝ) (rectangleFactor R w) = (rectangleDirichlet R w).det := by
  rw [rectangleDirichlet_det_eq_resultant, ← rationalPathPolynomial_map w,
    ← rationalContinuant_map R, Polynomial.natDegree_map, Polynomial.natDegree_map,
    Polynomial.resultant_map_map]
  rfl

/-- The good-prime test is exactly the condition for the polynomial inverse,
for a monic denominator over an arbitrary field. -/
theorem resultant_nonzero_iff_coprime {K : Type*} [Field K] {P f : Polynomial K}
    (hP : P.Monic) : P.resultant f ≠ 0 ↔ IsCoprime P f := by
  rw [← isUnit_iff_ne_zero, Polynomial.isUnit_resultant_iff_isCoprime hP]

end SpanningTreeIsoperimetry.ScalarResultant
