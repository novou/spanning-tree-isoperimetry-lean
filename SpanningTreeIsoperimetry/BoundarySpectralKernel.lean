import SpanningTreeIsoperimetry.BoundarySeparatedGreen
import SpanningTreeIsoperimetry.BoundaryTridiagonalGreen

/-! Full finite-y sine separation for every actual rectangular Green entry.
The arbitrary-depth scalar inverse handles either boundary orientation. -/
namespace SpanningTreeIsoperimetry.BoundarySpectralKernel
open ScalarResolvent BoundarySineModes BoundarySeparatedGreen BoundaryTridiagonalGreen
open scoped BigOperators Matrix Kronecker Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def modeOuter (n : ℕ) (j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun a b => mode n j a*mode n j b

theorem modeOuter_path (n : ℕ) (j : Fin n) :
    pathOperator n*modeOuter n j=eigenvalue n j • modeOuter n j := by
  ext a b
  change (∑ x : Fin n, pathOperator n a x*(mode n j x*mode n j b))=_
  have h := congrFun (mode_mulVec n j) a
  change (∑ x : Fin n, pathOperator n a x*mode n j x)=eigenvalue n j*mode n j a at h
  simp only [← mul_assoc,← Finset.sum_mul,h,Matrix.smul_apply,smul_eq_mul,modeOuter]

theorem modeOuter_sum (n : ℕ) :
    (∑ j : Fin n, modeOuter n j)=(((n : ℝ)+1)/2) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext a b
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M a b) (sineMatrix_right_gram n)
  simpa only [Matrix.mul_apply,Matrix.transpose_apply,sineMatrix,modeOuter,Matrix.sum_apply] using h

private theorem kronecker_sub_left (R n : ℕ)
    (A B : Matrix (Fin R) (Fin R) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) :
    (A-B) ⊗ₖ C=A ⊗ₖ C-B ⊗ₖ C := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp only [Matrix.kronecker_apply,Matrix.sub_apply]
  ring

private theorem kronecker_sum_right (R n : ℕ)
    (A : Matrix (Fin R) (Fin R) ℝ) (B : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    A ⊗ₖ (∑ j : Fin n, B j)=∑ j : Fin n, A ⊗ₖ B j := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp only [Matrix.kronecker_apply,Matrix.sum_apply,Finset.mul_sum]

theorem single_mode_inverse (R n : ℕ) (j : Fin n) :
    rectangleDirichlet R n*(kernel R (modeGamma n j) ⊗ₖ modeOuter n j)=
      (1 : Matrix (Fin R) (Fin R) ℝ) ⊗ₖ modeOuter n j := by
  have hs : eigenvalue n j • kernel R (modeGamma n j)-
      (SimpleGraph.pathGraph R).adjMatrix ℝ*kernel R (modeGamma n j)=1 := by
    have h := tridiagonal_mul_kernel R (modeGamma n j) (modeGamma_pos n j)
    simpa only [tridiagonal,Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,← eigenvalue_eq_cosh] using h
  rw [rectangleDirichlet,Matrix.sub_mul,← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,
    Matrix.one_mul,Matrix.one_mul,modeOuter_path,Matrix.kronecker_smul,← Matrix.smul_kronecker,
    ← kronecker_sub_left,hs]

def separatedInverse (R n : ℕ) : Matrix (Fin R × Fin n) (Fin R × Fin n) ℝ :=
  (2/((n : ℝ)+1)) • ∑ j : Fin n, kernel R (modeGamma n j) ⊗ₖ modeOuter n j

theorem rectangle_mul_separatedInverse (R n : ℕ) :
    rectangleDirichlet R n*separatedInverse R n=1 := by
  rw [separatedInverse,Matrix.mul_smul,Finset.mul_sum]
  simp_rw [single_mode_inverse]
  rw [← kronecker_sum_right,modeOuter_sum,Matrix.kronecker_smul,Matrix.one_kronecker_one,smul_smul]
  have hc : (2/((n : ℝ)+1))*(((n : ℝ)+1)/2)=1 := by field_simp
  rw [hc,one_smul]

/-- Complete separation of variables for the actual finite inverse, proved
by multiplying the candidate by the actual rectangular Dirichlet matrix. -/
theorem rectangle_inverse_eq (R n : ℕ) : (rectangleDirichlet R n)⁻¹=separatedInverse R n :=
  Matrix.inv_eq_right_inv (rectangle_mul_separatedInverse R n)

theorem rectangle_inverse_entry (R n : ℕ) (p q : Fin R × Fin n) :
    (rectangleDirichlet R n)⁻¹ p q=
      (2/((n : ℝ)+1))*∑ j : Fin n, mode n j p.2*mode n j q.2*
        kernel R (modeGamma n j) p.1 q.1 := by
  rw [rectangle_inverse_eq]
  simp only [separatedInverse,Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rcases p with ⟨px,py⟩
  rcases q with ⟨qx,qy⟩
  simp only [Matrix.kronecker_apply,modeOuter]
  ring

end
end SpanningTreeIsoperimetry.BoundarySpectralKernel
