module

public import SpanningTreeIsoperimetry.EuclideanHankel

@[expose] public section

/-! Simultaneous tridiagonal reduction of the actual path operator and its
positive commuting boundary Green form. -/
namespace SpanningTreeIsoperimetry.JacobiReduction

open scoped BigOperators Matrix Classical
open ScalarResolvent EuclideanHankel Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Zero entries strictly below the first subdiagonal. -/
def UpperHessenberg {w : ℕ} (M : Matrix (Fin w) (Fin w) ℝ) : Prop :=
  ∀ i j, j.1 + 1 < i.1 → M i j = 0

def UnitSubdiagonal {w : ℕ} (M : Matrix (Fin w) (Fin w) ℝ) : Prop :=
  ∀ i j, i.1 = j.1 + 1 → M i j = -1

theorem pathOperator_upperHessenberg (w : ℕ) : UpperHessenberg (pathOperator w) :=
  fun i j h => pathOperator_below i j h

theorem pathOperator_unitSubdiagonal (w : ℕ) : UnitSubdiagonal (pathOperator w) := by
  intro i j hij
  rw [pathOperator_apply]
  have hne : i ≠ j := by intro h; have := congrArg Fin.val h; omega
  simp [hne, hij]

theorem mul_upper_right {w : ℕ} {M T : Matrix (Fin w) (Fin w) ℝ}
    (hM : UpperHessenberg M) (hT : T.IsUpperTriangular) : UpperHessenberg (M * T) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : j < k
  · rw [hT hk, mul_zero]
  · rw [hM i k (by change k.1 + 1 < i.1; change ¬j.1 < k.1 at hk; omega), zero_mul]

theorem mul_upper_left {w : ℕ} {M T : Matrix (Fin w) (Fin w) ℝ}
    (hM : UpperHessenberg M) (hT : T.IsUpperTriangular) : UpperHessenberg (T * M) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k < i
  · rw [hT hk, zero_mul]
  · rw [hM k j (by change ¬k.1 < i.1 at hk; omega), mul_zero]

theorem subdiagonal_mul_upper_right {w : ℕ} {M T : Matrix (Fin w) (Fin w) ℝ}
    (hM : UpperHessenberg M) (hsub : UnitSubdiagonal M)
    (hT : T.IsUpperTriangular) (hdiag : ∀ i, T i i = 1) : UnitSubdiagonal (M * T) := by
  intro i j hij
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [hsub i j hij, hdiag, mul_one]
  · intro k _ hkj
    by_cases hk : j < k
    · rw [hT hk, mul_zero]
    · have hval : k.1 ≠ j.1 := fun h => hkj (Fin.ext h)
      rw [hM i k (by change ¬j.1 < k.1 at hk; omega), zero_mul]
  · simp

theorem subdiagonal_mul_upper_left {w : ℕ} {M T : Matrix (Fin w) (Fin w) ℝ}
    (hM : UpperHessenberg M) (hsub : UnitSubdiagonal M)
    (hT : T.IsUpperTriangular) (hdiag : ∀ i, T i i = 1) : UnitSubdiagonal (T * M) := by
  intro i j hij
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hsub i j hij, hdiag, one_mul]
  · intro k _ hki
    by_cases hk : k < i
    · rw [hT hk, zero_mul]
    · have hval : k.1 ≠ i.1 := fun h => hki (Fin.ext h)
      rw [hM k j (by change ¬k.1 < i.1 at hk; omega), mul_zero]
  · simp

theorem upper_mul_diagonal {w : ℕ} {A B : Matrix (Fin w) (Fin w) ℝ}
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin w) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

section Actual
variable {R w : ℕ} (hR : 0 < R)

noncomputable def basisMatrix : Matrix (Fin w) (Fin w) ℝ :=
  (LDL.lowerInv (boundaryGreen_posDef hR w))ᵀ

noncomputable def jacobi : Matrix (Fin w) (Fin w) ℝ :=
  (basisMatrix (w := w) hR)⁻¹ * pathOperator w * basisMatrix (w := w) hR

noncomputable def squaredNorm (i : Fin w) : ℝ :=
  LDL.diagEntries (boundaryGreen_posDef hR w) i

theorem basisMatrix_upper : (basisMatrix (w := w) hR).IsUpperTriangular :=
  (LDL.isLowerTriangular_lowerInv (boundaryGreen_posDef hR w)).transpose

theorem basisMatrix_diagonal (i : Fin w) : basisMatrix (w := w) hR i i = 1 :=
  lowerInv_diagonal (boundaryGreen_posDef hR w) i

theorem basisMatrix_isUnit : IsUnit (basisMatrix (w := w) hR) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [basisMatrix, Matrix.det_transpose, lowerInv_det]
  exact isUnit_one

theorem basisMatrix_inverse_upper : ((basisMatrix (w := w) hR)⁻¹).IsUpperTriangular := by
  letI := (basisMatrix_isUnit (w := w) hR).nonempty_invertible.some
  exact Matrix.blockTriangular_inv_of_blockTriangular (basisMatrix_upper hR)

theorem basisMatrix_inverse_diagonal (i : Fin w) : (basisMatrix (w := w) hR)⁻¹ i i = 1 := by
  have h := congrArg (fun M : Matrix (Fin w) (Fin w) ℝ => M i i)
    (Matrix.mul_nonsing_inv (basisMatrix (w := w) hR)
      ((Matrix.isUnit_iff_isUnit_det _).mp (basisMatrix_isUnit hR)))
  rw [upper_mul_diagonal (basisMatrix_upper hR) (basisMatrix_inverse_upper hR),
    basisMatrix_diagonal, one_mul, Matrix.one_apply_eq] at h
  exact h

theorem jacobi_upperHessenberg : UpperHessenberg (jacobi (w := w) hR) :=
  mul_upper_right (mul_upper_left (pathOperator_upperHessenberg w)
    (basisMatrix_inverse_upper hR)) (basisMatrix_upper hR)

theorem jacobi_unitSubdiagonal : UnitSubdiagonal (jacobi (w := w) hR) :=
  subdiagonal_mul_upper_right
    (mul_upper_left (pathOperator_upperHessenberg w) (basisMatrix_inverse_upper hR))
    (subdiagonal_mul_upper_left (pathOperator_upperHessenberg w)
      (pathOperator_unitSubdiagonal w) (basisMatrix_inverse_upper hR)
      (basisMatrix_inverse_diagonal hR))
    (basisMatrix_upper hR) (basisMatrix_diagonal hR)

theorem squaredNorm_pos (i : Fin w) : 0 < squaredNorm (w := w) hR i :=
  diagEntries_pos (boundaryGreen_posDef hR w) i

theorem green_leading_det_eq_prod {k : ℕ} (hk : k ≤ w) :
    ((boundaryGreen hR w).submatrix (Fin.castLE hk) (Fin.castLE hk)).det =
      ∏ i : Fin k, squaredNorm (w := w) hR (Fin.castLE hk i) :=
  leading_det_eq_prod_diagEntries (boundaryGreen_posDef hR w) hk

theorem basis_gram :
    (basisMatrix (w := w) hR)ᵀ * boundaryGreen hR w * basisMatrix (w := w) hR =
      Matrix.diagonal (squaredNorm (w := w) hR) := by
  unfold basisMatrix squaredNorm
  rw [Matrix.transpose_transpose]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, LDL.diag] using
    (LDL.diag_eq_lowerInv_conj (boundaryGreen_posDef hR w)).symm

theorem basis_mul_jacobi : basisMatrix (w := w) hR * jacobi (w := w) hR =
    pathOperator w * basisMatrix (w := w) hR := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).mp (basisMatrix_isUnit (w := w) hR)
  simp only [jacobi, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

/-- Self-adjointness in the positive Green form survives the triangular change
of basis and makes the transformed operator a Jacobi matrix. -/
theorem jacobi_weighted_symmetry :
    Matrix.diagonal (squaredNorm (w := w) hR) * jacobi (w := w) hR =
      (jacobi (w := w) hR)ᵀ * Matrix.diagonal (squaredNorm (w := w) hR) := by
  calc
    _ = (basisMatrix (w := w) hR)ᵀ * boundaryGreen hR w * (basisMatrix (w := w) hR * jacobi (w := w) hR) := by
      rw [← basis_gram hR]
      simp only [Matrix.mul_assoc]
    _ = (basisMatrix (w := w) hR)ᵀ * (boundaryGreen hR w * pathOperator w) * basisMatrix (w := w) hR := by
      rw [basis_mul_jacobi]
      simp only [Matrix.mul_assoc]
    _ = (basisMatrix (w := w) hR)ᵀ * (pathOperator w * boundaryGreen hR w) * basisMatrix (w := w) hR := by
      rw [(boundaryGreen_commute hR w).eq]
    _ = (pathOperator w * basisMatrix (w := w) hR)ᵀ * boundaryGreen hR w * basisMatrix (w := w) hR := by
      rw [Matrix.transpose_mul, pathOperator_isSymm w]
      simp only [Matrix.mul_assoc]
    _ = (basisMatrix (w := w) hR * jacobi (w := w) hR)ᵀ * boundaryGreen hR w * basisMatrix (w := w) hR := by
      rw [basis_mul_jacobi]
    _ = (jacobi (w := w) hR)ᵀ * Matrix.diagonal (squaredNorm (w := w) hR) := by
      rw [Matrix.transpose_mul, ← basis_gram hR]
      simp only [Matrix.mul_assoc]

theorem jacobi_weighted_entry (i j : Fin w) :
    squaredNorm (w := w) hR i * jacobi (w := w) hR i j = jacobi (w := w) hR j i * squaredNorm (w := w) hR j := by
  have h := congrArg (fun M : Matrix (Fin w) (Fin w) ℝ => M i j)
    (jacobi_weighted_symmetry (w := w) hR)
  simpa only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply] using h

theorem jacobi_above {i j : Fin w} (hij : i.1 + 1 < j.1) : jacobi (w := w) hR i j = 0 := by
  have h := jacobi_weighted_entry hR i j
  rw [jacobi_upperHessenberg hR j i hij, zero_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (squaredNorm_pos hR i).ne'

theorem jacobi_superdiagonal {i j : Fin w} (hij : j.1 = i.1 + 1) :
    jacobi (w := w) hR i j = -(squaredNorm (w := w) hR j / squaredNorm (w := w) hR i) := by
  have h := jacobi_weighted_entry hR i j
  rw [jacobi_unitSubdiagonal hR j i hij] at h
  rw [← neg_div]
  apply (eq_div_iff (squaredNorm_pos hR i).ne').mpr
  nlinarith

theorem jacobi_charpoly : (jacobi (w := w) hR).charpoly = pathPolynomial w := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).mp (basisMatrix_isUnit (w := w) hR)
  rw [jacobi, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, pathOperator_charpoly]

theorem basis_first_column (hw : 0 < w) (i : Fin w) :
    basisMatrix (w := w) hR i ⟨0, hw⟩ = if i = ⟨0, hw⟩ then 1 else 0 := by
  by_cases hi : i = ⟨0, hw⟩
  · subst i
    simp [basisMatrix_diagonal]
  · rw [if_neg hi]
    exact basisMatrix_upper hR (by
      change 0 < i.1
      have hne : i.1 ≠ 0 := fun h => hi (Fin.ext h)
      omega)

theorem basis_inverse_first_column (hw : 0 < w) (i : Fin w) :
    (basisMatrix (w := w) hR)⁻¹ i ⟨0, hw⟩ = if i = ⟨0, hw⟩ then 1 else 0 := by
  by_cases hi : i = ⟨0, hw⟩
  · subst i
    simp [basisMatrix_inverse_diagonal]
  · rw [if_neg hi]
    exact basisMatrix_inverse_upper hR (by
      change 0 < i.1
      have hne : i.1 ≠ 0 := fun h => hi (Fin.ext h)
      omega)

theorem green_basis_first_row (hw : 0 < w) (j : Fin w) :
    (boundaryGreen hR w * basisMatrix (w := w) hR) ⟨0, hw⟩ j =
      if (⟨0, hw⟩ : Fin w) = j then squaredNorm (w := w) hR ⟨0, hw⟩ else 0 := by
  have h := congrArg (fun M : Matrix (Fin w) (Fin w) ℝ => M ⟨0, hw⟩ j)
    (basis_gram (w := w) hR)
  rw [Matrix.mul_assoc, Matrix.mul_apply] at h
  simpa only [Matrix.transpose_apply, basis_first_column hR hw, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Matrix.diagonal_apply] using h

theorem shifted_similarity (z : ℝ) :
    z • (1 : Matrix (Fin w) (Fin w) ℝ) - pathOperator w =
      basisMatrix (w := w) hR * (z • 1 - jacobi (w := w) hR) * (basisMatrix (w := w) hR)⁻¹ := by
  have hu := (Matrix.isUnit_iff_isUnit_det _).mp (basisMatrix_isUnit (w := w) hR)
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_nonsing_inv _ hu, basis_mul_jacobi,
    Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

/-- The actual scalar Green resolvent is the endpoint Jacobi resolvent times
its genuine positive mass. -/
theorem scalar_resolvent_eq_jacobi (hw : 0 < w) (z : ℝ) :
    (boundaryGreen hR w *
        (z • (1 : Matrix (Fin w) (Fin w) ℝ) - pathOperator w)⁻¹) ⟨0, hw⟩ ⟨0, hw⟩ =
      squaredNorm (w := w) hR ⟨0, hw⟩ *
        ((z • (1 : Matrix (Fin w) (Fin w) ℝ) - jacobi (w := w) hR)⁻¹) ⟨0, hw⟩ ⟨0, hw⟩ := by
  letI := (basisMatrix_isUnit (w := w) hR).nonempty_invertible.some
  rw [shifted_similarity hR z, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.inv_inv_of_invertible]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_apply]
  simp only [basis_inverse_first_column hR hw, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Matrix.mul_apply]
  simp only [green_basis_first_row hR hw, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

noncomputable def normSequence (n : ℕ) : ℝ :=
  if hn : n < w then squaredNorm (w := w) hR ⟨n, hn⟩ else 1

noncomputable def diagonalSequence (n : ℕ) : ℝ :=
  if hn : n < w then jacobi (w := w) hR ⟨n, hn⟩ ⟨n, hn⟩ else 0

theorem normSequence_pos (n : ℕ) : 0 < normSequence (w := w) hR n := by
  unfold normSequence
  split_ifs
  · exact squaredNorm_pos hR _
  · norm_num

end Actual
end SpanningTreeIsoperimetry.JacobiReduction
