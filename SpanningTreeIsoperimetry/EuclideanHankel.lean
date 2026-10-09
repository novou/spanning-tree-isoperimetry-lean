import SpanningTreeIsoperimetry.ScalarResolvent
import Mathlib.Analysis.Matrix.LDL

/-! Orthogonalization of the actual positive moment matrices. The eventual
signed Euclidean-chain identification is separate from these proved matrix
factorizations. -/
namespace SpanningTreeIsoperimetry.EuclideanHankel

open scoped BigOperators Matrix Classical
open ScalarResolvent Matrix InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every permitted moment matrix is positive definite, not merely of
positive determinant. -/
theorem boundaryGreen_hankel_posDef {R w k : ℕ}
    (hR : 0 < R) (hw : 0 < w) (hk : k ≤ w) :
    (hankel hw (boundaryGreen hR w) k).PosDef := by
  have hgram := krylov_gram_eq_hankel (k := k) hw (boundaryGreen hR w)
    (boundaryGreen_commute hR w)
  rw [krylov_factor hw hk, Matrix.transpose_mul] at hgram
  have he : (krylovLeading hw hk)ᵀ *
      ((boundaryGreen hR w).submatrix (Fin.castLE hk) (Fin.castLE hk)) * krylovLeading hw hk =
      hankel hw (boundaryGreen hR w) k := by
    rw [← leadingEmbedding_gram hk]
    simpa only [Matrix.mul_assoc] using hgram
  have hunit : IsUnit (krylovLeading hw hk) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hs := krylovLeading_det_sq hw hk
    rw [hz] at hs
    norm_num at hs
  have hp := ((boundaryGreen_posDef hR w).submatrix (Fin.castLE_injective hk)).conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hunit)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, he] using hp

/-- A lower triangular matrix preserves the leading coordinate subspace on
rows, so restriction commutes with the relevant multiplication. -/
theorem leading_lower_rows {w k : ℕ} (hk : k ≤ w)
    (L : Matrix (Fin w) (Fin w) ℝ) (hL : L.IsLowerTriangular) :
    (leadingEmbedding hk)ᵀ * L =
      L.submatrix (Fin.castLE hk) (Fin.castLE hk) * (leadingEmbedding hk)ᵀ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, leadingEmbedding,
    Matrix.submatrix_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  by_cases hj : j.1 < k
  · let t : Fin k := ⟨j.1, hj⟩
    have hjt : j = Fin.castLE hk t := by apply Fin.ext; rfl
    rw [Finset.sum_eq_single t]
    · rw [← hjt]
      simp
    · intro l _ hlt
      have hne : j ≠ Fin.castLE hk l := by
        intro he
        apply hlt
        apply Fin.ext
        exact (congrArg Fin.val he).symm
      simp [hne]
    · simp
  · have hl : L (Fin.castLE hk i) j = 0 := hL (by change i.1 < j.1; omega)
    rw [hl]
    symm
    apply Finset.sum_eq_zero
    intro t _
    have hne : j ≠ Fin.castLE hk t := by
      intro he
      have hv := congrArg Fin.val he
      change j.1 = t.1 at hv
      omega
    simp [hne]

/-- A unit lower triangular congruence restricts to every leading block. -/
theorem leading_lower_congruence {w k : ℕ} (hk : k ≤ w)
    (L H : Matrix (Fin w) (Fin w) ℝ) (hL : L.IsLowerTriangular) :
    (L * H * Lᵀ).submatrix (Fin.castLE hk) (Fin.castLE hk) =
      L.submatrix (Fin.castLE hk) (Fin.castLE hk) *
        H.submatrix (Fin.castLE hk) (Fin.castLE hk) *
          (L.submatrix (Fin.castLE hk) (Fin.castLE hk))ᵀ := by
  rw [← leadingEmbedding_gram hk]
  calc
    _ = ((leadingEmbedding hk)ᵀ * L) * H * ((leadingEmbedding hk)ᵀ * L)ᵀ := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = _ := by
      rw [leading_lower_rows hk L hL, Matrix.transpose_mul, Matrix.transpose_transpose]
      rw [← leadingEmbedding_gram hk H]
      simp only [Matrix.mul_assoc]

section LDL
variable {w : ℕ} {H : Matrix (Fin w) (Fin w) ℝ} (hH : H.PosDef)

/-- The Gram--Schmidt coefficient matrix is monic (unit lower triangular). -/
theorem lowerInv_diagonal (i : Fin w) : LDL.lowerInv hH i i = 1 := by
  letI := Hᵀ.toNormedAddCommGroup hH.transpose
  letI := Hᵀ.toInnerProductSpace hH.transpose.posSemidef
  let b := Pi.basisFun ℝ (Fin w)
  have hz (j : Fin w) (hj : j < i) : gramSchmidt ℝ b j i = 0 := by
    simpa [b] using gramSchmidt_triangular (𝕜 := ℝ) hj b
  have h := congrFun (gramSchmidt_def'' ℝ b i) i
  have hb : b i i = 1 := by simp [b]
  simp only [Pi.add_apply, hb, RCLike.ofReal_real_eq_id, id_eq] at h
  conv_rhs at h =>
    rhs
    rw [Finset.sum_apply]
    equals 0 =>
      apply Finset.sum_eq_zero
      intro j hj
      simp [hz j (Finset.mem_Iio.mp hj)]
  simp only [add_zero] at h
  exact h.symm

theorem lowerInv_det : (LDL.lowerInv hH).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (LDL.isLowerTriangular_lowerInv hH)]
  simp only [lowerInv_diagonal, Finset.prod_const_one]

/-- The orthogonal polynomial squared norms are all strictly positive. -/
theorem diagEntries_pos (i : Fin w) : 0 < LDL.diagEntries hH i := by
  have hp := hH.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_of_isUnit (isUnit_of_invertible (LDL.lowerInv hH)))
  rw [← LDL.diag_eq_lowerInv_conj hH] at hp
  simpa only [LDL.diag, Matrix.diagonal_apply_eq] using hp.diag_pos (i := i)

/-- The Hankel determinant is the product of the genuine squared norms. -/
theorem det_eq_prod_diagEntries : H.det = ∏ i : Fin w, LDL.diagEntries hH i := by
  have hd := congrArg Matrix.det (LDL.diag_eq_lowerInv_conj hH)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
    lowerInv_det, star_one, one_mul, mul_one] at hd
  simpa only [LDL.diag, Matrix.det_diagonal] using hd.symm

/-- Every leading Hankel determinant factors into the first squared norms
of one coherent Gram--Schmidt system. -/
theorem leading_det_eq_prod_diagEntries {k : ℕ} (hk : k ≤ w) :
    (H.submatrix (Fin.castLE hk) (Fin.castLE hk)).det =
      ∏ i : Fin k, LDL.diagEntries hH (Fin.castLE hk i) := by
  let L := LDL.lowerInv hH
  have hL : L.IsLowerTriangular := LDL.isLowerTriangular_lowerInv hH
  have hLk : (L.submatrix (Fin.castLE hk) (Fin.castLE hk)).IsLowerTriangular := by
    intro i j hij
    exact hL hij
  have hLdet : (L.submatrix (Fin.castLE hk) (Fin.castLE hk)).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ hLk]
    simp only [Matrix.submatrix_apply, L, lowerInv_diagonal, Finset.prod_const_one]
  have he := congrArg (fun M : Matrix (Fin w) (Fin w) ℝ =>
    M.submatrix (Fin.castLE hk) (Fin.castLE hk)) (LDL.diag_eq_lowerInv_conj hH)
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at he
  rw [leading_lower_congruence hk _ _ hL] at he
  have hd := congrArg Matrix.det he
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hLdet, one_mul, mul_one] at hd
  have hdiag : (LDL.diag hH).submatrix (Fin.castLE hk) (Fin.castLE hk) =
      Matrix.diagonal (fun i : Fin k => LDL.diagEntries hH (Fin.castLE hk i)) := by
    ext i j
    simp [LDL.diag, Matrix.submatrix_apply, Matrix.diagonal_apply, Fin.castLE_inj]
  rw [hdiag, Matrix.det_diagonal] at hd
  exact hd.symm

end LDL
end SpanningTreeIsoperimetry.EuclideanHankel
