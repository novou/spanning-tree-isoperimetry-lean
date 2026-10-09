import SpanningTreeIsoperimetry.ScalarResolvent
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Rectangle determinant via checked layer Schur complements. -/
namespace SpanningTreeIsoperimetry.LayerDeterminant

open scoped BigOperators Matrix Classical Kronecker
open ScalarResolvent
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Separate the first layer from all remaining layers. -/
def layerSplitEquiv (R w : ℕ) :
    (Fin w ⊕ (Fin R × Fin w)) ≃ (Fin (R + 1) × Fin w) :=
  optionProdEquiv.symm.trans
    (Equiv.prodCongr (finSuccEquiv R).symm (Equiv.refl _))

@[simp] theorem layerSplitEquiv_inl (R w : ℕ) (x : Fin w) :
    layerSplitEquiv R w (Sum.inl x) = (0, x) := by
  simp [layerSplitEquiv]

@[simp] theorem layerSplitEquiv_inr (R w : ℕ) (p : Fin R × Fin w) :
    layerSplitEquiv R w (Sum.inr p) = (p.1.succ, p.2) := by
  rcases p with ⟨i, x⟩
  simp [layerSplitEquiv]

private theorem rectangleDirichlet_apply (R w : ℕ) (i j : Fin R) (x y : Fin w) :
    rectangleDirichlet R w (i, x) (j, y) =
      (if i = j then pathOperator w x y else 0) -
        (if i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 then
          (if x = y then 1 else 0) else 0) := by
  by_cases hxy : x = y <;>
    simp [rectangleDirichlet, Matrix.kronecker_apply, Matrix.one_apply,
      SimpleGraph.adjMatrix, SimpleGraph.pathGraph_adj, ite_mul, hxy]

/-- The actual rectangle matrix has the claimed two-by-two layer blocks. -/
theorem rectangleDirichlet_blocks {R : ℕ} (hR : 0 < R) (w : ℕ) :
    (rectangleDirichlet (R + 1) w).submatrix (layerSplitEquiv R w) (layerSplitEquiv R w) =
      Matrix.fromBlocks (pathOperator w) (-(firstLayer hR w)ᵀ)
        (-firstLayer hR w) (rectangleDirichlet R w) := by
  ext p q
  rcases p with x | ⟨i, x⟩ <;> rcases q with y | ⟨j, y⟩
  · simp [Matrix.submatrix_apply, rectangleDirichlet_apply]
  · simp only [Matrix.submatrix_apply, layerSplitEquiv_inl, layerSplitEquiv_inr,
      Matrix.fromBlocks_apply₁₂, rectangleDirichlet_apply, Matrix.neg_apply,
      Matrix.transpose_apply, firstLayer, Matrix.one_apply]
    by_cases hj : j.1 = 0 <;> by_cases hxy : x = y <;>
      simp [Fin.ext_iff, hj, hxy, eq_comm]
  · simp only [Matrix.submatrix_apply, layerSplitEquiv_inl, layerSplitEquiv_inr,
      Matrix.fromBlocks_apply₂₁, rectangleDirichlet_apply, Matrix.neg_apply,
      firstLayer, Matrix.one_apply]
    by_cases hi : i.1 = 0 <;> by_cases hxy : x = y <;>
      simp [Fin.ext_iff, hi, hxy]
  · simp [Matrix.submatrix_apply, rectangleDirichlet_apply, Fin.ext_iff]

/-- Extracting the first inverse block is multiplication by the layer embedding. -/
theorem firstLayer_inverse_firstLayer {R : ℕ} (hR : 0 < R) (w : ℕ) :
    (firstLayer hR w)ᵀ * (rectangleDirichlet R w)⁻¹ * firstLayer hR w =
      boundaryGreen hR w := by
  ext x y
  simp [Matrix.mul_apply, Matrix.transpose_apply, firstLayer, Matrix.one_apply,
    Fintype.sum_prod_type, mul_ite, ite_mul, boundaryGreen, Matrix.submatrix_apply]

/-- The actual layer Schur complement yields the determinant recurrence. -/
theorem rectangleDirichlet_det_succ {R : ℕ} (hR : 0 < R) (w : ℕ) :
    (rectangleDirichlet (R + 1) w).det =
      (rectangleDirichlet R w).det * (pathOperator w - boundaryGreen hR w).det := by
  have hu : IsUnit (rectangleDirichlet R w) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (rectangleDirichlet_posDef R w).det_pos.ne')
  letI := hu.nonempty_invertible.some
  rw [← Matrix.det_submatrix_equiv_self (layerSplitEquiv R w), rectangleDirichlet_blocks hR,
    Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, firstLayer_inverse_firstLayer]

/-- The Schur complement times the previous continuant is the next continuant. -/
theorem schur_mul_continuant {R : ℕ} (hR : 0 < R) (w : ℕ) :
    (pathOperator w - boundaryGreen hR w) * operatorContinuant w R =
      operatorContinuant w (R + 1) := by
  have h := green_first_column_continuant hR w ⟨0, hR⟩
  change boundaryGreen hR w * operatorContinuant w R = operatorContinuant w (R - 1 - 0) at h
  simp only [Nat.sub_zero] at h
  rw [Matrix.sub_mul, h]
  have hr := operatorContinuant_recurrence w (R - 1)
  rw [show R - 1 + 2 = R + 1 by omega, show R - 1 + 1 = R by omega] at hr
  exact hr.symm

/-- A one-layer rectangle is the actual path operator after the trivial reindexing. -/
theorem rectangleDirichlet_det_one (w : ℕ) :
    (rectangleDirichlet 1 w).det = (pathOperator w).det := by
  let e : Fin w ≃ (Fin 1 × Fin w) := (Equiv.uniqueProd (Fin w) (Fin 1)).symm
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext x y
  simp [e, rectangleDirichlet_apply]

/-- The actual rectangle Dirichlet determinant is the layer continuant determinant. -/
theorem rectangleDirichlet_det_eq_continuant (R w : ℕ) :
    (rectangleDirichlet R w).det = (operatorContinuant w R).det := by
  induction R with
  | zero => simp [operatorContinuant, Matrix.det_isEmpty]
  | succ R ih =>
    by_cases hR : R = 0
    · subst R
      simpa using rectangleDirichlet_det_one w
    · have hRpos : 0 < R := Nat.pos_of_ne_zero hR
      rw [rectangleDirichlet_det_succ hRpos, ih, mul_comm, ← Matrix.det_mul,
        schur_mul_continuant hRpos]

end SpanningTreeIsoperimetry.LayerDeterminant
