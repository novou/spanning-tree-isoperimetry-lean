module

public import SpanningTreeIsoperimetry.LogDetTangent
public import SpanningTreeIsoperimetry.BoundaryGreenBounds
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

/-! The finite Green-minor log-determinant is controlled by the Dirichlet
boundary trace. The Schur correction is entrywise nonnegative. -/
namespace SpanningTreeIsoperimetry.GreenLogDetComparison
open Ferrers CornerEnergy BoundaryGreenLoss SquareMaximality.Boundary
open scoped BigOperators Matrix Classical
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem inverse_block_schur {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (F : Matrix (m⊕n) (m⊕n) ℝ)
    (hF : IsUnit F.det) (hA : IsUnit F.toBlocks₁₁.det) :
    (F⁻¹.toBlocks₂₂)⁻¹ = F.toBlocks₂₂ - F.toBlocks₂₁ * F.toBlocks₁₁⁻¹ * F.toBlocks₁₂ := by
  have hp : fromBlocks F⁻¹.toBlocks₁₁ F⁻¹.toBlocks₁₂ F⁻¹.toBlocks₂₁ F⁻¹.toBlocks₂₂ *
      fromBlocks F.toBlocks₁₁ F.toBlocks₁₂ F.toBlocks₂₁ F.toBlocks₂₂ = 1 := by
    simpa only [fromBlocks_toBlocks] using Matrix.nonsing_inv_mul F hF
  have h21 := congrArg Matrix.toBlocks₂₁ hp
  have h22 := congrArg Matrix.toBlocks₂₂ hp
  have ho21 : (1 : Matrix (m⊕n) (m⊕n) ℝ).toBlocks₂₁=0 := by
    ext i j
    simp [Matrix.toBlocks₂₁]
  have ho22 : (1 : Matrix (m⊕n) (m⊕n) ℝ).toBlocks₂₂=1 := by
    ext i j
    simp [Matrix.toBlocks₂₂,Matrix.one_apply]
  rw [fromBlocks_multiply,toBlocks_fromBlocks₂₁,ho21] at h21
  rw [fromBlocks_multiply,toBlocks_fromBlocks₂₂,ho22] at h22
  have ht := congrArg (fun X => X * F.toBlocks₁₁⁻¹) h21
  rw [Matrix.add_mul,Matrix.mul_assoc,Matrix.mul_nonsing_inv F.toBlocks₁₁ hA,
    Matrix.mul_one,Matrix.zero_mul] at ht
  have hq : F⁻¹.toBlocks₂₁ = -(F⁻¹.toBlocks₂₂ * F.toBlocks₂₁ * F.toBlocks₁₁⁻¹) :=
    eq_neg_of_add_eq_zero_left ht
  apply Matrix.inv_eq_right_inv
  rw [hq] at h22
  rw [Matrix.mul_sub]
  simpa only [Matrix.mul_assoc,Matrix.neg_mul,sub_eq_add_neg,add_comm] using h22

theorem dirichlet_block_removed {U M : Diagram} (hM : M⊆U) :
    ((fourIminusAdjacency U).submatrix (faceSplitEquiv hM) (faceSplitEquiv hM)).toBlocks₂₂ =
      fourIminusAdjacency M := by
  ext i j
  simp only [Matrix.toBlocks₂₂,Matrix.submatrix_apply,fourIminusAdjacency_apply,
    faceSplitEquiv,Equiv.coe_fn_mk,Subtype.ext_iff,Matrix.of_apply]

theorem greenMinor_posDef {R S : ℕ} {U M : Diagram}
    (hU : U⊆faceRectangle R S) (hM : M⊆U) : (greenMinor hM).PosDef := by
  apply (dirichlet_posDef hU).inv.submatrix
  intro i j hij
  exact Subtype.ext (congrArg (fun p : {p // p∈U} => p.val) hij)

theorem dirichlet_sub_greenMinor_inv_nonneg {R S : ℕ} {U M : Diagram}
    (hU : U⊆faceRectangle R S) (hM : M⊆U) :
    ∀ i j, 0 ≤ (fourIminusAdjacency M - (greenMinor hM)⁻¹) i j := by
  let F := (fourIminusAdjacency U).submatrix (faceSplitEquiv hM) (faceSplitEquiv hM)
  have hFp := (dirichlet_posDef hU).submatrix (faceSplitEquiv hM).injective
  have hA : F.toBlocks₁₁=fourIminusAdjacency (U\M) := dirichlet_block_remaining hM
  have hD : F.toBlocks₂₂=fourIminusAdjacency M := dirichlet_block_removed hM
  have hH : F⁻¹.toBlocks₂₂=greenMinor hM := dirichlet_inverse_block_removed hM
  have hAp : F.toBlocks₁₁.PosDef := by
    rw [hA]
    exact dirichlet_posDef (Finset.Subset.trans Finset.sdiff_subset hU)
  have hi := inverse_block_schur F (isUnit_iff_ne_zero.mpr hFp.det_pos.ne')
    (isUnit_iff_ne_zero.mpr hAp.det_pos.ne')
  rw [hH,hD] at hi
  have hcor : fourIminusAdjacency M-(greenMinor hM)⁻¹=
      F.toBlocks₂₁ * F.toBlocks₁₁⁻¹ * F.toBlocks₁₂ := by rw [hi]; abel
  rw [hcor]
  have hC : ∀ i j, F.toBlocks₂₁ i j≤0 := by
    intro i j
    change fourIminusAdjacency U (faceSplitEquiv hM (Sum.inr i))
      (faceSplitEquiv hM (Sum.inl j))≤0
    rw [fourIminusAdjacency_apply]
    have hn : faceSplitEquiv hM (Sum.inr i)≠faceSplitEquiv hM (Sum.inl j) := by
      intro h
      have := (faceSplitEquiv hM).injective h
      cases this
    simp only [hn,ite_false,zero_sub]
    split_ifs <;> norm_num
  have hB : ∀ i j, F.toBlocks₁₂ i j≤0 := by
    intro i j
    change fourIminusAdjacency U (faceSplitEquiv hM (Sum.inl i))
      (faceSplitEquiv hM (Sum.inr j))≤0
    rw [fourIminusAdjacency_apply]
    have hn : faceSplitEquiv hM (Sum.inl i)≠faceSplitEquiv hM (Sum.inr j) := by
      intro h
      have := (faceSplitEquiv hM).injective h
      cases this
    simp only [hn,ite_false,zero_sub]
    split_ifs <;> norm_num
  have hAi : ∀ i j, 0≤F.toBlocks₁₁⁻¹ i j := by
    intro i j
    rw [hA]
    have hb := green_nonneg (U := U\M) (Finset.Subset.trans Finset.sdiff_subset hU) i.val j.val
    simpa only [green_mem i.property j.property] using hb
  have hCA : ∀ i j, (F.toBlocks₂₁*F.toBlocks₁₁⁻¹) i j≤0 := by
    intro i j
    rw [Matrix.mul_apply]
    exact Finset.sum_nonpos (fun l _ => mul_nonpos_of_nonpos_of_nonneg (hC i l) (hAi l j))
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg (fun l _ => mul_nonneg_of_nonpos_of_nonpos (hCA i l) (hB l j))

theorem trace_mul_le_of_entrywise {n : Type*} [Fintype n] [DecidableEq n]
    (A B C : Matrix n n ℝ) (hAB : ∀ i j, A i j≤B i j) (hC : ∀ i j, 0≤C i j) :
    Matrix.trace (A*C)≤Matrix.trace (B*C) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
    (fun j _ => mul_le_mul_of_nonneg_right (hAB i j) (hC j i)))

theorem finite_green_logdet_bound {R S T W : ℕ} {U V M : Diagram}
    (hU : U⊆faceRectangle R S) (hV : V⊆faceRectangle T W) (hUV : U⊆V) (hM : M⊆U) :
    Real.log (greenMinor (Finset.Subset.trans hM hUV)).det - Real.log (greenMinor hM).det ≤
      Matrix.trace (fourIminusAdjacency M *
        (greenMinor (Finset.Subset.trans hM hUV)-greenMinor hM)) := by
  have ht := LogDetTangent.log_det_tangent (greenMinor_posDef hU hM)
    (greenMinor_posDef hV (Finset.Subset.trans hM hUV))
  apply ht.trans
  apply trace_mul_le_of_entrywise
  · intro i j
    have := dirichlet_sub_greenMinor_inv_nonneg hU hM i j
    simpa only [Matrix.sub_apply,sub_nonneg] using this
  · intro i j
    have hm := BoundaryGreenBounds.green_mono hU hV hUV i.val j.val
    rw [green_mem (hUV (hM i.property)) (hUV (hM j.property)),
      green_mem (hM i.property) (hM j.property)] at hm
    exact sub_nonneg.mpr hm

end
end SpanningTreeIsoperimetry.GreenLogDetComparison
