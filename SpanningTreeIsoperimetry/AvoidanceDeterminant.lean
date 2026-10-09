import SquareMaximality.Multigraph.TransferCurrentConstruction
import SquareMaximality.Inputs.MatrixTreeTheorem

/-! Actual spanning-tree avoidance events and their complementary
transfer-current determinants. Edge deletion is represented by replacing
the deleted labels by loops, preserving the finite label type. -/
namespace SquareMaximality.Multigraph.LabeledMultigraph

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators Matrix MatrixOrder
noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : LabeledMultigraph V E)
local instance : DecidableEq V := Classical.decEq V
local instance : DecidableEq E := Classical.decEq E

def spanningTreesAvoiding (F : Finset E) : Finset G.SpanningTree := by
  classical
  exact G.spanningTrees.filter (fun T => Disjoint T.val F)

def avoidanceCount (F : Finset E) : ℕ := (G.spanningTreesAvoiding F).card

def avoidanceRatio (F : Finset E) : ℝ :=
  (G.avoidanceCount F : ℝ) / (G.spanningTreeCount : ℝ)

def loopDelete (root : V) (F : Finset E) : LabeledMultigraph V E where
  ends e := if e ∈ F then s(root,root) else G.ends e

theorem loopDelete_simpleGraphOn {root : V} {F T : Finset E} (hd : Disjoint T F) :
    (G.loopDelete root F).simpleGraphOn (T : Set E) = G.simpleGraphOn (T : Set E) := by
  ext u v
  simp only [simpleGraphOn_adj, IsLink, loopDelete]
  constructor <;> rintro ⟨hne,e,he,hlink⟩
  · exact ⟨hne,e,he,by simpa [Finset.disjoint_left.mp hd he] using hlink⟩
  · exact ⟨hne,e,he,by simpa [Finset.disjoint_left.mp hd he] using hlink⟩

theorem loopDelete_isSpanningTree_iff (root : V) (F T : Finset E) :
    (G.loopDelete root F).IsSpanningTree T ↔ G.IsSpanningTree T ∧ Disjoint T F := by
  constructor
  · intro h
    have hd : Disjoint T F := by
      apply Finset.disjoint_left.mpr
      intro e he hF
      have hl := h.loopless he
      exact hl (by simp [IsLoop, loopDelete, hF])
    refine ⟨⟨?_,?_,h.card_edges_add_one⟩,hd⟩
    · intro e he
      simpa [IsLoop, loopDelete, Finset.disjoint_left.mp hd he] using h.loopless he
    · simpa only [loopDelete_simpleGraphOn G hd] using h.selected_connected
  · rintro ⟨h,hd⟩
    refine ⟨?_,?_,h.card_edges_add_one⟩
    · intro e he
      simpa [IsLoop, loopDelete, Finset.disjoint_left.mp hd he] using h.loopless he
    · simpa only [loopDelete_simpleGraphOn G hd] using h.selected_connected

def loopDeleteTreeEquiv (root : V) (F : Finset E) :
    (G.loopDelete root F).SpanningTree ≃ {T : G.SpanningTree // Disjoint T.val F} where
  toFun T := ⟨⟨T.val, ((G.loopDelete_isSpanningTree_iff root F T.val).mp T.property).1⟩,
    ((G.loopDelete_isSpanningTree_iff root F T.val).mp T.property).2⟩
  invFun T := ⟨T.val.val, (G.loopDelete_isSpanningTree_iff root F T.val.val).mpr
    ⟨T.val.property,T.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem loopDelete_treeCount (root : V) (F : Finset E) :
    (G.loopDelete root F).spanningTreeCount = G.avoidanceCount F := by
  classical
  change Nat.card (G.loopDelete root F).SpanningTree = _
  rw [Nat.card_congr (G.loopDeleteTreeEquiv root F), Nat.card_eq_fintype_card]
  simp [avoidanceCount, spanningTreesAvoiding, spanningTrees, Fintype.card_subtype]

theorem loopDelete_reducedSignedIncidence (root : V) (F : Finset E)
    (v : AwayFrom root) (e : E) :
    reducedSignedIncidence (G.loopDelete root F) root v e =
      if e ∈ F then 0 else reducedSignedIncidence G root v e := by
  by_cases he : e ∈ F
  · simp [reducedSignedIncidence_apply, edgeSource, edgeTarget, loopDelete, he]
  · simp [reducedSignedIncidence_apply, edgeSource, edgeTarget, loopDelete, he]

def selectedIncidence (root : V) (F : Finset E) : Matrix (AwayFrom root) F ℝ :=
  (reducedSignedIncidence G root).submatrix id Subtype.val

theorem loopDelete_laplacian (root : V) (F : Finset E) :
    (G.loopDelete root F).reducedLaplacian ℝ root = G.reducedLaplacian ℝ root -
      G.selectedIncidence root F * (G.selectedIncidence root F)ᵀ := by
  rw [← reducedSignedIncidence_mul_transpose, ← reducedSignedIncidence_mul_transpose]
  ext u v
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    loopDelete_reducedSignedIncidence, selectedIncidence, Matrix.submatrix_apply, id_eq]
  have hsum := Finset.sum_add_sum_compl F
    (fun e => reducedSignedIncidence G root u e * reducedSignedIncidence G root v e)
  have hsub : (∑ e : F, reducedSignedIncidence G root u e.val *
      reducedSignedIncidence G root v e.val) =
      ∑ e ∈ F, reducedSignedIncidence G root u e * reducedSignedIncidence G root v e := by
    exact Finset.sum_coe_sort F (fun e => reducedSignedIncidence G root u e *
      reducedSignedIncidence G root v e)
  rw [hsub]
  have ht : ∀ e : E, (if e ∈ F then 0 else reducedSignedIncidence G root u e) *
      (if e ∈ F then 0 else reducedSignedIncidence G root v e) =
      if e ∈ F then 0 else reducedSignedIncidence G root u e *
        reducedSignedIncidence G root v e := by
    intro e
    by_cases he : e ∈ F <;> simp [he]
  simp_rw [ht]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, zero_add, Finset.filter_notMem_eq_sdiff]
  rw [Finset.compl_eq_univ_sdiff] at hsum
  linarith

theorem reducedTransferKernel_idempotent (root : V) (hCount : 0 < G.spanningTreeCount) :
    G.reducedTransferKernel root * G.reducedTransferKernel root = G.reducedTransferKernel root := by
  have hL := reducedLaplacian_posDef G SquareMaximality.labeledMultigraphCofactorInput hCount root
  have hunit : IsUnit (G.reducedLaplacian ℝ root).det := isUnit_iff_ne_zero.mpr hL.det_pos.ne'
  unfold reducedTransferKernel
  calc
    _ = (reducedSignedIncidence G root)ᵀ * (G.reducedLaplacian ℝ root)⁻¹ *
      (reducedSignedIncidence G root * (reducedSignedIncidence G root)ᵀ) *
      (G.reducedLaplacian ℝ root)⁻¹ * reducedSignedIncidence G root := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [reducedSignedIncidence_mul_transpose]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hunit]

theorem one_sub_reducedTransferKernel_posSemidef (root : V)
    (hCount : 0 < G.spanningTreeCount) :
    (1 - G.reducedTransferKernel root).PosSemidef := by
  have hGram := canonicalTransferFactor_gram G
    SquareMaximality.labeledMultigraphCofactorInput hCount root
  have hK : (G.reducedTransferKernel root).IsHermitian := by
    rw [← hGram]
    exact (Matrix.posSemidef_conjTranspose_mul_self _).isHermitian
  have hid := G.reducedTransferKernel_idempotent root hCount
  have heq : (1 - G.reducedTransferKernel root)ᴴ * (1 - G.reducedTransferKernel root) =
      1 - G.reducedTransferKernel root := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hK.eq]
    noncomm_ring [hid]
  rw [← heq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem spanningTreeCount_eq_det_real (root : V) :
    (G.spanningTreeCount : ℝ) = Matrix.det (G.reducedLaplacian ℝ root) := by
  have h := congrArg (fun z : ℤ => (z : ℝ))
    (SquareMaximality.labeledMultigraphCofactorInput V E G root)
  have hc : ((Int.castRingHom ℝ).mapMatrix (G.reducedLaplacian ℤ root)) =
      G.reducedLaplacian ℝ root := by
    ext u v
    simp [reducedLaplacian, laplacian]
  have hd := RingHom.map_det (Int.castRingHom ℝ) (G.reducedLaplacian ℤ root)
  rw [hc] at hd
  have h' : (G.spanningTreeCount : ℝ) = ((G.reducedLaplacian ℤ root).det : ℝ) := by
    simpa using h
  exact h'.trans hd

theorem selectedIncidence_transfer (root : V) (F : Finset E) :
    (G.selectedIncidence root F)ᵀ * (G.reducedLaplacian ℝ root)⁻¹ *
      G.selectedIncidence root F =
      HadamardFischer.principalSubmatrix (G.reducedTransferKernel root) F := by
  ext e f
  simp only [Matrix.mul_apply, Matrix.transpose_apply, selectedIncidence,
    Matrix.submatrix_apply, HadamardFischer.principalSubmatrix, reducedTransferKernel, id_eq]

theorem loopDelete_determinant (root : V) (F : Finset E)
    (hCount : 0 < G.spanningTreeCount) :
    Matrix.det ((G.loopDelete root F).reducedLaplacian ℝ root) =
      Matrix.det (G.reducedLaplacian ℝ root) *
        HadamardFischer.principalDet (1 - G.reducedTransferKernel root) F := by
  have hL := reducedLaplacian_posDef G SquareMaximality.labeledMultigraphCofactorInput hCount root
  have hunit : IsUnit (G.reducedLaplacian ℝ root).det := isUnit_iff_ne_zero.mpr hL.det_pos.ne'
  have h := Matrix.det_add_mul (A := G.reducedLaplacian ℝ root)
    (-G.selectedIncidence root F) (G.selectedIncidence root F)ᵀ hunit
  simp only [Matrix.neg_mul, Matrix.mul_neg, ← sub_eq_add_neg, selectedIncidence_transfer] at h
  rw [loopDelete_laplacian]
  rw [h]
  congr 1
  unfold HadamardFischer.principalDet
  congr 1
  ext e f
  simp only [HadamardFischer.principalSubmatrix, Matrix.submatrix_apply,
    Matrix.sub_apply, Matrix.one_apply, Subtype.ext_iff]

/-- Complementary transfer-current determinant for the actual avoidance
probability, with Kirchhoff and edge deletion proved internally. -/
theorem avoidanceRatio_eq_principalDet (root : V) (F : Finset E)
    (hCount : 0 < G.spanningTreeCount) :
    G.avoidanceRatio F =
      HadamardFischer.principalDet (1 - G.reducedTransferKernel root) F := by
  have hdet := G.loopDelete_determinant root F hCount
  rw [← spanningTreeCount_eq_det_real, ← spanningTreeCount_eq_det_real,
    loopDelete_treeCount] at hdet
  have hp : (G.spanningTreeCount : ℝ) ≠ 0 := by exact_mod_cast hCount.ne'
  unfold avoidanceRatio
  rw [hdet]
  exact mul_div_cancel_left₀ _ hp

/-- Avoidance events for disjoint edge sets are negatively correlated. -/
theorem avoidanceRatio_union_le_mul (root : V) (A B : Finset E)
    (hCount : 0 < G.spanningTreeCount) (hd : Disjoint A B) :
    G.avoidanceRatio (A ∪ B) ≤ G.avoidanceRatio A * G.avoidanceRatio B := by
  rw [G.avoidanceRatio_eq_principalDet root (A ∪ B) hCount,
    G.avoidanceRatio_eq_principalDet root A hCount,
    G.avoidanceRatio_eq_principalDet root B hCount]
  exact HadamardFischer.det_principal_union_le
    (G.one_sub_reducedTransferKernel_posSemidef root hCount) A B hd

end
end SquareMaximality.Multigraph.LabeledMultigraph
