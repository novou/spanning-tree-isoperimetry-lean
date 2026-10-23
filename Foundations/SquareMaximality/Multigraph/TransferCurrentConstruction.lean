module

public import SquareMaximality.Multigraph.TransferCurrent
public import SquareMaximality.Multigraph.ContractionTrees
public import SquareMaximality.Inputs.MatrixTree
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Constructing the transfer-current determinant input

This module gives the canonical reduced signed-incidence construction of the
transfer-current kernel.  The only finite graph identity separated below is
the complementary-minor identity relating a forest principal minor to the
cofactor of the graph obtained by contracting that forest.
-/

namespace SquareMaximality.Multigraph
namespace LabeledMultigraph

open scoped BigOperators Matrix MatrixOrder

noncomputable section

universe uV uE

variable {V : Type uV} {E : Type uE} (G : LabeledMultigraph V E)
variable [Fintype V] [Fintype E]

noncomputable local instance : DecidableEq V := Classical.decEq V

/-- An arbitrary orientation of the two ends of an edge label. -/
def edgeSource (e : E) : V := (G.ends e).out.1

/-- The other endpoint in the arbitrary orientation. -/
def edgeTarget (e : E) : V := (G.ends e).out.2

omit [Fintype V] [Fintype E] in theorem ends_edgeSource_edgeTarget (e : E) :
    G.ends e = s(G.edgeSource e, G.edgeTarget e) := by
  symm
  exact (G.ends e).out_eq

/-- The signed vertex-edge incidence matrix for the arbitrary orientation. -/
noncomputable def signedIncidence : Matrix V E ℝ := by
  classical
  exact fun v e =>
    (if v = G.edgeSource e then 1 else 0) -
      (if v = G.edgeTarget e then 1 else 0)

/-- Signed incidence with the root row removed.  Loop columns vanish. -/
noncomputable def reducedSignedIncidence (root : V) : Matrix (AwayFrom root) E ℝ := by
  exact (signedIncidence G).submatrix Subtype.val id

omit [Fintype V] [Fintype E] in @[simp] theorem reducedSignedIncidence_apply (root : V)
    (v : AwayFrom root) (e : E) :
    reducedSignedIncidence G root v e =
      (if v.1 = G.edgeSource e then 1 else 0) -
        (if v.1 = G.edgeTarget e then 1 else 0) :=
  by classical rfl

omit [Fintype V] [Fintype E] in
private noncomputable def linkSignedIndicator (e : E) (u v : V) : ℝ := by
  classical
  exact if G.IsLink e u v then -1 else 0

omit [Fintype V] [Fintype E] in
private theorem signedIncidence_mul_apply_of_ne {u v : V} (huv : u ≠ v) (e : E) :
    signedIncidence G u e * signedIncidence G v e =
      linkSignedIndicator G e u v := by
  classical
  have hlink : G.IsLink e u v ↔
      (G.edgeSource e = u ∧ G.edgeTarget e = v) ∨
        (G.edgeSource e = v ∧ G.edgeTarget e = u) := by
    rw [IsLink, G.ends_edgeSource_edgeTarget, Sym2.eq_iff]
  simp only [signedIncidence, linkSignedIndicator, hlink]
  by_cases hus : u = G.edgeSource e <;>
    by_cases hut : u = G.edgeTarget e <;>
    by_cases hvs : v = G.edgeSource e <;>
    by_cases hvt : v = G.edgeTarget e <;>
    simp_all [eq_comm]

omit [Fintype E] in private theorem signedIncidence_column_sum (e : E) :
    ∑ v, signedIncidence G v e = 0 := by
  simp only [signedIncidence, Finset.sum_sub_distrib]
  simp

omit [Fintype V] in
private theorem incidenceGram_offDiagonal {u v : V} (huv : u ≠ v) :
    (signedIncidence G * (signedIncidence G)ᵀ) u v =
      -(G.adjacencyMultiplicity u v : ℝ) := by
  classical
  rw [Matrix.mul_apply]
  simp_rw [Matrix.transpose_apply, signedIncidence_mul_apply_of_ne G huv]
  simp only [linkSignedIndicator]
  rw [G.adjacencyMultiplicity_of_ne huv, edgeMultiplicity, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  simp only [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, smul_neg,
    add_zero]
  rw [nsmul_eq_mul]
  norm_num

private theorem incidenceGram_row_sum (u : V) :
    ∑ v, (signedIncidence G * (signedIncidence G)ᵀ) u v = 0 := by
  classical
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _he
  rw [← Finset.mul_sum]
  simp [signedIncidence_column_sum]

/-- The signed incidence Gram matrix is the labelled-multigraph Laplacian. -/
theorem signedIncidence_mul_transpose :
    signedIncidence G * (signedIncidence G)ᵀ = G.laplacian ℝ := by
  classical
  ext u v
  by_cases huv : u = v
  · subst v
    have hrow := incidenceGram_row_sum G u
    rw [← Finset.univ.add_sum_erase _ (Finset.mem_univ u)] at hrow
    have hoff :
        ∑ x ∈ Finset.univ.erase u,
            (signedIncidence G * (signedIncidence G)ᵀ) u x =
          -(G.degree u : ℝ) := by
      calc
        (∑ x ∈ Finset.univ.erase u,
            (signedIncidence G * (signedIncidence G)ᵀ) u x) =
            ∑ x ∈ Finset.univ.erase u,
              -(G.adjacencyMultiplicity u x : ℝ) := by
                apply Finset.sum_congr rfl
                intro x hx
                rw [incidenceGram_offDiagonal G]
                exact Ne.symm (Finset.mem_erase.mp hx).1
        _ = -∑ x ∈ Finset.univ.erase u,
              (G.adjacencyMultiplicity u x : ℝ) := by
                rw [Finset.sum_neg_distrib]
        _ = -(G.degree u : ℝ) := by
          simp only [degree]
          push_cast
          rw [← Finset.univ.add_sum_erase _ (Finset.mem_univ u)]
          simp
    rw [hoff] at hrow
    rw [G.laplacian_diagonal]
    linarith
  · rw [incidenceGram_offDiagonal G huv, G.laplacian_offDiagonal ℝ huv]

/-- Root-row deletion commutes with the incidence Gram factorization. -/
theorem reducedSignedIncidence_mul_transpose (root : V) :
    reducedSignedIncidence G root * (reducedSignedIncidence G root)ᵀ =
      G.reducedLaplacian ℝ root := by
  classical
  ext u v
  simp only [Matrix.mul_apply, reducedSignedIncidence, Matrix.submatrix_apply,
    Matrix.transpose_apply, reducedLaplacian_apply]
  have hfull := congrArg (fun M : Matrix V V ℝ => M u.1 v.1)
    (signedIncidence_mul_transpose G)
  rw [Matrix.mul_apply] at hfull
  exact hfull

/-- Extend a matrix indexed away from a root by inserting a zero root row. -/
noncomputable def extendRootZero (root : V) (Q : Matrix (AwayFrom root) E ℝ) :
    Matrix V E ℝ := by
  classical
  exact fun v e => if h : v ≠ root then Q ⟨v, h⟩ e else 0

omit [Fintype E] in
private theorem extendRootZero_conjTranspose_mul_self (root : V)
    (Q : Matrix (AwayFrom root) E ℝ) :
    (extendRootZero root Q)ᴴ * extendRootZero root Q = Qᴴ * Q := by
  classical
  ext e f
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    star_id_of_comm, extendRootZero]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ root]
  simp only [ne_eq, not_true_eq_false, ↓reduceDIte, zero_mul, zero_add]
  apply Fintype.sum_congr
  intro x
  simp [x.property]

/-- The canonical transfer-current kernel based at `root`. -/
noncomputable def reducedTransferKernel (root : V) : Matrix E E ℝ :=
  (reducedSignedIncidence G root)ᵀ *
    (G.reducedLaplacian ℝ root)⁻¹ * reducedSignedIncidence G root

/-- A square-root Gram factor for the canonical kernel, embedded by a zero
row at the root. -/
noncomputable def canonicalTransferFactor (root : V) : Matrix V E ℝ :=
  extendRootZero root
    (CFC.sqrt ((G.reducedLaplacian ℝ root)⁻¹) *
      reducedSignedIncidence G root)

private theorem map_laplacian_int_real :
    (Int.castRingHom ℝ).mapMatrix (G.laplacian ℤ) = G.laplacian ℝ := by
  classical
  ext u v
  simp [laplacian]

private theorem det_reducedLaplacian_cast (root : V) :
    (((G.reducedLaplacian ℤ root).det : ℤ) : ℝ) =
      (G.reducedLaplacian ℝ root).det := by
  calc
    (((G.reducedLaplacian ℤ root).det : ℤ) : ℝ) =
        ((Int.castRingHom ℝ).mapMatrix (G.reducedLaplacian ℤ root)).det :=
      RingHom.map_det (Int.castRingHom ℝ) _
    _ = _ := by
      congr 1
      ext u v
      have hmap := congrArg
        (fun M : Matrix V V ℝ => M u.1 v.1)
        (map_laplacian_int_real G)
      change ((Int.castRingHom ℝ).mapMatrix (G.laplacian ℤ)) u.1 v.1 =
        G.laplacian ℝ u.1 v.1
      exact hmap

/-- Positive definiteness of the reduced Laplacian follows from the incidence
factorization and a nonzero Matrix--Tree cofactor. -/
theorem reducedLaplacian_posDef
    (hMatrixTree : LabeledMultigraphCofactorInput.{uV, uE})
    (hCount : 0 < G.spanningTreeCount) (root : V) :
    (G.reducedLaplacian ℝ root).PosDef := by
  classical
  have hPSD0 := Matrix.posSemidef_self_mul_conjTranspose
    (reducedSignedIncidence G root)
  have hPSD : (G.reducedLaplacian ℝ root).PosSemidef := by
    rw [← reducedSignedIncidence_mul_transpose G root]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hPSD0
  apply hPSD.posDef_iff_det_ne_zero.mpr
  rw [← det_reducedLaplacian_cast G root,
    ← hMatrixTree V E G root]
  exact_mod_cast (Nat.ne_of_gt hCount)

/-- The chosen square-root factor has precisely the standard
`Bᵀ L⁻¹ B` transfer-current Gram matrix. -/
theorem canonicalTransferFactor_gram
    (hMatrixTree : LabeledMultigraphCofactorInput.{uV, uE})
    (hCount : 0 < G.spanningTreeCount) (root : V) :
    (canonicalTransferFactor G root)ᴴ * canonicalTransferFactor G root =
      reducedTransferKernel G root := by
  classical
  let L := G.reducedLaplacian ℝ root
  let B := reducedSignedIncidence G root
  let P := CFC.sqrt L⁻¹
  have hL : L.PosDef := reducedLaplacian_posDef G hMatrixTree hCount root
  have hPinv : 0 ≤ L⁻¹ := hL.inv.posSemidef.nonneg
  have hPsq : P * P = L⁻¹ := by
    simpa only [P, pow_two] using CFC.sq_sqrt L⁻¹ hPinv
  have hPstar : Pᴴ = P := by
    exact (CFC.sqrt_nonneg L⁻¹).star_eq
  rw [canonicalTransferFactor, extendRootZero_conjTranspose_mul_self]
  rw [Matrix.conjTranspose_mul, hPstar,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [reducedTransferKernel]
  change (Bᵀ * P) * (P * B) = Bᵀ * L⁻¹ * B
  calc
    (Bᵀ * P) * (P * B) = Bᵀ * ((P * P) * B) := by
      simp only [Matrix.mul_assoc]
    _ = Bᵀ * L⁻¹ * B := by rw [hPsq, Matrix.mul_assoc]

/-- The exact remaining all-minors statement.  For a forest, the principal
minor of `Bᵀ L⁻¹ B` is the ratio of the contracted and ambient cofactors.

This is strictly prior to the transfer-current probability statement: its
right-hand side contains only explicit reduced Laplacian determinants. -/
def ForestContractionComplementaryMinorInput (root : V) : Prop :=
  ∀ (F : Finset E) (_hF : G.IsEdgeForest F),
    HadamardFischer.principalDet (reducedTransferKernel G root) F =
      Matrix.det ((G.contract F).reducedLaplacian ℝ
          (G.contractionMap F root)) /
        Matrix.det (G.reducedLaplacian ℝ root)

private theorem cofactorRatio_eq_containmentRatio
    (hMatrixTree : LabeledMultigraphCofactorInput.{uV, uE})
    (root : V) {F : Finset E} (hF : G.IsEdgeForest F) :
    Matrix.det ((G.contract F).reducedLaplacian ℝ
          (G.contractionMap F root)) /
        Matrix.det (G.reducedLaplacian ℝ root) = G.containmentRatio F := by
  classical
  letI : Fintype (G.simpleGraphOn (F : Set E)).ConnectedComponent :=
    G.contractionComponentFintype F
  rw [G.containmentRatio_eq_contract_ratio hF]
  rw [← det_reducedLaplacian_cast (G.contract F) (G.contractionMap F root),
    ← det_reducedLaplacian_cast G root]
  rw [← hMatrixTree _ _ (G.contract F) (G.contractionMap F root),
    ← hMatrixTree V E G root]
  norm_num

/-- Construct the complete transfer-current determinant interface from
Matrix--Tree and the isolated complementary-minor/contraction identity. -/
noncomputable def transferCurrentDeterminantInput
    (hMatrixTree : LabeledMultigraphCofactorInput.{uV, uE})
    (hCount : 0 < G.spanningTreeCount) (root : V)
    (hComplementary : ForestContractionComplementaryMinorInput G root) :
    G.TransferCurrentDeterminantInput where
  transferFactor := canonicalTransferFactor G root
  forestPrincipalMinor F hF := by
    calc
      G.containmentRatio F =
          Matrix.det ((G.contract F).reducedLaplacian ℝ
              (G.contractionMap F root)) /
            Matrix.det (G.reducedLaplacian ℝ root) :=
        (cofactorRatio_eq_containmentRatio G hMatrixTree root hF).symm
      _ = HadamardFischer.principalDet
          (reducedTransferKernel G root) F :=
        (hComplementary F hF).symm
      _ = HadamardFischer.principalDet
          ((canonicalTransferFactor G root)ᴴ *
            canonicalTransferFactor G root) F := by
        rw [canonicalTransferFactor_gram G hMatrixTree hCount root]

section BlockJacobi

variable {I J : Type*} [Fintype I] [Fintype J]
variable [DecidableEq I] [DecidableEq J]

/-- Jacobi's complementary-minor identity in the two-block form needed for
the forest-coordinate argument. -/
theorem det_topLeft_eq_det_mul_det_inv_bottomRight
    (A : Matrix I I ℝ) (B : Matrix I J ℝ)
    (C : Matrix J I ℝ) (D : Matrix J J ℝ)
    (hM : (Matrix.fromBlocks A B C D).PosDef) :
    A.det = (Matrix.fromBlocks A B C D).det *
      ((Matrix.fromBlocks A B C D)⁻¹.toBlocks₂₂).det := by
  let M := Matrix.fromBlocks A B C D
  have hA : A.PosDef := by
    have h := hM.submatrix (e := Sum.inl) Sum.inl_injective
    exact h
  letI iA : Invertible A := hA.isUnit.invertible
  letI iM : Invertible M := hM.isUnit.invertible
  let S := D - C * ⅟A * B
  letI iS : Invertible S := by
    exact Matrix.invertibleOfFromBlocks₁₁Invertible A B C D
  letI : Invertible S.det := Matrix.detInvertibleOfInvertible S
  have hbottom : M⁻¹.toBlocks₂₂ = ⅟S := by
    rw [← Matrix.invOf_eq_nonsing_inv,
      Matrix.invOf_fromBlocks₁₁_eq]
    rfl
  change A.det = M.det * (M⁻¹.toBlocks₂₂).det
  rw [hbottom, Matrix.det_invOf]
  rw [invOf_eq_inv]
  change A.det = M.det * S.det⁻¹
  have hdet := Matrix.det_fromBlocks₁₁ A B C D
  change M.det = A.det * S.det at hdet
  rw [hdet]
  rw [← div_eq_mul_inv,
    mul_div_cancel_right₀ _ (Invertible.ne_zero S.det)]

/-- Coordinate-free wrapper of the two-block Jacobi identity. -/
theorem det_toBlocks₁₁_eq_det_mul_det_inv_toBlocks₂₂
    (M : Matrix (I ⊕ J) (I ⊕ J) ℝ) (hM : M.PosDef) :
    M.toBlocks₁₁.det = M.det * (M⁻¹.toBlocks₂₂).det := by
  have hblocks : Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂
      M.toBlocks₂₁ M.toBlocks₂₂ = M := Matrix.fromBlocks_toBlocks M
  have hPos : (Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂
      M.toBlocks₂₁ M.toBlocks₂₂).PosDef := by
    rw [hblocks]
    exact hM
  have h := det_topLeft_eq_det_mul_det_inv_bottomRight
    M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ hPos
  rw [hblocks] at h
  exact h

end BlockJacobi

/-- A forest has exactly enough selected-edge coordinates and non-root
component coordinates to parametrize the vertices away from one root. -/
noncomputable def forestCoordinateEquiv {F : Finset E}
    (hF : G.IsEdgeForest F) (root : V) :
    AwayFrom root ≃
      SelectedEdge F ⊕ AwayFrom (G.contractionMap F root) := by
  classical
  letI : Fintype (G.simpleGraphOn (F : Set E)).ConnectedComponent :=
    G.contractionComponentFintype F
  apply Fintype.equivOfCardEq
  have hforest := IsEdgeForest.card_add_components G hF
  have hVpos : 0 < Fintype.card V :=
    Fintype.card_pos_iff.mpr ⟨root⟩
  have hComponentsPos :
      0 < Fintype.card (G.simpleGraphOn (F : Set E)).ConnectedComponent :=
    Fintype.card_pos_iff.mpr ⟨G.contractionMap F root⟩
  have hAway : Fintype.card (AwayFrom root) = Fintype.card V - 1 := by
    change Fintype.card {v : V // ¬v = root} = _
    rw [Fintype.card_subtype_compl]
    simp
  have hContractAway :
      Fintype.card (AwayFrom (G.contractionMap F root)) =
        Fintype.card (G.simpleGraphOn (F : Set E)).ConnectedComponent - 1 := by
    change Fintype.card
        {c : (G.simpleGraphOn (F : Set E)).ConnectedComponent //
          ¬c = G.contractionMap F root} = _
    rw [Fintype.card_subtype_compl]
    simp
  rw [hAway, Fintype.card_sum, Fintype.card_coe, hContractAway]
  omega

/-- Columns consisting of the selected forest incidences followed by one
standard representative vector for each non-root contraction component. -/
noncomputable def forestCoordinateColumns (F : Finset E) (root : V) :
    Matrix (AwayFrom root)
      (SelectedEdge F ⊕ AwayFrom (G.contractionMap F root)) ℝ := by
  classical
  intro v j
  cases j with
  | inl e => exact reducedSignedIncidence G root v e.1
  | inr c =>
      exact if v.1 = G.contractionRep F c.1 then 1 else 0

/-- Add one synthetic edge from the chosen representative of every non-root
forest component to the root.  The resulting labelled graph is a tree. -/
noncomputable def forestCone (F : Finset E) (root : V) :
    LabeledMultigraph V
      (SelectedEdge F ⊕ AwayFrom (G.contractionMap F root)) where
  ends e := match e with
    | Sum.inl f => G.ends f.1
    | Sum.inr c => s(G.contractionRep F c.1, root)

omit [Fintype V] [Fintype E] in
private theorem contractionRep_ne_root (F : Finset E) (root : V)
    (c : AwayFrom (G.contractionMap F root)) :
    G.contractionRep F c.1 ≠ root := by
  intro h
  apply c.property
  calc
    c.1 = G.contractionMap F (G.contractionRep F c.1) :=
      (G.contractionMap_contractionRep F c.1).symm
    _ = G.contractionMap F root := congrArg (G.contractionMap F) h

omit [Fintype V] [Fintype E] in
private theorem forestCone_connected {F : Finset E}
    (root : V) : (forestCone G F root).Connected := by
  classical
  let H := forestCone G F root
  let K := G.simpleGraphOn (F : Set E)
  letI : Nonempty V := ⟨root⟩
  have hmono : K ≤ H.toSimpleGraph := by
    intro u v huv
    rcases huv with ⟨huv, e, heF, he⟩
    exact ⟨huv, Sum.inl ⟨e, heF⟩, he⟩
  have hcomponent (u : V) :
      H.toSimpleGraph.Reachable u
        (G.contractionRep F (G.contractionMap F u)) := by
    apply SimpleGraph.Reachable.mono hmono
    apply SimpleGraph.ConnectedComponent.exact
    exact (G.contractionMap_contractionRep F (G.contractionMap F u)).symm
  have hroot (u : V) :
      H.toSimpleGraph.Reachable
        (G.contractionRep F (G.contractionMap F u)) root := by
    by_cases hu : G.contractionMap F u = G.contractionMap F root
    · apply SimpleGraph.Reachable.mono hmono
      apply SimpleGraph.ConnectedComponent.exact
      calc
        G.contractionMap F (G.contractionRep F (G.contractionMap F u)) =
            G.contractionMap F u :=
          G.contractionMap_contractionRep F (G.contractionMap F u)
        _ = G.contractionMap F root := hu
    · have hne : G.contractionRep F (G.contractionMap F u) ≠ root :=
        contractionRep_ne_root G F root ⟨G.contractionMap F u, hu⟩
      apply SimpleGraph.Adj.reachable
      exact ⟨hne, Sum.inr ⟨G.contractionMap F u, hu⟩, rfl⟩
  refine { preconnected := ?_ }
  intro u v
  exact (hcomponent u).trans ((hroot u).trans ((hroot v).symm.trans (hcomponent v).symm))

private theorem forestCone_univ_isSpanningTree {F : Finset E}
    (hF : G.IsEdgeForest F) (root : V) :
    (forestCone G F root).IsSpanningTree Finset.univ := by
  classical
  letI : Fintype (G.simpleGraphOn (F : Set E)).ConnectedComponent :=
    G.contractionComponentFintype F
  let H := forestCone G F root
  obtain ⟨T, hFT⟩ := hF
  refine ⟨?_, ?_, ?_⟩
  · intro e _he
    cases e with
    | inl f =>
        exact T.2.loopless (hFT f.2)
    | inr c =>
        exact H.not_isLoop_of_isLink_of_ne rfl
          (contractionRep_ne_root G F root c)
  · have hc := forestCone_connected G (F := F) root
    change (forestCone G F root).toSimpleGraph.Connected at hc
    simpa only [Finset.coe_univ,
      (forestCone G F root).simpleGraphOn_univ] using hc
  · have hforest := IsEdgeForest.card_add_components G ⟨T, hFT⟩
    have hVpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨root⟩
    have hComponentsPos :
        0 < Fintype.card (G.simpleGraphOn (F : Set E)).ConnectedComponent :=
      Fintype.card_pos_iff.mpr ⟨G.contractionMap F root⟩
    have hContractAway :
        Fintype.card (AwayFrom (G.contractionMap F root)) =
          Fintype.card (G.simpleGraphOn (F : Set E)).ConnectedComponent - 1 := by
      change Fintype.card
          {c : (G.simpleGraphOn (F : Set E)).ConnectedComponent //
            ¬c = G.contractionMap F root} = _
      rw [Fintype.card_subtype_compl]
      simp
    simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_coe,
      hContractAway]
    omega

private theorem forestCone_spanningTreeCount {F : Finset E}
    (hF : G.IsEdgeForest F) (root : V) :
    (forestCone G F root).spanningTreeCount = 1 := by
  classical
  letI : Fintype (G.simpleGraphOn (F : Set E)).ConnectedComponent :=
    G.contractionComponentFintype F
  let H := forestCone G F root
  let full : H.SpanningTree := ⟨Finset.univ,
    forestCone_univ_isSpanningTree G hF root⟩
  letI : Unique H.SpanningTree :=
    { default := full
      uniq := fun T => by
        apply Subtype.ext
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        have hT := T.2.card_edges_add_one
        have hfull := full.2.card_edges_add_one
        change (Finset.univ : Finset
          (SelectedEdge F ⊕ AwayFrom (G.contractionMap F root))).card + 1 =
            Fintype.card V at hfull
        omega }
  unfold spanningTreeCount
  exact Nat.card_unique

omit [Fintype V] [Fintype E] in
private theorem reducedSignedIncidence_mul_of_isLink_root
    {H : LabeledMultigraph V E} (root w : V) (e : E)
    (hlink : H.IsLink e w root) (u v : AwayFrom root) :
    reducedSignedIncidence H root u e * reducedSignedIncidence H root v e =
      (if u.1 = w then 1 else 0) * (if v.1 = w then 1 else 0) := by
  classical
  have horient :
      (H.edgeSource e = w ∧ H.edgeTarget e = root) ∨
        (H.edgeSource e = root ∧ H.edgeTarget e = w) := by
    apply Sym2.eq_iff.mp
    calc
      s(H.edgeSource e, H.edgeTarget e) = H.ends e :=
        (H.ends_edgeSource_edgeTarget e).symm
      _ = s(w, root) := hlink
  rcases horient with h | h
  · simp [reducedSignedIncidence_apply, h.1, h.2, u.property, v.property]
  · simp [reducedSignedIncidence_apply, h.1, h.2, u.property, v.property,
      eq_comm]
    split_ifs <;> norm_num

/-- The preceding coordinate columns made square by the canonical cardinality
equivalence for a forest. -/
noncomputable def forestCoordinateMatrix {F : Finset E}
    (hF : G.IsEdgeForest F) (root : V) :
    Matrix (SelectedEdge F ⊕ AwayFrom (G.contractionMap F root))
      (SelectedEdge F ⊕ AwayFrom (G.contractionMap F root)) ℝ :=
  (forestCoordinateColumns G F root).submatrix
    (forestCoordinateEquiv G hF root).symm id

/-- After the row reindexing, the coordinate matrix and the cone incidence
matrix have the same row Gram matrix.  Synthetic columns may differ in sign,
which disappears in the Gram product. -/
private theorem forestCoordinateMatrix_mul_transpose_eq_cone {F : Finset E}
    (hF : G.IsEdgeForest F) (root : V) :
    forestCoordinateMatrix G hF root *
        (forestCoordinateMatrix G hF root)ᵀ =
      let e := forestCoordinateEquiv G hF root
      let B := reducedSignedIncidence (forestCone G F root) root
      (B.submatrix e.symm id) * (B.submatrix e.symm id)ᵀ := by
  classical
  letI : Fintype (G.simpleGraphOn (F : Set E)).ConnectedComponent :=
    G.contractionComponentFintype F
  let e := forestCoordinateEquiv G hF root
  let H := forestCone G F root
  let B := reducedSignedIncidence H root
  dsimp only
  ext i j
  simp only [forestCoordinateMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.submatrix_apply]
  apply Finset.sum_congr rfl
  intro c _hc
  cases c with
  | inl f => rfl
  | inr c =>
      simp only [id_eq, forestCoordinateColumns]
      symm
      apply reducedSignedIncidence_mul_of_isLink_root root
        (G.contractionRep F c.1) (Sum.inr c)
      rfl

/-- The forest-incidence/component-representative coordinate matrix is
unimodular.  Matrix--Tree is used only for the auxiliary cone, whose unique
spanning tree is its full edge set. -/
theorem forestCoordinateMatrix_unimodular
    (hMatrixTree : LabeledMultigraphCofactorInput.{uV, max uE uV})
    {F : Finset E} (hF : G.IsEdgeForest F) (root : V) :
    (forestCoordinateMatrix G hF root).det *
        (forestCoordinateMatrix G hF root).det = 1 := by
  classical
  letI : Fintype (G.simpleGraphOn (F : Set E)).ConnectedComponent :=
    G.contractionComponentFintype F
  let e := forestCoordinateEquiv G hF root
  let H := forestCone G F root
  let B := reducedSignedIncidence H root
  let W := forestCoordinateMatrix G hF root
  have hGram := forestCoordinateMatrix_mul_transpose_eq_cone G hF root
  have hConeGram :
      (B.submatrix e.symm id) * (B.submatrix e.symm id)ᵀ =
        (H.reducedLaplacian ℝ root).submatrix e.symm e.symm := by
    rw [Matrix.transpose_submatrix]
    calc
      B.submatrix e.symm id * Bᵀ.submatrix id e.symm =
          (B * Bᵀ).submatrix e.symm e.symm := by
        simpa using Matrix.submatrix_mul_equiv B Bᵀ e.symm
          (Equiv.refl _) e.symm
      _ = (H.reducedLaplacian ℝ root).submatrix e.symm e.symm := by
        rw [reducedSignedIncidence_mul_transpose H root]
  change W * Wᵀ =
    (B.submatrix e.symm id) * (B.submatrix e.symm id)ᵀ at hGram
  rw [hConeGram] at hGram
  have hdet := congrArg Matrix.det hGram
  rw [Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_submatrix_equiv_self] at hdet
  rw [← det_reducedLaplacian_cast H root] at hdet
  have hTreeInt : (H.spanningTreeCount : ℤ) =
      (H.reducedLaplacian ℤ root).det := hMatrixTree _ _ H root
  have hTreeReal : (H.spanningTreeCount : ℝ) =
      (((H.reducedLaplacian ℤ root).det : ℤ) : ℝ) := by
    exact_mod_cast hTreeInt
  rw [← hTreeReal, forestCone_spanningTreeCount G hF root] at hdet
  norm_num at hdet ⊢
  exact hdet

/-- Sum vertex coordinates over each non-root contraction component. -/
noncomputable def forestComponentSum (F : Finset E) (root : V) :
    Matrix (AwayFrom (G.contractionMap F root)) (AwayFrom root) ℝ := by
  classical
  exact fun c v => if c.1 = G.contractionMap F v.1 then 1 else 0

private theorem sum_away_indicator (root x : V) (p : V → Prop)
    [DecidablePred p] :
    (∑ v : AwayFrom root, if p v.1 then if v.1 = x then (1 : ℝ) else 0 else 0) =
      if x = root then 0 else if p x then 1 else 0 := by
  classical
  by_cases hx : x = root
  · subst x
    rw [if_pos rfl]
    apply Finset.sum_eq_zero
    intro v _hv
    by_cases hp : p v.1 <;> simp [hp, v.property]
  · simp only [if_neg hx]
    calc
      (∑ v : AwayFrom root,
          if p v.1 then if v.1 = x then (1 : ℝ) else 0 else 0) =
          ∑ v : AwayFrom root,
            if v = ⟨x, hx⟩ then (if p v.1 then 1 else 0) else 0 := by
        apply Fintype.sum_congr
        intro v
        by_cases hp : p v.1 <;> by_cases hv : v.1 = x <;>
          simp_all [Subtype.ext_iff]
      _ = if p x then 1 else 0 := by
        rw [Fintype.sum_ite_eq']

omit [Fintype E] in
private theorem forestComponentSum_mul_reducedSignedIncidence_apply
    (F : Finset E) (root : V)
    (c : AwayFrom (G.contractionMap F root)) (edge : E) :
    (forestComponentSum G F root * reducedSignedIncidence G root) c edge =
      (if c.1 = G.contractionMap F (G.edgeSource edge) then 1 else 0) -
        (if c.1 = G.contractionMap F (G.edgeTarget edge) then 1 else 0) := by
  classical
  simp only [Matrix.mul_apply, forestComponentSum,
    reducedSignedIncidence_apply, mul_sub, Finset.sum_sub_distrib]
  simp only [ite_mul, one_mul, zero_mul]
  rw [sum_away_indicator root (G.edgeSource edge)
      (fun v => c.1 = G.contractionMap F v),
    sum_away_indicator root (G.edgeTarget edge)
      (fun v => c.1 = G.contractionMap F v)]
  by_cases hs : G.edgeSource edge = root <;>
    by_cases ht : G.edgeTarget edge = root <;>
    simp [hs, ht, c.property]

omit [Fintype E] in
private theorem forestComponentAggregated_column_mul
    (F : Finset E) (root : V)
    (c d : AwayFrom (G.contractionMap F root)) (edge : E) :
    (forestComponentSum G F root * reducedSignedIncidence G root) c edge *
        (forestComponentSum G F root * reducedSignedIncidence G root) d edge =
      reducedSignedIncidence (G.contractWithLoops F)
          (G.contractionMap F root) c edge *
        reducedSignedIncidence (G.contractWithLoops F)
          (G.contractionMap F root) d edge := by
  classical
  rw [forestComponentSum_mul_reducedSignedIncidence_apply,
    forestComponentSum_mul_reducedSignedIncidence_apply]
  have horient :
      ((G.contractWithLoops F).edgeSource edge =
          G.contractionMap F (G.edgeSource edge) ∧
        (G.contractWithLoops F).edgeTarget edge =
          G.contractionMap F (G.edgeTarget edge)) ∨
      ((G.contractWithLoops F).edgeSource edge =
          G.contractionMap F (G.edgeTarget edge) ∧
        (G.contractWithLoops F).edgeTarget edge =
          G.contractionMap F (G.edgeSource edge)) := by
    apply Sym2.eq_iff.mp
    calc
      s((G.contractWithLoops F).edgeSource edge,
          (G.contractWithLoops F).edgeTarget edge) =
          (G.contractWithLoops F).ends edge :=
        ((G.contractWithLoops F).ends_edgeSource_edgeTarget edge).symm
      _ = Sym2.map (G.contractionMap F) (G.ends edge) := rfl
      _ = s(G.contractionMap F (G.edgeSource edge),
          G.contractionMap F (G.edgeTarget edge)) := by
        rw [G.ends_edgeSource_edgeTarget, Sym2.map_mk]
  rcases horient with h | h
  · simp [reducedSignedIncidence_apply, h.1, h.2]
  · simp only [reducedSignedIncidence_apply, h.1, h.2]
    ring

/-- Compressing the original reduced Laplacian by component sums gives the
reduced Laplacian after simultaneous contraction. -/
theorem forestComponentSum_mul_reducedLaplacian_mul_transpose
    (F : Finset E) (root : V) :
    forestComponentSum G F root * G.reducedLaplacian ℝ root *
        (forestComponentSum G F root)ᵀ =
      (G.contract F).reducedLaplacian ℝ (G.contractionMap F root) := by
  classical
  letI : Fintype (G.simpleGraphOn (F : Set E)).ConnectedComponent :=
    G.contractionComponentFintype F
  let S := forestComponentSum G F root
  let B := reducedSignedIncidence G root
  let H := G.contractWithLoops F
  let BH := reducedSignedIncidence H (G.contractionMap F root)
  have hGram : (S * B) * (S * B)ᵀ = BH * BHᵀ := by
    ext c d
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro edge _hedge
    exact forestComponentAggregated_column_mul G F root c d edge
  rw [← reducedSignedIncidence_mul_transpose G root]
  calc
    S * (B * Bᵀ) * Sᵀ = (S * B) * (S * B)ᵀ := by
      rw [Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    _ = BH * BHᵀ := hGram
    _ = H.reducedLaplacian ℝ (G.contractionMap F root) :=
      reducedSignedIncidence_mul_transpose H (G.contractionMap F root)
    _ = (G.contract F).reducedLaplacian ℝ
        (G.contractionMap F root) := by
      simpa only [H, contract] using
        (H.deleteLoops_reducedLaplacian ℝ
          (G.contractionMap F root)).symm

private theorem contractionMap_edgeSource_eq_edgeTarget_of_mem
    {F : Finset E} (hF : G.IsEdgeForest F) {edge : E} (hedge : edge ∈ F) :
    G.contractionMap F (G.edgeSource edge) =
      G.contractionMap F (G.edgeTarget edge) := by
  obtain ⟨T, hFT⟩ := hF
  have hloop : (G.contractWithLoops F).IsLoop edge :=
    G.contractWithLoops_isLoop_of_mem hedge (T.2.loopless (hFT hedge))
  change (Sym2.map (G.contractionMap F) (G.ends edge)).IsDiag at hloop
  rw [G.ends_edgeSource_edgeTarget, Sym2.map_mk,
    Sym2.mk_isDiag_iff] at hloop
  exact hloop

private theorem forestComponentSum_mul_selectedIncidence
    {F : Finset E} (hF : G.IsEdgeForest F) (root : V)
    (c : AwayFrom (G.contractionMap F root)) (edge : SelectedEdge F) :
    (forestComponentSum G F root * reducedSignedIncidence G root) c edge.1 = 0 := by
  rw [forestComponentSum_mul_reducedSignedIncidence_apply]
  rw [contractionMap_edgeSource_eq_edgeTarget_of_mem G hF edge.2]
  exact sub_self _

/-- In component-sum coordinates the forest incidence columns vanish and
the representative columns form the identity. -/
theorem forestComponentSum_mul_forestCoordinateColumns
    {F : Finset E} (hF : G.IsEdgeForest F) (root : V) :
    forestComponentSum G F root * forestCoordinateColumns G F root =
      (1 : Matrix
        (SelectedEdge F ⊕ AwayFrom (G.contractionMap F root))
        (SelectedEdge F ⊕ AwayFrom (G.contractionMap F root)) ℝ).submatrix
          Sum.inr id := by
  classical
  letI : Fintype (G.simpleGraphOn (F : Set E)).ConnectedComponent :=
    G.contractionComponentFintype F
  ext c j
  cases j with
  | inl edge =>
      change
        (forestComponentSum G F root * reducedSignedIncidence G root)
          c edge.1 = 0
      exact forestComponentSum_mul_selectedIncidence G hF root c edge
  | inr d =>
      simp only [Matrix.mul_apply, forestComponentSum, forestCoordinateColumns,
        Matrix.submatrix_apply, Matrix.one_apply, ite_mul,
        one_mul, zero_mul]
      rw [sum_away_indicator root (G.contractionRep F d.1)
        (fun v => c.1 = G.contractionMap F v)]
      have hrep : G.contractionRep F d.1 ≠ root :=
        contractionRep_ne_root G F root d
      rw [if_neg hrep, G.contractionMap_contractionRep]
      simp only [id_eq, Sum.inr.injEq, Subtype.ext_iff]

/-- Component sums expressed in the square forest coordinate row indexing. -/
noncomputable def forestComponentCoordinateRows {F : Finset E}
    (hF : G.IsEdgeForest F) (root : V) :
    Matrix (AwayFrom (G.contractionMap F root))
      (SelectedEdge F ⊕ AwayFrom (G.contractionMap F root)) ℝ :=
  (forestComponentSum G F root).submatrix id
    (forestCoordinateEquiv G hF root).symm

/-- The component-sum rows are the bottom rows of the inverse forest
coordinate change of basis. -/
theorem forestComponentCoordinateRows_mul_forestCoordinateMatrix
    {F : Finset E} (hF : G.IsEdgeForest F) (root : V) :
    forestComponentCoordinateRows G hF root *
        forestCoordinateMatrix G hF root =
      (1 : Matrix
        (SelectedEdge F ⊕ AwayFrom (G.contractionMap F root))
        (SelectedEdge F ⊕ AwayFrom (G.contractionMap F root)) ℝ).submatrix
          Sum.inr id := by
  classical
  letI : Fintype (G.simpleGraphOn (F : Set E)).ConnectedComponent :=
    G.contractionComponentFintype F
  let e := forestCoordinateEquiv G hF root
  let S := forestComponentSum G F root
  let C := forestCoordinateColumns G F root
  change S.submatrix id e.symm * C.submatrix e.symm id = _
  rw [Matrix.submatrix_mul_equiv]
  exact forestComponentSum_mul_forestCoordinateColumns G hF root

/-- The component-sum rows are literally the bottom rows of the inverse
forest coordinate matrix. -/
theorem forestCoordinateMatrix_inv_bottomRows
    (hMatrixTree : LabeledMultigraphCofactorInput.{uV, max uE uV})
    {F : Finset E} (hF : G.IsEdgeForest F) (root : V) :
    (forestCoordinateMatrix G hF root)⁻¹.submatrix Sum.inr id =
      forestComponentCoordinateRows G hF root := by
  classical
  letI : Fintype (G.simpleGraphOn (F : Set E)).ConnectedComponent :=
    G.contractionComponentFintype F
  let J := SelectedEdge F ⊕ AwayFrom (G.contractionMap F root)
  let W := forestCoordinateMatrix G hF root
  let R := forestComponentCoordinateRows G hF root
  let P := (1 : Matrix J J ℝ).submatrix Sum.inr id
  have hunimod := forestCoordinateMatrix_unimodular G hMatrixTree hF root
  have hdet : W.det ≠ 0 := by
    intro hzero
    change W.det * W.det = 1 at hunimod
    rw [hzero, zero_mul] at hunimod
    norm_num at hunimod
  have hunit : IsUnit W.det := isUnit_iff_ne_zero.mpr hdet
  have hRW : R * W = P := by
    exact forestComponentCoordinateRows_mul_forestCoordinateMatrix G hF root
  have hPInv : P * W⁻¹ = W⁻¹.submatrix Sum.inr id := by
    dsimp only [P]
    simpa using Matrix.submatrix_mul_equiv
      (1 : Matrix J J ℝ) W⁻¹ Sum.inr (Equiv.refl J) id
  change W⁻¹.submatrix Sum.inr id = R
  calc
    W⁻¹.submatrix Sum.inr id = P * W⁻¹ := hPInv.symm
    _ = (R * W) * W⁻¹ := by rw [hRW]
    _ = R * (W * W⁻¹) := Matrix.mul_assoc _ _ _
    _ = R := by rw [Matrix.mul_nonsing_inv W hunit, Matrix.mul_one]

/-- The reduced Laplacian in the same forest/component row coordinates. -/
noncomputable def forestCoordinateLaplacian {F : Finset E}
    (hF : G.IsEdgeForest F) (root : V) :
    Matrix (SelectedEdge F ⊕ AwayFrom (G.contractionMap F root))
      (SelectedEdge F ⊕ AwayFrom (G.contractionMap F root)) ℝ :=
  (G.reducedLaplacian ℝ root).submatrix
    (forestCoordinateEquiv G hF root).symm
    (forestCoordinateEquiv G hF root).symm

/-- The inverse-Laplacian Gram matrix in forest/component block coordinates. -/
noncomputable def forestBlockMatrix {F : Finset E}
    (hF : G.IsEdgeForest F) (root : V) :
    Matrix (SelectedEdge F ⊕ AwayFrom (G.contractionMap F root))
      (SelectedEdge F ⊕ AwayFrom (G.contractionMap F root)) ℝ :=
  (forestCoordinateMatrix G hF root)ᵀ *
    (forestCoordinateLaplacian G hF root)⁻¹ *
      forestCoordinateMatrix G hF root

/-- In the square forest coordinates, component-sum compression still gives
the contracted reduced Laplacian. -/
theorem forestComponentCoordinateRows_mul_forestCoordinateLaplacian_mul_transpose
    {F : Finset E} (hF : G.IsEdgeForest F) (root : V) :
    forestComponentCoordinateRows G hF root *
        forestCoordinateLaplacian G hF root *
          (forestComponentCoordinateRows G hF root)ᵀ =
      (G.contract F).reducedLaplacian ℝ (G.contractionMap F root) := by
  classical
  letI : Fintype (G.simpleGraphOn (F : Set E)).ConnectedComponent :=
    G.contractionComponentFintype F
  let e := forestCoordinateEquiv G hF root
  let S := forestComponentSum G F root
  let L := G.reducedLaplacian ℝ root
  change S.submatrix id e.symm * L.submatrix e.symm e.symm *
      (S.submatrix id e.symm)ᵀ = _
  rw [Matrix.transpose_submatrix]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  simpa using
    forestComponentSum_mul_reducedLaplacian_mul_transpose G F root

/-- The complementary inverse block of the inverse-Laplacian forest Gram
matrix is the reduced Laplacian of the contracted graph. -/
theorem forestBlockMatrix_inv_toBlocks₂₂
    (hMatrixTree : LabeledMultigraphCofactorInput.{uV, uE})
    (hMatrixTreeCone :
      LabeledMultigraphCofactorInput.{uV, max uE uV})
    (hCount : 0 < G.spanningTreeCount)
    {F : Finset E} (hF : G.IsEdgeForest F) (root : V) :
    (forestBlockMatrix G hF root)⁻¹.toBlocks₂₂ =
      (G.contract F).reducedLaplacian ℝ (G.contractionMap F root) := by
  classical
  letI : Fintype (G.simpleGraphOn (F : Set E)).ConnectedComponent :=
    G.contractionComponentFintype F
  let e := forestCoordinateEquiv G hF root
  let J := SelectedEdge F ⊕ AwayFrom (G.contractionMap F root)
  let W := forestCoordinateMatrix G hF root
  let Lc := forestCoordinateLaplacian G hF root
  let M := forestBlockMatrix G hF root
  let R := forestComponentCoordinateRows G hF root
  let N := W⁻¹ * Lc * (W⁻¹)ᵀ
  have hL : (G.reducedLaplacian ℝ root).PosDef :=
    reducedLaplacian_posDef G hMatrixTree hCount root
  have hLc : Lc.PosDef := by
    exact hL.submatrix e.symm.injective
  letI iLc : Invertible Lc := hLc.isUnit.invertible
  have hunimod :=
    forestCoordinateMatrix_unimodular G hMatrixTreeCone hF root
  have hWdet : W.det ≠ 0 := by
    intro hzero
    change W.det * W.det = 1 at hunimod
    rw [hzero, zero_mul] at hunimod
    norm_num at hunimod
  have hWdetUnit : IsUnit W.det := isUnit_iff_ne_zero.mpr hWdet
  letI iW : Invertible W := Matrix.invertibleOfIsUnitDet W hWdetUnit
  have hMN : M * N = 1 := by
    change (Wᵀ * Lc⁻¹ * W) * (W⁻¹ * Lc * (W⁻¹)ᵀ) = 1
    simp only [Matrix.mul_assoc, Matrix.mul_inv_cancel_left_of_invertible,
      Matrix.inv_mul_cancel_left_of_invertible]
    rw [← Matrix.transpose_mul, Matrix.inv_mul_of_invertible,
      Matrix.transpose_one]
  have hMinv : M⁻¹ = N := Matrix.inv_eq_right_inv hMN
  have hBottomRows : W⁻¹.submatrix Sum.inr id = R :=
    forestCoordinateMatrix_inv_bottomRows G hMatrixTreeCone hF root
  change M⁻¹.toBlocks₂₂ = _
  rw [hMinv]
  change (W⁻¹ * Lc * (W⁻¹)ᵀ).submatrix Sum.inr Sum.inr = _
  calc
    (W⁻¹ * Lc * (W⁻¹)ᵀ).submatrix Sum.inr Sum.inr =
        (W⁻¹.submatrix Sum.inr id * Lc) *
          (W⁻¹.submatrix Sum.inr id)ᵀ := by
      rw [Matrix.transpose_submatrix]
      symm
      have hFirst : W⁻¹.submatrix Sum.inr id * Lc =
          (W⁻¹ * Lc).submatrix Sum.inr id := by
        simpa using Matrix.submatrix_mul_equiv W⁻¹ Lc Sum.inr
          (Equiv.refl J) id
      rw [hFirst]
      simpa using Matrix.submatrix_mul_equiv (W⁻¹ * Lc) W⁻¹ᵀ
        Sum.inr (Equiv.refl J) Sum.inr
    _ = R * Lc * Rᵀ := by rw [hBottomRows]
    _ = (G.contract F).reducedLaplacian ℝ
        (G.contractionMap F root) :=
      forestComponentCoordinateRows_mul_forestCoordinateLaplacian_mul_transpose
        G hF root

/-- The upper-left block is exactly the forest principal submatrix of the
canonical transfer-current kernel. -/
theorem forestBlockMatrix_toBlocks₁₁ {F : Finset E}
    (hF : G.IsEdgeForest F) (root : V) :
    (forestBlockMatrix G hF root).toBlocks₁₁ =
      HadamardFischer.principalSubmatrix
        (reducedTransferKernel G root) F := by
  classical
  letI : Fintype (G.simpleGraphOn (F : Set E)).ConnectedComponent :=
    G.contractionComponentFintype F
  let e := forestCoordinateEquiv G hF root
  ext x y
  simp only [forestBlockMatrix, forestCoordinateMatrix,
    forestCoordinateLaplacian, forestCoordinateColumns,
    HadamardFischer.principalSubmatrix, reducedTransferKernel,
    Matrix.toBlocks₁₁, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.of_apply,
    Matrix.transpose_apply, Matrix.inv_submatrix_equiv]
  simp only [id_eq]
  change (∑ j, (∑ i, reducedSignedIncidence G root (e.symm i) x.1 *
      (G.reducedLaplacian ℝ root)⁻¹ (e.symm i) (e.symm j)) *
        reducedSignedIncidence G root (e.symm j) y.1) = _
  calc
    (∑ j, (∑ i, reducedSignedIncidence G root (e.symm i) x.1 *
        (G.reducedLaplacian ℝ root)⁻¹ (e.symm i) (e.symm j)) *
          reducedSignedIncidence G root (e.symm j) y.1) =
        ∑ j : AwayFrom root,
          (∑ i, reducedSignedIncidence G root (e.symm i) x.1 *
            (G.reducedLaplacian ℝ root)⁻¹ (e.symm i) j) *
              reducedSignedIncidence G root j y.1 := by
        exact e.symm.sum_comp (fun j : AwayFrom root =>
          (∑ i, reducedSignedIncidence G root (e.symm i) x.1 *
            (G.reducedLaplacian ℝ root)⁻¹ (e.symm i) j) *
              reducedSignedIncidence G root j y.1)
    _ = ∑ j : AwayFrom root,
          (∑ i : AwayFrom root, reducedSignedIncidence G root i x.1 *
            (G.reducedLaplacian ℝ root)⁻¹ i j) *
              reducedSignedIncidence G root j y.1 := by
        apply Finset.sum_congr rfl
        intro j _hj
        congr 1
        exact e.symm.sum_comp (fun i : AwayFrom root =>
          reducedSignedIncidence G root i x.1 *
            (G.reducedLaplacian ℝ root)⁻¹ i j)

/-- The two explicit forest-coordinate facts needed after the generic block
Jacobi identity: the incidence/representative change of basis is unimodular,
and its complementary inverse block is the contracted reduced Laplacian. -/
structure ForestCoordinateCertificate {F : Finset E}
    (hF : G.IsEdgeForest F) (root : V) : Prop where
  unimodular :
    (forestCoordinateMatrix G hF root).det *
      (forestCoordinateMatrix G hF root).det = 1
  inverse_bottom_block :
    (forestBlockMatrix G hF root)⁻¹.toBlocks₂₂ =
      (G.contract F).reducedLaplacian ℝ (G.contractionMap F root)

/-- Matrix--Tree supplies the complete forest-coordinate certificate. -/
theorem forestCoordinateCertificateOfMatrixTree
    (hMatrixTree : LabeledMultigraphCofactorInput.{uV, uE})
    (hMatrixTreeCone :
      LabeledMultigraphCofactorInput.{uV, max uE uV})
    (hCount : 0 < G.spanningTreeCount)
    {F : Finset E} (hF : G.IsEdgeForest F) (root : V) :
    G.ForestCoordinateCertificate hF root where
  unimodular :=
    forestCoordinateMatrix_unimodular G hMatrixTreeCone hF root
  inverse_bottom_block :=
    forestBlockMatrix_inv_toBlocks₂₂ G hMatrixTree hMatrixTreeCone
      hCount hF root

/-- The explicit forest-coordinate certificate implies the full
complementary-minor/contraction identity. -/
theorem forestContractionComplementaryMinor_of_coordinateCertificate
    (hMatrixTree : LabeledMultigraphCofactorInput.{uV, uE})
    (hCount : 0 < G.spanningTreeCount) (root : V)
    {F : Finset E} (hF : G.IsEdgeForest F)
    (hCoordinate : G.ForestCoordinateCertificate hF root) :
    HadamardFischer.principalDet (reducedTransferKernel G root) F =
      Matrix.det ((G.contract F).reducedLaplacian ℝ
          (G.contractionMap F root)) /
        Matrix.det (G.reducedLaplacian ℝ root) := by
  classical
  letI : Fintype (G.simpleGraphOn (F : Set E)).ConnectedComponent :=
    G.contractionComponentFintype F
  let e := forestCoordinateEquiv G hF root
  let W := forestCoordinateMatrix G hF root
  let L := G.reducedLaplacian ℝ root
  let Lc := forestCoordinateLaplacian G hF root
  let M := forestBlockMatrix G hF root
  have hL : L.PosDef := reducedLaplacian_posDef G hMatrixTree hCount root
  letI iL : Invertible L := hL.isUnit.invertible
  letI iLdet : Invertible L.det := Matrix.detInvertibleOfInvertible L
  have hLc : Lc.PosDef := by
    exact hL.submatrix e.symm.injective
  letI iLc : Invertible Lc := hLc.isUnit.invertible
  letI iLcDet : Invertible Lc.det := Matrix.detInvertibleOfInvertible Lc
  have hLcInv : Lc⁻¹.PosDef := hLc.inv
  have hWdet : W.det ≠ 0 := by
    intro hzero
    have h := hCoordinate.unimodular
    change W.det * W.det = 1 at h
    rw [hzero, zero_mul] at h
    norm_num at h
  have hWunit : IsUnit W := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact hWdet
  have hM : M.PosDef := by
    have hgram := hLcInv.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_iff_isUnit.mpr hWunit)
    change (Wᵀ * Lc⁻¹ * W).PosDef
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hgram
  have hMdet : M.det = L.det⁻¹ := by
    change (Wᵀ * Lc⁻¹ * W).det = L.det⁻¹
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_nonsing_inv]
    rw [Ring.inverse_invertible]
    rw [invOf_eq_inv]
    have hLcDet : Lc.det = L.det := by
      exact Matrix.det_submatrix_equiv_self e.symm L
    rw [hLcDet]
    have hunimodular := hCoordinate.unimodular
    change W.det * W.det = 1 at hunimodular
    calc
      W.det * L.det⁻¹ * W.det = (W.det * W.det) * L.det⁻¹ := by ring
      _ = L.det⁻¹ := by rw [hunimodular, one_mul]
  have hJacobi := det_toBlocks₁₁_eq_det_mul_det_inv_toBlocks₂₂ M hM
  rw [forestBlockMatrix_toBlocks₁₁ G hF root] at hJacobi
  rw [HadamardFischer.principalDet]
  rw [hJacobi, hMdet, hCoordinate.inverse_bottom_block]
  rw [div_eq_mul_inv, mul_comm]

/-- The forest complementary-minor/contraction identity, constructed from
Matrix--Tree with no separate all-minors input. -/
theorem forestContractionComplementaryMinor_of_matrixTree
    (hMatrixTree : LabeledMultigraphCofactorInput.{uV, uE})
    (hMatrixTreeCone :
      LabeledMultigraphCofactorInput.{uV, max uE uV})
    (hCount : 0 < G.spanningTreeCount) (root : V) :
    ForestContractionComplementaryMinorInput G root := by
  intro F hF
  exact forestContractionComplementaryMinor_of_coordinateCertificate G
    hMatrixTree hCount root hF
      (forestCoordinateCertificateOfMatrixTree G hMatrixTree
        hMatrixTreeCone hCount hF root)

/-- Construct the complete transfer-current determinant interface from the
Matrix--Tree interface proved elsewhere in the development. -/
noncomputable def transferCurrentDeterminantInputOfMatrixTree
    (hMatrixTree : LabeledMultigraphCofactorInput.{uV, uE})
    (hMatrixTreeCone :
      LabeledMultigraphCofactorInput.{uV, max uE uV})
    (hCount : 0 < G.spanningTreeCount) (root : V) :
    G.TransferCurrentDeterminantInput :=
  transferCurrentDeterminantInput G hMatrixTree hCount root
    (forestContractionComplementaryMinor_of_matrixTree G hMatrixTree
      hMatrixTreeCone hCount root)

omit [Fintype V] [Fintype E] in
private theorem exists_label_of_mem_subgraph_edgeSet
    (T : SimpleGraph V) (hTG : T ≤ G.toSimpleGraph)
    (p : T.edgeSet) : ∃ edge : E, G.ends edge = p.1 := by
  have hpG : p.1 ∈ G.toSimpleGraph.edgeSet :=
    SimpleGraph.edgeSet_mono hTG p.2
  induction hp : p.1 using Sym2.inductionOn with
  | _ u v =>
      rw [hp, SimpleGraph.mem_edgeSet] at hpG
      obtain ⟨_huv, edge, hedge⟩ := hpG
      exact ⟨edge, hedge⟩

/-- Choose one original edge label above every edge of a simple subgraph. -/
noncomputable def labelSimpleSubgraphEdge
    (T : SimpleGraph V) (hTG : T ≤ G.toSimpleGraph) (p : T.edgeSet) : E :=
  Classical.choose (exists_label_of_mem_subgraph_edgeSet G T hTG p)

omit [Fintype V] [Fintype E] in
@[simp] theorem labelSimpleSubgraphEdge_ends
    (T : SimpleGraph V) (hTG : T ≤ G.toSimpleGraph) (p : T.edgeSet) :
    G.ends (labelSimpleSubgraphEdge G T hTG p) = p.1 :=
  Classical.choose_spec (exists_label_of_mem_subgraph_edgeSet G T hTG p)

omit [Fintype V] [Fintype E] in
private theorem labelSimpleSubgraphEdge_injective
    (T : SimpleGraph V) (hTG : T ≤ G.toSimpleGraph) :
    Function.Injective (labelSimpleSubgraphEdge G T hTG) := by
  intro p q hpq
  apply Subtype.ext
  rw [← labelSimpleSubgraphEdge_ends G T hTG p,
    ← labelSimpleSubgraphEdge_ends G T hTG q, hpq]

/-- The chosen labels over a finite simple subgraph. -/
noncomputable def labelsOfSimpleSubgraph
    (T : SimpleGraph V) [Fintype T.edgeSet]
    (hTG : T ≤ G.toSimpleGraph) : Finset E :=
  Finset.univ.map
    ⟨labelSimpleSubgraphEdge G T hTG,
      labelSimpleSubgraphEdge_injective G T hTG⟩

omit [Fintype V] [Fintype E] in
private theorem simpleGraphOn_labelsOfSimpleSubgraph
    (T : SimpleGraph V) [Fintype T.edgeSet]
    (hTG : T ≤ G.toSimpleGraph) :
    G.simpleGraphOn (labelsOfSimpleSubgraph G T hTG : Set E) = T := by
  classical
  ext u v
  constructor
  · rintro ⟨_huv, edge, hedgeF, hedge⟩
    change edge ∈ labelsOfSimpleSubgraph G T hTG at hedgeF
    rw [labelsOfSimpleSubgraph, Finset.mem_map] at hedgeF
    obtain ⟨p, hpT, rfl⟩ := hedgeF
    have hpEnds : p.1 = s(u, v) := by
      rw [← labelSimpleSubgraphEdge_ends G T hTG p]
      exact hedge
    rw [← SimpleGraph.mem_edgeSet, ← hpEnds]
    exact p.2
  · intro huv
    let p : T.edgeSet := ⟨s(u, v), (SimpleGraph.mem_edgeSet T).mpr huv⟩
    refine ⟨huv.ne, labelSimpleSubgraphEdge G T hTG p, ?_, ?_⟩
    · change labelSimpleSubgraphEdge G T hTG p ∈
        labelsOfSimpleSubgraph G T hTG
      rw [labelsOfSimpleSubgraph, Finset.mem_map]
      exact ⟨p, Finset.mem_univ p, rfl⟩
    · exact labelSimpleSubgraphEdge_ends G T hTG p

/-- Every connected finite labelled multigraph has at least one labelled
spanning tree. -/
theorem spanningTreeCount_pos_of_connected (hG : G.Connected) :
    0 < G.spanningTreeCount := by
  classical
  obtain ⟨T, hTG, hTree⟩ := hG.exists_isTree_le
  let F := labelsOfSimpleSubgraph G T hTG
  apply G.spanningTreeCount_pos_iff.mpr
  refine ⟨F, ?_, ?_, ?_⟩
  · intro edge hedgeF
    dsimp only [F] at hedgeF
    rw [labelsOfSimpleSubgraph, Finset.mem_map] at hedgeF
    obtain ⟨p, hpT, rfl⟩ := hedgeF
    change ¬(G.ends (labelSimpleSubgraphEdge G T hTG p)).IsDiag
    rw [labelSimpleSubgraphEdge_ends]
    exact T.not_isDiag_of_mem_edgeSet p.2
  · rw [simpleGraphOn_labelsOfSimpleSubgraph G T hTG]
    exact hTree.connected
  · dsimp only [F]
    rw [labelsOfSimpleSubgraph, Finset.card_map, Finset.card_univ,
      ← SimpleGraph.edgeFinset_card]
    exact hTree.card_edgeFinset

/-- Connected-graph form of the transfer-current constructor. -/
noncomputable def transferCurrentDeterminantInputOfConnectedMatrixTree
    (hMatrixTree : LabeledMultigraphCofactorInput.{uV, uE})
    (hMatrixTreeCone :
      LabeledMultigraphCofactorInput.{uV, max uE uV})
    (hConnected : G.Connected) (root : V) :
    G.TransferCurrentDeterminantInput :=
  transferCurrentDeterminantInputOfMatrixTree G hMatrixTree hMatrixTreeCone
    (spanningTreeCount_pos_of_connected G hConnected) root

/-- Same-universe convenience form: one Matrix--Tree input applies both to
the original graph and to every auxiliary forest cone.  In particular this
is the form used by finite `Type`-valued rectangle duals. -/
noncomputable def transferCurrentDeterminantInputOfConnectedMatrixTreeSameUniverse
    {V' E' : Type uV} (H : LabeledMultigraph V' E')
    [Fintype V'] [Fintype E']
    (hMatrixTree : LabeledMultigraphCofactorInput.{uV, uV})
    (hConnected : H.Connected) (root : V') :
    H.TransferCurrentDeterminantInput :=
  transferCurrentDeterminantInputOfConnectedMatrixTree H hMatrixTree
    hMatrixTree hConnected root

end

end LabeledMultigraph
end SquareMaximality.Multigraph
