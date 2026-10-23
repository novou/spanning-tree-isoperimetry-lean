module

public import SpanningTreeIsoperimetry.CornerEnergyTransfer
public import SquareMaximality.Boundary.SpectralBound
public import SquareMaximality.ClosedWalk.EntropySeries
public import SquareMaximality.Multigraph.TransferCurrentConstruction

@[expose] public section

/-!
# Connecting the concrete corner words with Dirichlet determinants

The finite alphabet, positions, normalized visited sets, and rectangular
placements are matched with the fully proved local trace-walk foundation.
-/

namespace SpanningTreeIsoperimetry.CornerEnergy

open scoped BigOperators
open Ferrers

abbrev FoundationStep := SquareMaximality.ClosedWalk.Step

def foundationStepEquiv : Fin 4 ≃ FoundationStep where
  toFun := ![.east, .west, .north, .south]
  invFun
    | .east => 0
    | .west => 1
    | .north => 2
    | .south => 3
  left_inv d := by fin_cases d <;> rfl
  right_inv d := by cases d <;> rfl

@[simp] theorem foundationStep_vector (d : Fin 4) :
    (foundationStepEquiv d).vector = direction d := by fin_cases d <;> rfl

def foundationWordEquiv (ℓ : ℕ) : Word ℓ ≃ SquareMaximality.ClosedWalk.Word ℓ :=
  Equiv.piCongrRight (fun _ => foundationStepEquiv)

theorem foundation_position {ℓ : ℕ} (w : Word ℓ) (i : ℕ) (hi : i ≤ ℓ) :
    SquareMaximality.ClosedWalk.position (foundationWordEquiv ℓ w) i = position w i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [position_succ w (by omega)]
    have hprev := ih (by omega)
    unfold SquareMaximality.ClosedWalk.position at hprev ⊢
    rw [Finset.sum_range_succ, hprev]
    simp [SquareMaximality.ClosedWalk.stepAt, show i < ℓ by omega, foundationWordEquiv]

theorem foundation_partialSums {ℓ : ℕ} (w : Word ℓ) :
    SquareMaximality.ClosedWalk.partialSums (foundationWordEquiv ℓ w) = visited w := by
  unfold SquareMaximality.ClosedWalk.partialSums visited
  apply Finset.image_congr
  intro i hi
  exact foundation_position w i (by have := Finset.mem_range.mp hi; omega)

theorem foundation_isClosed {ℓ : ℕ} (w : Word ℓ) :
    SquareMaximality.ClosedWalk.IsClosed (foundationWordEquiv ℓ w) ↔ position w ℓ = (0, 0) := by
  rw [SquareMaximality.ClosedWalk.IsClosed,
    ← SquareMaximality.ClosedWalk.position_length, foundation_position w ℓ le_rfl]

def foundationClosedWordEquiv (ℓ : ℕ) : ClosedWord ℓ ≃
    {w : SquareMaximality.ClosedWalk.Word ℓ // SquareMaximality.ClosedWalk.IsClosed w} :=
  (foundationWordEquiv ℓ).subtypeEquiv (fun w => (foundation_isClosed w).symm)

theorem foundation_walkMinX {ℓ : ℕ} (w : Word ℓ) :
    SquareMaximality.Boundary.walkMinX (foundationWordEquiv ℓ w) =
      minimumX (visited w) (visited_nonempty w) := by
  simp [SquareMaximality.Boundary.walkMinX, SquareMaximality.ClosedWalk.visitedX,
    foundation_partialSums, minimumX]

theorem foundation_walkMinY {ℓ : ℕ} (w : Word ℓ) :
    SquareMaximality.Boundary.walkMinY (foundationWordEquiv ℓ w) =
      minimumY (visited w) (visited_nonempty w) := by
  simp [SquareMaximality.Boundary.walkMinY, SquareMaximality.ClosedWalk.visitedY,
    foundation_partialSums, minimumY]

theorem foundation_normalizedWalkPoint {ℓ : ℕ} (w : Word ℓ) (p : Vertex) :
    SquareMaximality.Boundary.normalizedWalkPoint (foundationWordEquiv ℓ w) p =
      normalizePoint (visited w) (visited_nonempty w) p := by
  simp only [SquareMaximality.Boundary.normalizedWalkPoint, normalizePoint,
    foundation_walkMinX, foundation_walkMinY]

theorem foundation_normalizedPartialSums {ℓ : ℕ} (w : Word ℓ) :
    SquareMaximality.Boundary.normalizedPartialSums (foundationWordEquiv ℓ w) =
      normalizedVisited w := by
  simp only [SquareMaximality.Boundary.normalizedPartialSums, foundation_partialSums,
    normalizedVisited, normalizeVisited]
  apply Finset.image_congr
  intro p _
  exact foundation_normalizedWalkPoint w p

theorem foundation_faceIndices (m n : ℕ) :
    SquareMaximality.Boundary.faceIndices m n = faceRectangle m n := by
  ext t
  simp only [SquareMaximality.Boundary.mem_faceIndices, mem_faceRectangle]
  omega

/-- A corner lower ideal marks exactly its own faces. -/
theorem foundation_markedFaces {m n : ℕ} {M : Diagram} (hM : IsFerrers M)
    (hU : M ⊆ faceRectangle m n) : SquareMaximality.Boundary.markedFaces m n M = M := by
  ext t
  rw [SquareMaximality.Boundary.mem_markedFaces]
  constructor
  · rintro ⟨_, _, p, hp, htx, _, hty, _⟩
    exact hM p hp t htx hty
  · intro ht
    have hf := mem_faceRectangle.mp (hU ht)
    exact ⟨by omega, by omega, t, ht, le_rfl, by omega, le_rfl, by omega⟩

theorem foundation_spanX {ℓ : ℕ} (w : Word ℓ) :
    (normalizedVisited w).sup Prod.fst =
      SquareMaximality.ClosedWalk.spanX (foundationWordEquiv ℓ w) := by
  rw [← foundation_normalizedPartialSums w]
  apply le_antisymm
  · apply Finset.sup_le
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact SquareMaximality.Boundary.normalizedWalkPoint_fst_le_spanX _ hp
  · let v := foundationWordEquiv ℓ w
    have hm := Finset.max'_mem (SquareMaximality.ClosedWalk.visitedX v)
      (SquareMaximality.ClosedWalk.visitedX_nonempty v)
    obtain ⟨p, hp, hx⟩ := Finset.mem_image.mp hm
    have h := Finset.le_sup (f := Prod.fst) (Finset.mem_image.mpr
      ⟨p, hp, rfl⟩ : SquareMaximality.Boundary.normalizedWalkPoint v p ∈
        SquareMaximality.Boundary.normalizedPartialSums v)
    simpa only [SquareMaximality.Boundary.normalizedWalkPoint, hx,
      SquareMaximality.Boundary.walkMinX, SquareMaximality.ClosedWalk.spanX,
      v, SquareMaximality.Boundary.normalizedPartialSums] using h

theorem foundation_spanY {ℓ : ℕ} (w : Word ℓ) :
    (normalizedVisited w).sup Prod.snd =
      SquareMaximality.ClosedWalk.spanY (foundationWordEquiv ℓ w) := by
  rw [← foundation_normalizedPartialSums w]
  apply le_antisymm
  · apply Finset.sup_le
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact SquareMaximality.Boundary.normalizedWalkPoint_snd_le_spanY _ hp
  · let v := foundationWordEquiv ℓ w
    have hm := Finset.max'_mem (SquareMaximality.ClosedWalk.visitedY v)
      (SquareMaximality.ClosedWalk.visitedY_nonempty v)
    obtain ⟨p, hp, hy⟩ := Finset.mem_image.mp hm
    have h := Finset.le_sup (f := Prod.snd) (Finset.mem_image.mpr
      ⟨p, hp, rfl⟩ : SquareMaximality.Boundary.normalizedWalkPoint v p ∈
        SquareMaximality.Boundary.normalizedPartialSums v)
    simpa only [SquareMaximality.Boundary.normalizedWalkPoint, hy,
      SquareMaximality.Boundary.walkMinY, SquareMaximality.ClosedWalk.spanY,
      v, SquareMaximality.Boundary.normalizedPartialSums] using h

theorem foundation_fitting {ℓ : ℕ} (w : Word ℓ) (m n : ℕ) (t : Point) :
    t ∈ fittingStarts (faceRectangle m n) (normalizedVisited w) ↔
      t.1 + (SquareMaximality.ClosedWalk.spanX (foundationWordEquiv ℓ w) + 1) ≤ m ∧
      t.2 + (SquareMaximality.ClosedWalk.spanY (foundationWordEquiv ℓ w) + 1) ≤ n := by
  simp only [fittingStarts_faceRectangle, mem_faceRectangle, foundation_spanX, foundation_spanY]
  omega

def foundationStartEquiv : (Σ _x : ℕ, ℕ) ≃ Point where
  toFun z := (z.1, z.2)
  invFun t := ⟨t.1, t.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem foundation_placedPartialSums {ℓ : ℕ} (w : Word ℓ) (t : Point) :
    SquareMaximality.Boundary.placedPartialSums (foundationWordEquiv ℓ w) t.1 t.2 =
      (normalizedVisited w).image (shift t) := by
  simp only [SquareMaximality.Boundary.placedPartialSums, foundation_normalizedPartialSums]
  rfl

theorem foundation_meetingStarts {ℓ m n : ℕ} (w : Word ℓ) {M : Diagram}
    (hM : IsFerrers M) (hU : M ⊆ faceRectangle m n) :
    (SquareMaximality.Boundary.walkMeetingStarts m n M (foundationWordEquiv ℓ w)).image
      foundationStartEquiv =
        hitStarts M (normalizedVisited w) ∩ fittingStarts (faceRectangle m n) (normalizedVisited w) := by
  ext t
  simp only [Finset.mem_image, Finset.mem_inter, mem_hitStarts_iff hM,
    foundation_fitting, SquareMaximality.Boundary.mem_walkMeetingStarts,
    foundation_markedFaces hM hU]
  constructor
  · rintro ⟨z, ⟨hx, hy, q, hq⟩, rfl⟩
    have hq' := Finset.mem_inter.mp hq
    rw [foundation_placedPartialSums w (z.1, z.2)] at hq'
    obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq'.1
    exact ⟨⟨p, hp, hpq.symm ▸ hq'.2⟩, hx, hy⟩
  · rintro ⟨⟨p, hp, htp⟩, hx, hy⟩
    refine ⟨foundationStartEquiv.symm t, ⟨hx, hy, shift t p, ?_⟩, by simp⟩
    apply Finset.mem_inter.mpr
    refine ⟨?_, htp⟩
    change shift t p ∈ SquareMaximality.Boundary.placedPartialSums
      (foundationWordEquiv ℓ w) t.1 t.2
    rw [foundation_placedPartialSums w t]
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

theorem foundation_closedPlacementCount {m n : ℕ} {M : Diagram}
    (hM : IsFerrers M) (hU : M ⊆ faceRectangle m n) (ℓ : ℕ) :
    SquareMaximality.Boundary.closedPlacementCount m n M ℓ =
      ∑ w : ClosedWord ℓ, (hitStarts M (normalizedVisited w.val) ∩
        fittingStarts (faceRectangle m n) (normalizedVisited w.val)).card := by
  unfold SquareMaximality.Boundary.closedPlacementCount
  rw [Finset.sum_subtype _ (fun _ => SquareMaximality.ClosedWalk.mem_closedWords) _]
  rw [← (foundationClosedWordEquiv ℓ).sum_comp]
  apply Finset.sum_congr rfl
  intro w _
  change (SquareMaximality.Boundary.walkMeetingStarts m n M (foundationWordEquiv ℓ w.val)).card = _
  rw [← foundation_meetingStarts w.val hM hU,
    Finset.card_image_of_injective _ foundationStartEquiv.injective]

theorem defect_lost_fit_partition (U M P : Diagram) :
    defectCount M P + lostCount U M P +
      (hitStarts M P ∩ fittingStarts U P).card = M.card := by
  have hh := Finset.card_le_card (hitStarts_subset M P)
  have hp := Finset.card_inter_add_card_sdiff (hitStarts M P) (fittingStarts U P)
  unfold defectCount lostCount lostStarts
  omega

theorem finite_word_partition {m n : ℕ} {M : Diagram}
    (hM : IsFerrers M) (hU : M ⊆ faceRectangle m n) (ℓ : ℕ) :
    defectSum M ℓ + lostSum (faceRectangle m n) M ℓ +
      SquareMaximality.Boundary.closedPlacementCount m n M ℓ =
        M.card * Fintype.card (ClosedWord ℓ) := by
  rw [foundation_closedPlacementCount hM hU]
  unfold defectSum lostSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  simp only [defect_lost_fit_partition, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_comm, Nat.cast_id]

theorem finite_word_energyTerm {m n : ℕ} {M : Diagram}
    (hM : IsFerrers M) (hU : M ⊆ faceRectangle m n) (i : ℕ) :
    realEnergyTerm M i + correctionTerm (faceRectangle m n) M i =
      (M.card : ℝ) * closedWordTerm i -
        SquareMaximality.Boundary.DeterminantSeries.positivePlacementTerm m n M i := by
  have hc : (defectSum M (i + 1) : ℝ) + lostSum (faceRectangle m n) M (i + 1) +
      SquareMaximality.Boundary.closedPlacementCount m n M (i + 1) =
        M.card * Fintype.card (ClosedWord (i + 1)) := by
    exact_mod_cast finite_word_partition hM hU (i + 1)
  unfold realEnergyTerm correctionTerm closedWordTerm
    SquareMaximality.Boundary.DeterminantSeries.positivePlacementTerm
  push_cast
  rw [← add_div, ← mul_div_assoc, ← sub_div]
  congr 1
  linarith

theorem foundation_closedWordCount (ℓ : ℕ) :
    SquareMaximality.ClosedWalk.closedWordCount ℓ = Fintype.card (ClosedWord ℓ) := by
  have hc := Fintype.subtype_card (SquareMaximality.ClosedWalk.closedWords ℓ)
    (fun _ => SquareMaximality.ClosedWalk.mem_closedWords)
  calc
    SquareMaximality.ClosedWalk.closedWordCount ℓ =
        Fintype.card {w : SquareMaximality.ClosedWalk.Word ℓ //
          SquareMaximality.ClosedWalk.IsClosed w} := hc.symm
    _ = Fintype.card (ClosedWord ℓ) := (Fintype.card_congr (foundationClosedWordEquiv ℓ)).symm

theorem closedWordTerm_foundation_odd (i : ℕ) :
    closedWordTerm (2 * i + 1) = SquareMaximality.Boundary.evenClosedWordTerm i := by
  unfold closedWordTerm SquareMaximality.Boundary.evenClosedWordTerm
  rw [foundation_closedWordCount]
  rw [show 2 * i + 1 + 1 = 2 * (i + 1) by omega]
  push_cast
  congr 1
  ring

/-- The entropy normalization for this project's own `Fin 4` closed words. -/
theorem closedWordTerm_hasSum :
    HasSum closedWordTerm (Real.log 4 - SquareMaximality.squareLatticeEntropy) := by
  have heven : HasSum (fun i => closedWordTerm (2 * i)) (0 : ℝ) := by simp
  have hodd : HasSum (fun i => closedWordTerm (2 * i + 1))
      (Real.log 4 - SquareMaximality.squareLatticeEntropy) := by
    simpa only [closedWordTerm_foundation_odd] using
      SquareMaximality.ClosedWalk.hasSum_evenClosedWordTerm
  simpa only [zero_add] using heven.even_add_odd hodd

/-- The concrete corner word energy is the finite Dirichlet determinant ratio
minus the bulk entropy. No determinant expansion remains as a hypothesis. -/
theorem finiteWordEnergy_logdet {m n : ℕ} {M : Diagram}
    (hM : IsFerrers M) (hU : M ⊆ faceRectangle m n) :
    finiteWordEnergy (faceRectangle m n) M =
      Real.log (Matrix.det (SquareMaximality.Boundary.fourIminusAdjacency (faceRectangle m n))) -
        Real.log (Matrix.det (SquareMaximality.Boundary.fourIminusAdjacency (faceRectangle m n \ M))) -
          SquareMaximality.squareLatticeEntropy * M.card := by
  have hplace := SquareMaximality.Boundary.DeterminantSeries.hasSum_positivePlacementTerm m n M
    (SquareMaximality.Boundary.SpectralBound.faceIndices_spectralBound m n)
    (SquareMaximality.Boundary.SpectralBound.unmarkedFaces_spectralBound m n M)
  have hlog1 := congrArg (fun U : Diagram => Real.log
    (Matrix.det (SquareMaximality.Boundary.fourIminusAdjacency U))) (foundation_faceIndices m n)
  have hu : SquareMaximality.Boundary.unmarkedFaces m n M = faceRectangle m n \ M := by
    unfold SquareMaximality.Boundary.unmarkedFaces
    rw [foundation_markedFaces hM hU, foundation_faceIndices]
  have hlog2 := congrArg (fun U : Diagram => Real.log
    (Matrix.det (SquareMaximality.Boundary.fourIminusAdjacency U))) hu
  rw [hlog1, hlog2, foundation_markedFaces hM hU] at hplace
  have hseries := (closedWordTerm_hasSum.mul_left (M.card : ℝ)).sub hplace
  have hsum := (realEnergy_hasSum M).add (correctionTerm_summable (faceRectangle m n) M).hasSum
  have hid := HasSum.congr_fun hsum (fun i => (finite_word_energyTerm hM hU i).symm)
  have h := HasSum.unique hid hseries
  unfold finiteWordEnergy correction
  linarith

/-- Strict spectral control gives positivity for every finite induced face matrix. -/
theorem dirichlet_posDef {m n : ℕ} {U : Diagram} (hU : U ⊆ faceRectangle m n) :
    (SquareMaximality.Boundary.fourIminusAdjacency U).PosDef := by
  classical
  let A := (SquareMaximality.Boundary.faceGraph U).adjMatrix ℝ
  let hA := (SquareMaximality.Boundary.faceGraph U).isHermitian_adjMatrix ℝ
  have hs := SquareMaximality.Boundary.SpectralBound.faceAdjacencySpectralBound_of_subset
    (R := m) (S := n) (foundation_faceIndices m n ▸ hU)
  have hdiag : (Matrix.diagonal (fun i => 4 - hA.eigenvalues i)).PosDef :=
    Matrix.posDef_diagonal_iff.mpr (fun i => by have := (abs_lt.mp (hs i)).2; linarith)
  have hdeq : Matrix.diagonal (fun i => 4 - hA.eigenvalues i) =
      (4 : ℝ) • (1 : Matrix {z // z ∈ U} {z // z ∈ U} ℝ) -
        Matrix.diagonal hA.eigenvalues := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hspec : A = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (Matrix.diagonal hA.eigenvalues) := by
    simpa [A, Function.comp_def] using hA.spectral_theorem
  have heq : SquareMaximality.Boundary.fourIminusAdjacency U =
      Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (Matrix.diagonal (fun i => 4 - hA.eigenvalues i)) := by
    rw [hdeq, map_sub, map_smul, map_one, ← hspec]
    rfl
  rw [heq, Unitary.conjStarAlgAut_apply]
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff Unitary.isUnit_coe).mpr hdiag

/-- Reindexing by unremoved cells followed by removed cells. -/
def faceSplitEquiv {U M : Diagram} (hM : M ⊆ U) :
    {p // p ∈ U \ M} ⊕ {p // p ∈ M} ≃ {p // p ∈ U} where
  toFun
    | Sum.inl p => ⟨p.val, (Finset.mem_sdiff.mp p.property).1⟩
    | Sum.inr p => ⟨p.val, hM p.property⟩
  invFun p := if h : p.val ∈ M then Sum.inr ⟨p.val, h⟩
    else Sum.inl ⟨p.val, Finset.mem_sdiff.mpr ⟨p.property, h⟩⟩
  left_inv p := by
    cases p with
    | inl p => simp [(Finset.mem_sdiff.mp p.property).2]
    | inr p => simp [p.property]
  right_inv p := by dsimp; split_ifs <;> rfl

/-- The actual principal minor of the finite Green matrix. -/
noncomputable def greenMinor {U M : Diagram} (hM : M ⊆ U) :
    Matrix {p // p ∈ M} {p // p ∈ M} ℝ :=
  (SquareMaximality.Boundary.fourIminusAdjacency U)⁻¹.submatrix
    (fun p => ⟨p.val, hM p.property⟩) (fun p => ⟨p.val, hM p.property⟩)

theorem dirichlet_block_remaining {U M : Diagram} (hM : M ⊆ U) :
    ((SquareMaximality.Boundary.fourIminusAdjacency U).submatrix
      (faceSplitEquiv hM) (faceSplitEquiv hM)).toBlocks₁₁ =
        SquareMaximality.Boundary.fourIminusAdjacency (U \ M) := by
  classical
  ext i j
  simp only [Matrix.toBlocks₁₁, Matrix.submatrix_apply,
    SquareMaximality.Boundary.fourIminusAdjacency_apply, faceSplitEquiv,
    Equiv.coe_fn_mk, Subtype.ext_iff, Matrix.of_apply]

theorem dirichlet_inverse_block_removed {U M : Diagram} (hM : M ⊆ U) :
    (((SquareMaximality.Boundary.fourIminusAdjacency U).submatrix
      (faceSplitEquiv hM) (faceSplitEquiv hM))⁻¹).toBlocks₂₂ = greenMinor hM := by
  rw [Matrix.inv_submatrix_equiv]
  rfl

theorem greenMinor_det_identity {m n : ℕ} {U M : Diagram}
    (hU : U ⊆ faceRectangle m n) (hM : M ⊆ U) :
    Matrix.det (SquareMaximality.Boundary.fourIminusAdjacency (U \ M)) =
      Matrix.det (SquareMaximality.Boundary.fourIminusAdjacency U) * Matrix.det (greenMinor hM) := by
  have hp := (dirichlet_posDef hU).submatrix (faceSplitEquiv hM).injective
  have h := SquareMaximality.Multigraph.LabeledMultigraph.det_toBlocks₁₁_eq_det_mul_det_inv_toBlocks₂₂
    ((SquareMaximality.Boundary.fourIminusAdjacency U).submatrix
      (faceSplitEquiv hM) (faceSplitEquiv hM)) hp
  rw [dirichlet_block_remaining, dirichlet_inverse_block_removed,
    Matrix.det_submatrix_equiv_self] at h
  exact h

theorem greenMinor_det_pos {m n : ℕ} {U M : Diagram}
    (hU : U ⊆ faceRectangle m n) (hM : M ⊆ U) :
    0 < Matrix.det (greenMinor hM) := by
  have hfull := (dirichlet_posDef hU).det_pos
  have hremaining := (dirichlet_posDef (U := U \ M) (Finset.Subset.trans Finset.sdiff_subset hU)).det_pos
  have h := greenMinor_det_identity hU hM
  nlinarith

/-- The finite Green-minor identity from Section 4, now for the concrete
closed-word energy with all analytic and combinatorial inputs discharged. -/
theorem finiteWordEnergy_greenMinor {m n : ℕ} {M : Diagram}
    (hM : IsFerrers M) (hU : M ⊆ faceRectangle m n) :
    finiteWordEnergy (faceRectangle m n) M =
      -Real.log (Matrix.det (greenMinor hU)) -
        SquareMaximality.squareLatticeEntropy * M.card := by
  have hid := greenMinor_det_identity (Finset.Subset.refl (faceRectangle m n)) hU
  have hlog := congrArg Real.log hid
  rw [Real.log_mul
    (ne_of_gt (dirichlet_posDef (Finset.Subset.refl (faceRectangle m n))).det_pos)
    (ne_of_gt (greenMinor_det_pos (Finset.Subset.refl (faceRectangle m n)) hU))] at hlog
  rw [finiteWordEnergy_logdet hM hU]
  linarith

/-- Actual finite Dirichlet defect energy, expressed using the Green minor. -/
noncomputable def dirichletEnergy {U M : Diagram} (hU : M ⊆ U) : ℝ :=
  -Real.log (Matrix.det (greenMinor hU)) - SquareMaximality.squareLatticeEntropy * M.card

theorem dirichletEnergy_eq {m n : ℕ} {M : Diagram}
    (hM : IsFerrers M) (hU : M ⊆ faceRectangle m n) :
    dirichletEnergy hU = realEnergy M + correction (faceRectangle m n) M :=
  (finiteWordEnergy_greenMinor hM hU).symm

/-- The nested-ideal transfer inequality is now about actual Green determinants. -/
theorem dirichletEnergy_transfer {m n : ℕ} {A B : Diagram}
    (hA : IsFerrers A) (hB : IsFerrers B) (hAB : A ⊆ B) (hBU : B ⊆ faceRectangle m n) :
    realEnergy B - realEnergy A +
        ∑ t ∈ B \ A, correction (faceRectangle (m - t.1) (n - t.2)) {(0, 0)} ≤
      dirichletEnergy hBU - dirichletEnergy (Finset.Subset.trans hAB hBU) := by
  rw [dirichletEnergy_eq hB hBU, dirichletEnergy_eq hA (Finset.Subset.trans hAB hBU)]
  exact finiteWordEnergy_transfer m n hAB

end SpanningTreeIsoperimetry.CornerEnergy




