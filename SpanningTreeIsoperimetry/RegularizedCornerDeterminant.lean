import SpanningTreeIsoperimetry.RegularizedQuadrantGreen
import SpanningTreeIsoperimetry.StripSpectralRegularization
import SpanningTreeIsoperimetry.CornerLimit

/-! Regularized corner determinants with the bulk constant defined by the
actual closed-loop series. Its identification with the zero symbol coefficient
is a separate analytic statement and is not assumed here. -/
namespace SpanningTreeIsoperimetry.RegularizedCornerDeterminant
open Ferrers CornerEnergy RegularizedGreenSeries StripSpectralRegularization
open SquareMaximality.Boundary SquareMaximality.Boundary.DeterminantSeries
open scoped BigOperators Matrix Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def weight (z : ℝ) (n : ℕ) : ℝ := (4/z)^(n+1)
def bulkTerm (z : ℝ) (n : ℕ) : ℝ := weight z n*closedWordTerm n
def bulkEntropy (z : ℝ) : ℝ := Real.log z-∑' n,bulkTerm z n
def correctionTermZ (z : ℝ) (U M : Diagram) (n : ℕ) : ℝ :=
  weight z n*correctionTerm U M n
def correctionZ (z : ℝ) (U M : Diagram) : ℝ := ∑' n,correctionTermZ z U M n

theorem weight_bounds {z : ℝ} (hz : 4≤z) (n : ℕ) : 0≤weight z n ∧ weight z n≤1 := by
  have hz0 : 0<z := by linarith
  exact ⟨pow_nonneg (by positivity) _,pow_le_one₀ (by positivity) ((div_le_one hz0).mpr hz)⟩

theorem bulkTerm_summable {z : ℝ} (hz : 4≤z) : Summable (bulkTerm z) := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (weight_bounds hz n).1 (closedWordTerm_nonneg n))
    (fun n => mul_le_of_le_one_left (closedWordTerm_nonneg n) (weight_bounds hz n).2)
    closedWordTerm_summable

theorem bulkTerm_eq {z : ℝ} (hz : 4≤z) (n : ℕ) :
    bulkTerm z n=(Fintype.card (ClosedWord (n+1)) : ℝ)/(((n : ℝ)+1)*z^(n+1)) := by
  have hz0 : z≠0 := by linarith
  unfold bulkTerm weight closedWordTerm
  rw [div_pow]
  push_cast
  field_simp
  <;> ring

theorem bulkEntropy_four : bulkEntropy 4=SquareMaximality.squareLatticeEntropy := by
  have h := closedWordTerm_hasSum.tsum_eq
  simp only [bulkEntropy,bulkTerm,weight,div_self (by norm_num : (4 : ℝ)≠0),one_pow,one_mul]
  rw [h]
  ring

theorem correctionTermZ_nonneg {z : ℝ} (hz : 4≤z) (U M : Diagram) (n : ℕ) :
    0≤correctionTermZ z U M n :=
  mul_nonneg (weight_bounds hz n).1 (correctionTerm_nonneg U M n)

theorem correctionTermZ_le {z : ℝ} (hz : 4≤z) (U M : Diagram) (n : ℕ) :
    correctionTermZ z U M n≤correctionTerm U M n :=
  mul_le_of_le_one_left (correctionTerm_nonneg U M n) (weight_bounds hz n).2

theorem correctionTermZ_summable {z : ℝ} (hz : 4≤z) (U M : Diagram) :
    Summable (correctionTermZ z U M) :=
  Summable.of_nonneg_of_le (correctionTermZ_nonneg hz U M)
    (correctionTermZ_le hz U M) (correctionTerm_summable U M)

theorem correctionZ_nonneg {z : ℝ} (hz : 4≤z) (U M : Diagram) : 0≤correctionZ z U M :=
  tsum_nonneg (correctionTermZ_nonneg hz U M)

theorem correctionZ_le {z : ℝ} (hz : 4≤z) (U M : Diagram) : correctionZ z U M≤correction U M :=
  (correctionTermZ_summable hz U M).tsum_le_tsum (correctionTermZ_le hz U M)
    (correctionTerm_summable U M)

theorem traceTerm_eq_weight {z : ℝ} (hz : 4≤z) (U : Diagram) (n : ℕ) :
    DeterminantComparison.traceTerm z ((faceGraph U).adjMatrix ℝ) n=
      weight z n*faceTraceTerm U n := by
  have hz0 : z≠0 := by linarith
  unfold DeterminantComparison.traceTerm weight faceTraceTerm matrixTraceTerm
  rw [div_pow]
  push_cast
  field_simp
  <;> ring

theorem faceTrace_hasSum {z : ℝ} (hz : 4≤z) {m n : ℕ} {U : Diagram}
    (hU : U⊆faceRectangle m n) :
    HasSum (fun i => weight z i*faceTraceTerm U i)
      ((U.card : ℝ)*Real.log z-Real.log (dirichletZ z U).det) := by
  have hs := SpectralBound.faceAdjacencySpectralBound_of_subset ((foundation_faceIndices m n).symm ▸ hU)
  have h := DeterminantComparison.logdet_hasSum ((faceGraph U).isHermitian_adjMatrix ℝ)
    (by linarith : 0<z) (fun i => (hs i).trans_le hz)
  simp only [Fintype.card_coe] at h
  exact h.congr_fun (fun i => (traceTerm_eq_weight hz U i).symm)

theorem placement_hasSum {z : ℝ} (hz : 4≤z) {m n : ℕ} {M : Diagram}
    (hM : IsFerrers M) (hU : M⊆faceRectangle m n) :
    HasSum (fun i => weight z i*positivePlacementTerm m n M i)
      ((M.card : ℝ)*Real.log z-
        (Real.log (dirichletZ z (faceRectangle m n)).det-
          Real.log (dirichletZ z (faceRectangle m n\M)).det)) := by
  have hu : unmarkedFaces m n M=faceRectangle m n\M := by
    unfold unmarkedFaces
    rw [foundation_markedFaces hM hU,foundation_faceIndices]
  have hc (i : ℕ) : weight z i*positivePlacementTerm m n M i=
      weight z i*faceTraceTerm (faceRectangle m n) i-
        weight z i*faceTraceTerm (faceRectangle m n\M) i := by
    rw [← faceTraceTerm_sub_eq_positivePlacementTerm,foundation_faceIndices,hu,mul_sub]
  have h := (faceTrace_hasSum hz (Finset.Subset.refl (faceRectangle m n))).sub
    (faceTrace_hasSum hz (Finset.sdiff_subset : faceRectangle m n\M⊆faceRectangle m n))
  have h' := h.congr_fun hc
  convert h' using 1
  have hcard : ((faceRectangle m n\M).card : ℝ)+(M.card : ℝ)=(faceRectangle m n).card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hU
  have hcardlog := congrArg (fun x : ℝ => x*Real.log z) hcard
  nlinarith

/-- The actual regularized word energy plus the actual lost-placement
correction equals the finite Dirichlet log determinant ratio. -/
theorem spectralEnergy_add_correctionZ_logdet {z : ℝ} (hz : 4≤z) {m n : ℕ} {M : Diagram}
    (hM : IsFerrers M) (hU : M⊆faceRectangle m n) :
    spectralEnergy M z+correctionZ z (faceRectangle m n) M=
      Real.log (dirichletZ z (faceRectangle m n)).det-
        Real.log (dirichletZ z (faceRectangle m n\M)).det-bulkEntropy z*M.card := by
  have hc (i : ℕ) : term M z i+correctionTermZ z (faceRectangle m n) M i=
      (M.card : ℝ)*bulkTerm z i-weight z i*positivePlacementTerm m n M i := by
    unfold term correctionTermZ bulkTerm weight
    rw [← mul_add,finite_word_energyTerm hM hU]
    ring
  have hsum := (term_summable M hz).hasSum.add (correctionTermZ_summable hz (faceRectangle m n) M).hasSum
  have hleft := hsum.congr_fun (fun i => (hc i).symm)
  have hright := ((bulkTerm_summable hz).hasSum.mul_left (M.card : ℝ)).sub (placement_hasSum hz hM hU)
  have heq := hleft.unique hright
  change (∑' i,term M z i)+(∑' i,correctionTermZ z (faceRectangle m n) M i)=_
  unfold bulkEntropy
  linarith

theorem dirichletZ_posDef {z : ℝ} (hz : 4≤z) {m n : ℕ} {U : Diagram}
    (hU : U⊆faceRectangle m n) : (dirichletZ z U).PosDef := by
  let A := (faceGraph U).adjMatrix ℝ
  let hA := (faceGraph U).isHermitian_adjMatrix ℝ
  have hs := SpectralBound.faceAdjacencySpectralBound_of_subset ((foundation_faceIndices m n).symm ▸ hU)
  have hdiag : (Matrix.diagonal (fun i => z-hA.eigenvalues i)).PosDef :=
    Matrix.posDef_diagonal_iff.mpr (fun i => by have := (abs_lt.mp (hs i)).2; linarith)
  have hdeq : Matrix.diagonal (fun i => z-hA.eigenvalues i)=
      z • (1 : Matrix {p // p∈U} {p // p∈U} ℝ)-Matrix.diagonal hA.eigenvalues := by
    ext i j
    by_cases hij : i=j <;> simp [hij]
  have hspec : A=Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary (Matrix.diagonal hA.eigenvalues) := by
    simpa [A,Function.comp_def] using hA.spectral_theorem
  have heq : dirichletZ z U=Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (Matrix.diagonal (fun i => z-hA.eigenvalues i)) := by
    rw [hdeq,map_sub,map_smul,map_one,← hspec]
    rfl
  rw [heq,Unitary.conjStarAlgAut_apply]
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff Unitary.isUnit_coe).mpr hdiag

def greenMinorZ (z : ℝ) {U M : Diagram} (hM : M⊆U) : Matrix {p // p∈M} {p // p∈M} ℝ :=
  (dirichletZ z U)⁻¹.submatrix (fun p => ⟨p.val,hM p.property⟩) (fun p => ⟨p.val,hM p.property⟩)

theorem dirichletZ_block_remaining (z : ℝ) {U M : Diagram} (hM : M⊆U) :
    ((dirichletZ z U).submatrix (faceSplitEquiv hM) (faceSplitEquiv hM)).toBlocks₁₁=
      dirichletZ z (U\M) := by
  rw [RegularizedQuadrantGreen.dirichletZ_eq,RegularizedQuadrantGreen.dirichletZ_eq]
  ext i j
  have h4 := congrArg (fun A => A i j) (dirichlet_block_remaining hM)
  simp only [Matrix.toBlocks₁₁,Matrix.submatrix_apply,Matrix.add_apply,
    Matrix.smul_apply,smul_eq_mul,Matrix.of_apply] at h4 ⊢
  have hone : (1 : Matrix {p // p∈U} {p // p∈U} ℝ)
      ((faceSplitEquiv hM) (Sum.inl i)) ((faceSplitEquiv hM) (Sum.inl j))=
      (1 : Matrix {p // p∈U\M} {p // p∈U\M} ℝ) i j := by
    by_cases hij : i=j
    · subst j
      simp only [Matrix.one_apply,ite_true]
    · have hne : (faceSplitEquiv hM) (Sum.inl i)≠(faceSplitEquiv hM) (Sum.inl j) :=
        fun h => hij (Sum.inl.inj ((faceSplitEquiv hM).injective h))
      simp only [Matrix.one_apply,if_neg hij,if_neg hne]
  rw [h4,hone]

theorem greenMinorZ_det_identity {z : ℝ} (hz : 4≤z) {m n : ℕ} {U M : Diagram}
    (hU : U⊆faceRectangle m n) (hM : M⊆U) :
    (dirichletZ z (U\M)).det=(dirichletZ z U).det*(greenMinorZ z hM).det := by
  have hp := (dirichletZ_posDef hz hU).submatrix (faceSplitEquiv hM).injective
  have h := SquareMaximality.Multigraph.LabeledMultigraph.det_toBlocks₁₁_eq_det_mul_det_inv_toBlocks₂₂
    ((dirichletZ z U).submatrix (faceSplitEquiv hM) (faceSplitEquiv hM)) hp
  rw [dirichletZ_block_remaining,Matrix.inv_submatrix_equiv,Matrix.det_submatrix_equiv_self] at h
  exact h

theorem greenMinorZ_det_pos {z : ℝ} (hz : 4≤z) {m n : ℕ} {U M : Diagram}
    (hU : U⊆faceRectangle m n) (hM : M⊆U) : 0<(greenMinorZ z hM).det := by
  have hf := dirichletZ_det_pos hz hU
  have hr := dirichletZ_det_pos hz (Finset.Subset.trans Finset.sdiff_subset hU : U\M⊆faceRectangle m n)
  have h := greenMinorZ_det_identity hz hU hM
  nlinarith

/-- Finite regularized energy normalization for the actual inverse minor. -/
theorem spectralEnergy_add_correctionZ_greenMinor {z : ℝ} (hz : 4≤z) {m n : ℕ} {M : Diagram}
    (hM : IsFerrers M) (hU : M⊆faceRectangle m n) :
    spectralEnergy M z+correctionZ z (faceRectangle m n) M=
      -Real.log (greenMinorZ z hU).det-bulkEntropy z*M.card := by
  have hid := greenMinorZ_det_identity hz (Finset.Subset.refl (faceRectangle m n)) hU
  have hlog := congrArg Real.log hid
  rw [Real.log_mul (dirichletZ_det_pos hz (Finset.Subset.refl (faceRectangle m n))).ne'
    (greenMinorZ_det_pos hz (Finset.Subset.refl (faceRectangle m n)) hU).ne'] at hlog
  rw [spectralEnergy_add_correctionZ_logdet hz hM hU]
  linarith

end
end SpanningTreeIsoperimetry.RegularizedCornerDeterminant
