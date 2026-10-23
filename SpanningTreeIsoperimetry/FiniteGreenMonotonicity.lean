module

public import SpanningTreeIsoperimetry.CornerDeterminant

@[expose] public section

/-! Enlargement of the actual finite face domain decreases the lost-walk
correction and increases every containing Ferrers Green-minor determinant. -/
namespace SpanningTreeIsoperimetry.FiniteGreenMonotonicity
open Ferrers CornerEnergy
open scoped Classical

theorem fittingStarts_mono_ambient {U V P : Diagram} (hUV : U⊆V) :
    fittingStarts U P ⊆ fittingStarts V P := by
  intro t ht
  obtain ⟨htU,hfit⟩:=mem_fittingStarts.mp ht
  exact mem_fittingStarts.mpr ⟨hUV htU,fun p hp => hUV (hfit p hp)⟩

theorem lostCount_antitone_ambient {U V M P : Diagram} (hUV : U⊆V) :
    lostCount V M P≤lostCount U M P := by
  apply Finset.card_le_card
  exact Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (fittingStarts_mono_ambient hUV)

theorem correctionTerm_antitone_ambient {U V M : Diagram} (hUV : U⊆V) (n : ℕ) :
    correctionTerm V M n≤correctionTerm U M n := by
  have hs : lostSum V M (n+1)≤lostSum U M (n+1) := by
    unfold lostSum
    exact Finset.sum_le_sum (fun (w : ClosedWord (n+1)) _ =>
      lostCount_antitone_ambient (M := M) (P := normalizedVisited w.val) hUV)
  unfold correctionTerm
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast hs

theorem correction_antitone_ambient {U V M : Diagram} (hUV : U⊆V) :
    correction V M≤correction U M :=
  (correctionTerm_summable V M).tsum_le_tsum
    (correctionTerm_antitone_ambient hUV) (correctionTerm_summable U M)

theorem rectangle_subset {R S T W : ℕ} (hR : R≤T) (hS : S≤W) :
    faceRectangle R S⊆faceRectangle T W := by
  intro p hp
  rw [mem_faceRectangle] at hp ⊢
  omega

theorem dirichletEnergy_antitone {R S T W : ℕ} {M : Diagram} (hM : IsFerrers M)
    (hU : M⊆faceRectangle R S) (hV : M⊆faceRectangle T W) (hR : R≤T) (hS : S≤W) :
    dirichletEnergy hV≤dirichletEnergy hU := by
  rw [dirichletEnergy_eq hM,dirichletEnergy_eq hM]
  have h:=correction_antitone_ambient (M := M) (rectangle_subset hR hS)
  linarith

theorem greenMinor_det_monotone {R S T W : ℕ} {M : Diagram} (hM : IsFerrers M)
    (hU : M⊆faceRectangle R S) (hV : M⊆faceRectangle T W) (hR : R≤T) (hS : S≤W) :
    Matrix.det (greenMinor hU)≤Matrix.det (greenMinor hV) := by
  have hpU:=greenMinor_det_pos (Finset.Subset.refl (faceRectangle R S)) hU
  have hpV:=greenMinor_det_pos (Finset.Subset.refl (faceRectangle T W)) hV
  apply (Real.log_le_log_iff hpU hpV).mp
  have h:=dirichletEnergy_antitone hM hU hV hR hS
  unfold dirichletEnergy at h
  linarith

end SpanningTreeIsoperimetry.FiniteGreenMonotonicity
