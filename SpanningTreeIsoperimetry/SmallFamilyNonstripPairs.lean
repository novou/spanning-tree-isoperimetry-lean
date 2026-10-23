module

public import SpanningTreeIsoperimetry.SmallFamilyPatternData

@[expose] public section

set_option backward.privateInPublic true

/-! Two-corner source bounds when at least the larger corner is not a strip.
Only the corner square requires a separate finite-correction estimate. -/
namespace SpanningTreeIsoperimetry.SmallFamilyNonstripPairs
open Ferrers CornerEnergy CornerPrimalDomains SmallFamilySourceBounds SmallFamilyPatternData
open SmallFamilyStripCorrections SmallCornerCorrections StripRigidity
open SmallFamilyProfiles SmallFamilyMonotonicity MulticornerEndpointChecks
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 1500000

private theorem ell_floor : (3357 : ℝ)/50000<realEnergy threeCell := by
  have he : RefinedObstructionPolynomials.ell.diagram=threeCell := by decide +kernel
  simpa only [he] using RefinedObstructionEnergy.ell.energy_lower

private theorem singleton_square_pair {r : ℕ} {A : Diagram} {c d : Corner}
    (hcd : c≠d) (hr : 5≤r) (hA : IsFerrers A) (hcard : A.card=1) :
    stripFloor 1+(2837 : ℝ)/50000+(112/5)*weight r 0≤
      sourceEnergy r r (twoCornerFamily c d A (faceRectangle 2 2)) := by
  have hEA := diagramFloor_le hA (show A.card≤6 by omega)
  rw [hcard] at hEA
  have hEB := RefinedObstructionEnergy.square.energy_lower
  change (2837 : ℝ)/50000<realEnergy (faceRectangle 2 2) at hEB
  have hAc := diagramEnergy_ge_cells r r A
  rw [hcard] at hAc
  norm_num at hAc
  have hS := single_square_weight (by omega : 2≤r)
  have hSq := square_weight hr (by omega : 3≤r)
  rw [sourceEnergy_pair r r hcd]
  change _≤diagramEnergy r r A+(realEnergy (faceRectangle 2 2)+square r r)
  linarith only [hEA,hEB,hAc,hS,hSq]

theorem nonstrip_pair_rows {r a p q : ℕ} {A B : Diagram} {c d : Corner}
    (hcd : c≠d) (hA : IsFerrers A) (hB : IsFerrers B) (hn : ¬IsStraightStrip B)
    (hAp : A.card=p) (hBq : B.card=q) (hp : 1≤p) (hpq : p≤q)
    (hsize : p+q<r) (hsupport : Supported a (p+q)) :
    RowBound r a (p+q) (twoCornerFamily c d A B) := by
  have hk6 : p+q≤6 := by rcases hsupport with h|h|h <;> omega
  have hq3 : 3≤q := by have h := nonstrip_card_ge_three hB hn; omega
  have hq5 : q≤5 := by omega
  have hQA := diagramFloor_le hA (show A.card≤6 by omega)
  rw [hAp] at hQA
  have hQB := RefinedCornerEnvelope.single_nonstrip_bound hB (show 2≤B.card by omega) hn
  rw [hBq] at hQB
  have hcell := sourceEnergy_pair_cells r (r+a) hcd A B
  rw [hAp,hBq] at hcell
  have hbare : realEnergy A+realEnergy B≤sourceEnergy r (r+a) (twoCornerFamily c d A B) := by
    rw [sourceEnergy_pair r (r+a) hcd]
    exact add_le_add (diagramEnergy_ge_quadrant r (r+a) A) (diagramEnergy_ge_quadrant r (r+a) B)
  have hw := weight_nonneg r 0
  rcases hsupport with ⟨rfl,hk2,hk6⟩|⟨rfl,hk2,hk5⟩|⟨rfl,hk3,hk5⟩
  · have hS := single_square_weight (by omega : 2≤r)
    have hcases : (p=1 ∧ q=3) ∨ (p=1 ∧ q=4) ∨ (p=1 ∧ q=5) ∨ (p=2 ∧ q=3) ∨ (p=2 ∧ q=4) ∨ (p=3 ∧ q=3) := by omega
    rcases hcases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · refine ⟨7,by norm_num [Matches,gap,rowDeficit],?_⟩
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor,RefinedCornerEnvelope.bound] at hQA hQB hcell ⊢
      nlinarith only [hQA,hQB,hcell,hS,hw]
    · by_cases heq : B=faceRectangle 2 2
      · subst B
        refine ⟨12,by norm_num [Matches,gap,rowDeficit],?_⟩
        have h := singleton_square_pair hcd (by omega : 5≤r) hA hAp
        rw [rowLower,weightedLoss_four]
        norm_num [quadrantFloor,coeff,stripFloor] at h ⊢
        linarith only [h]
      · have hell : realEnergy threeCell≤realEnergy B := by
          rcases small_nonstrip_square_or_ell hB (show B.card≤5 by omega) hn with he|he
          · exact False.elim (heq he)
          · exact he
        refine ⟨13,by norm_num [Matches,gap,rowDeficit],?_⟩
        rw [rowLower,weightedLoss_four]
        norm_num [quadrantFloor,coeff,stripFloor] at hQA hcell ⊢
        nlinarith only [hQA,hell,ell_floor,hcell,hS,hw]
    · refine ⟨19,by norm_num [Matches,gap,rowDeficit],?_⟩
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor,RefinedCornerEnvelope.bound] at hQA hQB hcell ⊢
      nlinarith only [hQA,hQB,hcell,hS,hw]
    · refine ⟨13,by norm_num [Matches,gap,rowDeficit],?_⟩
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor,RefinedCornerEnvelope.bound] at hQA hQB hcell ⊢
      nlinarith only [hQA,hQB,hcell,hS,hw]
    · refine ⟨19,by norm_num [Matches,gap,rowDeficit],?_⟩
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor,RefinedCornerEnvelope.bound] at hQA hQB hcell ⊢
      nlinarith only [hQA,hQB,hcell,hS,hw]
    · refine ⟨19,by norm_num [Matches,gap,rowDeficit],?_⟩
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor,RefinedCornerEnvelope.bound] at hQA hQB hcell ⊢
      nlinarith only [hQA,hQB,hcell,hS,hw]
  · have hS := single_ordered_weight (by omega : 2≤r) (by omega : r≤r+1)
    have hcases : (p=1 ∧ q=3) ∨ (p=1 ∧ q=4) ∨ (p=2 ∧ q=3) := by omega
    rcases hcases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · refine ⟨9,by norm_num [Matches,gap,rowDeficit],?_⟩
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor,RefinedCornerEnvelope.bound] at hQA hQB hcell ⊢
      nlinarith only [hQA,hQB,hcell,hS,hw]
    · refine ⟨15,by norm_num [Matches,gap,rowDeficit],?_⟩
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor,RefinedCornerEnvelope.bound] at hQA hQB hcell ⊢
      nlinarith only [hQA,hQB,hcell,hS,hw]
    · refine ⟨15,by norm_num [Matches,gap,rowDeficit],?_⟩
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor,RefinedCornerEnvelope.bound] at hQA hQB hcell ⊢
      nlinarith only [hQA,hQB,hcell,hS,hw]
  · have hS := single_ordered_weight (by omega : 2≤r) (by omega : r≤r+2)
    have hcases : (p=1 ∧ q=3) ∨ (p=1 ∧ q=4) ∨ (p=2 ∧ q=3) := by omega
    rcases hcases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · refine ⟨10,by norm_num [Matches,gap,rowDeficit],?_⟩
      have hW := weight_le_at (by decide : 0<5) (show 5≤r by omega)
      norm_num [weight] at hW
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor,RefinedCornerEnvelope.bound,weight] at hQA hQB ⊢
      nlinarith only [hQA,hQB,hbare,hW]
    · refine ⟨16,by norm_num [Matches,gap,rowDeficit],?_⟩
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor,RefinedCornerEnvelope.bound] at hQA hQB hcell ⊢
      nlinarith only [hQA,hQB,hcell,hS,hw]
    · refine ⟨16,by norm_num [Matches,gap,rowDeficit],?_⟩
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor,RefinedCornerEnvelope.bound] at hQA hQB hcell ⊢
      nlinarith only [hQA,hQB,hcell,hS,hw]

end
end SpanningTreeIsoperimetry.SmallFamilyNonstripPairs
