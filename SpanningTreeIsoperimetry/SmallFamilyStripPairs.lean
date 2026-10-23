module

public import SpanningTreeIsoperimetry.SmallFamilyFoldable

@[expose] public section

/-! Every pair of straight corner strips in the small table either folds
strictly or satisfies the matching finite source-energy lower bound. -/
namespace SpanningTreeIsoperimetry.SmallFamilyStripPairs
open Ferrers CornerEnergy CornerPrimalDomains SmallFamilySourceBounds SmallFamilyPatternData
open SmallFamilyStripCorrections SmallCornerCorrections SmallFamilyFoldable StripRigidity
open SmallFamilyProfiles SmallFamilyMonotonicity MulticornerEndpointChecks
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 1500000

theorem strip_pair_rows {r a p q : ℕ} {A B : Diagram} {c d : Corner}
    (hcd : c≠d) (hA : IsStraightStrip A) (hB : IsStraightStrip B)
    (hAp : A.card=p) (hBq : B.card=q) (hp : 1≤p) (hpq : p≤q)
    (hsize : p+q<r) (harea : 18+(p+q)≤r*(r+a)) (hsupport : Supported a (p+q)) :
    Foldable a (twoCornerFamily c d A B) ∨ RowBound r a (p+q) (twoCornerFamily c d A B) := by
  by_cases hfold : p=a+2 ∨ q=a+2
  · left
    apply pair_foldable hcd hA hB (by omega) (by omega)
    simpa only [hAp,hBq] using hfold
  · right
    have hk6 : p+q≤6 := by rcases hsupport with h|h|h <;> omega
    have hsource := straight_pair_lower hcd (by omega : 2≤r) (by omega : r≤r+a) hA hB
      (by omega : A.card<r) (by omega : B.card<r)
    rw [hAp,hBq] at hsource
    have hP := stripFloor_le (show p≤6 by omega)
    have hQ := stripFloor_le (show q≤6 by omega)
    have hlow : stripFloor p+stripFloor q+strip r (r+a) p+strip r (r+a) q≤
        sourceEnergy r (r+a) (twoCornerFamily c d A B) := by linarith only [hsource,hP,hQ]
    have hw := weight_nonneg r 0
    rcases hsupport with ⟨rfl,hk2,hk6⟩|⟨rfl,hk2,hk5⟩|⟨rfl,hk3,hk5⟩
    · have hcases : (p=1 ∧ q=1) ∨ (p=1 ∧ q=3) ∨ (p=1 ∧ q=4) ∨ (p=1 ∧ q=5) ∨ (p=3 ∧ q=3) := by omega
      rcases hcases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · refine ⟨0,by norm_num [Matches,gap,rowDeficit],?_⟩
        have hcorr := pair_square_cells (p := 1) (q := 1) (by omega : 2≤r)
        rw [rowLower,weightedLoss_four]
        norm_num [quadrantFloor,coeff,stripFloor] at hlow hcorr ⊢
        nlinarith only [hlow,hcorr,hw]
      · refine ⟨6,by norm_num [Matches,gap,rowDeficit],?_⟩
        have hcorr := pair_one_three_square (by omega : 5≤r)
        rw [rowLower,weightedLoss_four]
        norm_num [quadrantFloor,coeff,stripFloor] at hlow hcorr ⊢
        nlinarith only [hlow,hcorr,hw]
      · refine ⟨11,by norm_num [Matches,gap,rowDeficit],?_⟩
        have hcorr := pair_one_four_square (by omega : 6≤r)
        rw [rowLower,weightedLoss_four]
        norm_num [quadrantFloor,coeff,stripFloor] at hlow hcorr ⊢
        nlinarith only [hlow,hcorr,hw]
      · refine ⟨17,by norm_num [Matches,gap,rowDeficit],?_⟩
        have hcorr := pair_one_five_square (by omega : 7≤r)
        rw [rowLower,weightedLoss_four]
        norm_num [quadrantFloor,coeff,stripFloor] at hlow hcorr ⊢
        nlinarith only [hlow,hcorr,hw]
      · refine ⟨18,by norm_num [Matches,gap,rowDeficit],?_⟩
        have hcorr := pair_square_cells (p := 3) (q := 3) (by omega : 2≤r)
        rw [rowLower,weightedLoss_four]
        norm_num [quadrantFloor,coeff,stripFloor] at hlow hcorr ⊢
        nlinarith only [hlow,hcorr,hw]
    · have hcases : (p=1 ∧ q=1) ∨ (p=1 ∧ q=2) ∨ (p=2 ∧ q=2) ∨ (p=1 ∧ q=4) := by omega
      rcases hcases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · refine ⟨1,by norm_num [Matches,gap,rowDeficit],?_⟩
        have hcorr := pair_ordered_cells (p := 1) (q := 1) (by omega : 2≤r) (by omega : r≤r+1)
        rw [rowLower,weightedLoss_four]
        norm_num [quadrantFloor,coeff,stripFloor] at hlow hcorr ⊢
        nlinarith only [hlow,hcorr,hw]
      · refine ⟨3,by norm_num [Matches,gap,rowDeficit],?_⟩
        have hr5 : 5≤r := by
          by_contra hh
          have hr4 : r=4 := by omega
          subst r
          norm_num at harea
        have hcorr := pair_one_two hr5 (by omega : r≤r+1)
        rw [rowLower,weightedLoss_four]
        norm_num [quadrantFloor,coeff,stripFloor] at hlow hcorr ⊢
        nlinarith only [hlow,hcorr,hw]
      · refine ⟨8,by norm_num [Matches,gap,rowDeficit],?_⟩
        have hcorr := pair_two_two (by omega : 5≤r) (by omega : r≤r+1)
        rw [rowLower,weightedLoss_four]
        norm_num [quadrantFloor,coeff,stripFloor] at hlow hcorr ⊢
        nlinarith only [hlow,hcorr,hw]
      · refine ⟨14,by norm_num [Matches,gap,rowDeficit],?_⟩
        have hcorr := pair_one_four_ordered (by omega : 5≤r) (by omega : r≤r+1)
        rw [rowLower,weightedLoss_four]
        norm_num [quadrantFloor,coeff,stripFloor] at hlow hcorr ⊢
        nlinarith only [hlow,hcorr,hw]
    · have hcases : (p=1 ∧ q=2) ∨ (p=1 ∧ q=3) ∨ (p=2 ∧ q=2) ∨ (p=2 ∧ q=3) := by omega
      rcases hcases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · refine ⟨5,by norm_num [Matches,gap,rowDeficit],?_⟩
        have hcorr := pair_ordered_cells (p := 1) (q := 2) (by omega : 2≤r) (by omega : r≤r+2)
        rw [rowLower,weightedLoss_four]
        norm_num [quadrantFloor,coeff,stripFloor] at hlow hcorr ⊢
        nlinarith only [hlow,hcorr,hw]
      · refine ⟨10,by norm_num [Matches,gap,rowDeficit],?_⟩
        have hcorr := pair_one_three_gap_two (by omega : 5≤r)
        rw [rowLower,weightedLoss_four]
        norm_num [quadrantFloor,coeff,stripFloor] at hlow hcorr ⊢
        nlinarith only [hlow,hcorr,hw]
      · refine ⟨10,by norm_num [Matches,gap,rowDeficit],?_⟩
        have hcorr := pair_two_two (by omega : 5≤r) (by omega : r≤r+2)
        rw [rowLower,weightedLoss_four]
        norm_num [quadrantFloor,coeff,stripFloor] at hlow hcorr ⊢
        nlinarith only [hlow,hcorr,hw]
      · refine ⟨16,by norm_num [Matches,gap,rowDeficit],?_⟩
        have hcorr := pair_ordered_cells (p := 2) (q := 3) (by omega : 2≤r) (by omega : r≤r+2)
        rw [rowLower,weightedLoss_four]
        norm_num [quadrantFloor,coeff,stripFloor] at hlow hcorr ⊢
        nlinarith only [hlow,hcorr,hw]

end
end SpanningTreeIsoperimetry.SmallFamilyStripPairs
