import SpanningTreeIsoperimetry.SmallFamilyPatternData

/-! Three or more nonempty corners satisfy one of the table's source rows,
without enumerating corner placements or Ferrers diagrams. -/
namespace SpanningTreeIsoperimetry.SmallFamilyThreeCorners
open Ferrers CornerEnergy CornerPrimalDomains SmallFamilySourceBounds SmallFamilyPatternData
open SmallFamilyStripCorrections SmallCornerCorrections
open SmallFamilyProfiles SmallFamilyMonotonicity MulticornerEndpointChecks
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 1000000

theorem three_corner_rows {r a k : ℕ} {M : Corner → Diagram}
    (hM : ∀ c, IsFerrers (M c)) (hcard : totalDefect M=k)
    (hsize : k<r) (hsupport : Supported a k)
    {c d e : Corner} (hcd : c≠d) (hce : c≠e) (hde : d≠e)
    (hc : (M c).Nonempty) (hd : (M d).Nonempty) (he : (M e).Nonempty) : RowBound r a k M := by
  have hk3 : 3≤k := by have h := three_total_ge_three hcd hce hde hc hd he; omega
  have hk6 : k≤6 := by rcases hsupport with h|h|h <;> omega
  have hQ := three_floor hM (show totalDefect M≤6 by omega) hcd hce hde hc hd he
  have hE := sourceEnergy_ge_cells r (r+a) M
  have hbare := sourceEnergy_ge_quadrant r (r+a) M
  rw [hcard] at hQ hE
  have hw := weight_nonneg r 0
  rcases hsupport with ⟨rfl,hk2,hk6⟩|⟨rfl,hk2,hk5⟩|⟨rfl,hk2,hk5⟩
  · have hS := single_square_weight (by omega : 2≤r)
    simp only [Nat.add_zero] at hE hbare ⊢
    interval_cases k
    · refine ⟨2,by norm_num [Matches,gap,rowDeficit],?_⟩
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor] at hQ hE ⊢
      nlinarith only [hQ,hE,hS,hw]
    · refine ⟨7,by norm_num [Matches,gap,rowDeficit],?_⟩
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor] at hQ hE ⊢
      nlinarith only [hQ,hE,hS,hw]
    · refine ⟨13,by norm_num [Matches,gap,rowDeficit],?_⟩
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor] at hQ hE ⊢
      nlinarith only [hQ,hE,hS,hw]
    · refine ⟨19,by norm_num [Matches,gap,rowDeficit],?_⟩
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor] at hQ hE ⊢
      nlinarith only [hQ,hE,hS,hw]
  · have hS := single_ordered_weight (by omega : 2≤r) (by omega : r≤r+1)
    interval_cases k
    · refine ⟨4,by norm_num [Matches,gap,rowDeficit],?_⟩
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor] at hQ hE ⊢
      nlinarith only [hQ,hE,hS,hw]
    · refine ⟨9,by norm_num [Matches,gap,rowDeficit],?_⟩
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor] at hQ hE ⊢
      nlinarith only [hQ,hE,hS,hw]
    · refine ⟨15,by norm_num [Matches,gap,rowDeficit],?_⟩
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor] at hQ hE ⊢
      nlinarith only [hQ,hE,hS,hw]
  · have hS := single_ordered_weight (by omega : 2≤r) (by omega : r≤r+2)
    interval_cases k
    · refine ⟨5,by norm_num [Matches,gap,rowDeficit],?_⟩
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor] at hQ hE ⊢
      nlinarith only [hQ,hE,hS,hw]
    · refine ⟨10,by norm_num [Matches,gap,rowDeficit],?_⟩
      have hW := weight_le_at (by decide : 0<5) (show 5≤r by omega)
      norm_num [weight] at hW
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor,weight] at hQ ⊢
      nlinarith only [hQ,hbare,hW]
    · refine ⟨16,by norm_num [Matches,gap,rowDeficit],?_⟩
      rw [rowLower,weightedLoss_four]
      norm_num [quadrantFloor,coeff,stripFloor] at hQ hE ⊢
      nlinarith only [hQ,hE,hS,hw]

end
end SpanningTreeIsoperimetry.SmallFamilyThreeCorners
