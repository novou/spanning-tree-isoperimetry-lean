module

public import SpanningTreeIsoperimetry.FerrersFoldHook
public import SpanningTreeIsoperimetry.StripRigidity
public import SpanningTreeIsoperimetry.HullArithmetic
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! The small classification has six possible nonstrip hulls. A Ferrers
defect of at most three cells is a strip or the three-cell L. -/
namespace SpanningTreeIsoperimetry.SmallShapeCatalogue
open Ferrers CornerEnergy CornerFolds StripRigidity

theorem ferrers_three_cell_catalogue {M : Diagram} (hM : IsFerrers M) (hk : M.card≤3) :
    IsStraightStrip M ∨ M=threeCell := by
  by_cases hs : IsStraightStrip M
  · exact Or.inl hs
  · right
    have hne:=nonempty_of_not_straight hs
    have hb:=ferrers_nonstrip_extents hM (fun h => hs (Or.inl h)) (fun h => hs (Or.inr h))
    have h0:=ferrers_origin_mem hM hne
    have hx : (1,0)∈M := hM _ (ferrers_width_corner hM hne) _ (by omega) le_rfl
    have hy : (0,1)∈M := hM _ (ferrers_height_corner hM hne) _ le_rfl (by omega)
    have hsub : threeCell⊆M := by
      intro p hp
      simp only [threeCell,Finset.mem_insert,Finset.mem_singleton] at hp
      rcases hp with rfl|rfl|rfl
      · exact h0
      · exact hx
      · exact hy
    exact (Finset.eq_of_subset_of_card_le hsub (by simpa only [card_threeCell] using hk)).symm

theorem ferrers_two_cell_strip {M : Diagram} (hM : IsFerrers M) (hk : M.card≤2) : IsStraightStrip M := by
  rcases ferrers_three_cell_catalogue hM (by omega) with h|h
  · exact h
  · rw [h,card_threeCell] at hk
    omega

theorem small_nonstrip_hulls {N r s k : ℕ} (hN : N≤17) (hr : 0<r) (hrs : r≤s)
    (hcard : N+k=r*s) (hk : k<r) (hk2 : 2≤k) (hL : IsMinimumSideSum N (r+s)) :
    (r=3 ∧ s=3 ∧ k=2) ∨ (r=3 ∧ s=4 ∧ k=2) ∨ (r=3 ∧ s=5 ∧ k=2) ∨
      (r=4 ∧ s=4 ∧ k=2) ∨ (r=4 ∧ s=4 ∧ k=3) ∨ (r=4 ∧ s=5 ∧ k=3) := by
  have hsq:=hL.2.1
  have hpred : r+s-1+1=r+s := by omega
  have hsum : r+s≤9 := by nlinarith
  have hr3 : 3≤r := by omega
  have hr4 : r≤4 := by omega
  have hs3 : 3≤s := by omega
  have hs6 : s≤6 := by omega
  interval_cases r <;> interval_cases s <;> interval_cases k <;>
    norm_num at * <;> omega

end SpanningTreeIsoperimetry.SmallShapeCatalogue
