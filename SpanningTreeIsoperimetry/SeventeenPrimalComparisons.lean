module

public import SpanningTreeIsoperimetry.CornerPrimalFaces
public import SpanningTreeIsoperimetry.TwoCornerStripTree
public import SpanningTreeIsoperimetry.FiniteFaceCountBridge
public import SpanningTreeIsoperimetry.ThreeCellEnergy

@[expose] public section

/-! The actual opposite-pair, L and three-singleton tree counts at seventeen.
The exhaustive shape reduction is separate from these strict comparisons. -/
namespace SpanningTreeIsoperimetry.SeventeenPrimalComparisons
open Ferrers CornerEnergy CornerPrimalDomains SmallCases FiniteFaceCountBridge
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def pairFamily (vertical : Bool) : Corner → Diagram :=
  twoCornerFamily (true,true) (false,false) (stripDiagram 2 vertical) (horizontalStrip 1)
def ellFamily : Corner → Diagram := twoCornerFamily (true,true) (false,false) threeCell ∅
def tripleFamily : Corner → Diagram := fun c => if c=(false,false) then ∅ else horizontalStrip 1

theorem pairFamily_ferrers (v : Bool) : ∀ c, IsFerrers (pairFamily v c) :=
  twoCornerFamily_ferrers _ _ (stripDiagram_ferrers 2 v) (horizontalStrip_isFerrers 1)
theorem ellFamily_ferrers : ∀ c, IsFerrers (ellFamily c) :=
  twoCornerFamily_ferrers _ _ ThreeCellEnergy.ell_isFerrers
    (by intro p hp; exact False.elim (Finset.notMem_empty p hp))
theorem tripleFamily_ferrers : ∀ c, IsFerrers (tripleFamily c) := by
  intro c
  unfold tripleFamily
  split_ifs
  · intro p hp; exact False.elim (Finset.notMem_empty p hp)
  · exact horizontalStrip_isFerrers 1

theorem pairFamily_total (v : Bool) : totalDefect (pairFamily v)=3 := by
  rw [pairFamily,totalDefect_twoCornerFamily (by decide : (true,true)≠(false,false))]
  simp only [stripDiagram_card,card_horizontalStrip]
theorem ellFamily_total : totalDefect ellFamily=3 := by
  rw [ellFamily,totalDefect_twoCornerFamily (by decide : (true,true)≠(false,false)),card_threeCell]
  simp
theorem tripleFamily_total : totalDefect tripleFamily=3 := by decide +kernel

theorem pair_face_set (v : Bool) : cornerFaceDomain 3 4 (pairFamily v)=
    Finset.univ.image (if v then winner17Points else short17Points) := by
  cases v <;> decide +kernel
theorem ell_face_set : cornerFaceDomain 3 4 ellFamily=Finset.univ.image alternative17Points := by decide +kernel
theorem triple_face_set : cornerFaceDomain 3 4 tripleFamily=Finset.univ.image triple17Points := by decide +kernel

theorem pair_count (v : Bool) : treeCount (cornerPrimal 3 4 (pairFamily v))=
    if v then 112456 else 111184 := by
  have h := cornerPrimal_treeCount_eq_faceDeterminant (by decide : 1≤3) (by decide : 1≤4)
    (pairFamily_ferrers v) (by rw [pairFamily_total]) (by rw [pairFamily_total]; decide)
  rw [pair_face_set] at h
  cases v
  · simp only [Bool.false_eq_true,ite_false] at h ⊢
    rw [faceDeterminant_points short17Points seventeen_points_injective.2.2.2.2,short17Points_det] at h
    norm_num [alternative17,core,continuant,ladder] at h
    exact_mod_cast h
  · simp only [ite_true] at h ⊢
    rw [faceDeterminant_points winner17Points seventeen_points_injective.1,winner17Points_det] at h
    norm_num [winner17,ladder,cornerLadder,continuant,cycle] at h
    exact_mod_cast h

theorem ell_count : treeCount (cornerPrimal 3 4 ellFamily)=111184 := by
  have h := cornerPrimal_treeCount_eq_faceDeterminant (by decide : 1≤3) (by decide : 1≤4)
    ellFamily_ferrers (by rw [ellFamily_total]) (by rw [ellFamily_total]; decide)
  rw [ell_face_set,faceDeterminant_points alternative17Points seventeen_points_injective.2.1,
    alternative17Points_det] at h
  norm_num [alternative17,core,continuant,ladder] at h
  exact_mod_cast h

theorem triple_count : treeCount (cornerPrimal 3 4 tripleFamily)=110220 := by
  have h := cornerPrimal_treeCount_eq_faceDeterminant (by decide : 1≤3) (by decide : 1≤4)
    tripleFamily_ferrers (by rw [tripleFamily_total]) (by rw [tripleFamily_total]; decide)
  rw [triple_face_set,faceDeterminant_points triple17Points seventeen_points_injective.2.2.1,
    triple17Points_det] at h
  norm_num [triple17,core,continuant,ladder,cycle] at h
  exact_mod_cast h

theorem candidate_cards : (cornerPrimal 3 4 (pairFamily true)).card=17 ∧
    (cornerPrimal 3 4 (pairFamily false)).card=17 ∧
    (cornerPrimal 3 4 ellFamily).card=17 ∧ (cornerPrimal 3 4 tripleFamily).card=17 := by
  constructor
  · rw [cornerPrimal_card (pairFamily_ferrers true) (by rw [pairFamily_total])
      (by rw [pairFamily_total]; decide),pairFamily_total]
  constructor
  · rw [cornerPrimal_card (pairFamily_ferrers false) (by rw [pairFamily_total])
      (by rw [pairFamily_total]; decide),pairFamily_total]
  constructor
  · rw [cornerPrimal_card ellFamily_ferrers (by rw [ellFamily_total])
      (by rw [ellFamily_total]; decide),ellFamily_total]
  · rw [cornerPrimal_card tripleFamily_ferrers (by rw [tripleFamily_total])
      (by rw [tripleFamily_total]; decide),tripleFamily_total]

theorem other_candidates_not_maximal : ¬IsMaximizer (cornerPrimal 3 4 (pairFamily false)) ∧
    ¬IsMaximizer (cornerPrimal 3 4 ellFamily) ∧ ¬IsMaximizer (cornerPrimal 3 4 tripleFamily) := by
  have hc := cornerPrimal_connected (R := 3) (S := 4)
    (pairFamily_ferrers true) (by rw [pairFamily_total])
  constructor
  · intro hm
    have h := hm.2 (cornerPrimal 3 4 (pairFamily true))
      (candidate_cards.1.trans candidate_cards.2.1.symm) hc
    rw [pair_count,pair_count] at h
    norm_num at h
  constructor
  · intro hm
    have h := hm.2 (cornerPrimal 3 4 (pairFamily true))
      (candidate_cards.1.trans candidate_cards.2.2.1.symm) hc
    rw [pair_count,ell_count] at h
    norm_num at h
  · intro hm
    have h := hm.2 (cornerPrimal 3 4 (pairFamily true))
      (candidate_cards.1.trans candidate_cards.2.2.2.symm) hc
    rw [pair_count,triple_count] at h
    norm_num at h

end
end SpanningTreeIsoperimetry.SeventeenPrimalComparisons
