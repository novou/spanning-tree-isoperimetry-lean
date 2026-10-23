module

public import SpanningTreeIsoperimetry.CornerPrimalFaces
public import SpanningTreeIsoperimetry.ThirteenFaceCounts
public import SpanningTreeIsoperimetry.ThreeCellEnergy

@[expose] public section

/-! The square-hull N=13 comparisons for actual connected primal domains. -/
namespace SpanningTreeIsoperimetry.SmallPrimalComparisons
open Ferrers CornerEnergy CornerPrimalDomains ThirteenFaceCounts
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def oppositeFamily : Corner → Diagram :=
  twoCornerFamily (true,true) (false,false) (horizontalStrip 2) (horizontalStrip 1)

def ellFamily : Corner → Diagram :=
  twoCornerFamily (true,true) (false,false) threeCell ∅

def tripleFamily : Corner → Diagram := fun c =>
  if c=(true,true) ∨ c=(false,true) ∨ c=(false,false) then horizontalStrip 1 else ∅

theorem oppositeFamily_ferrers : ∀ c, IsFerrers (oppositeFamily c) :=
  twoCornerFamily_ferrers _ _ (horizontalStrip_isFerrers 2) (horizontalStrip_isFerrers 1)

theorem ellFamily_ferrers : ∀ c, IsFerrers (ellFamily c) :=
  twoCornerFamily_ferrers _ _ ThreeCellEnergy.ell_isFerrers
    (by intro p hp; exact False.elim (Finset.notMem_empty p hp))

theorem tripleFamily_ferrers : ∀ c, IsFerrers (tripleFamily c) := by
  intro c
  unfold tripleFamily
  split_ifs
  · exact horizontalStrip_isFerrers 1
  · intro p hp
    exact False.elim (Finset.notMem_empty p hp)

theorem oppositeFamily_total : totalDefect oppositeFamily=3 := by
  rw [oppositeFamily,totalDefect_twoCornerFamily (by decide : (true,true)≠(false,false)),
    card_horizontalStrip,card_horizontalStrip]

theorem ellFamily_total : totalDefect ellFamily=3 := by
  rw [ellFamily,totalDefect_twoCornerFamily (by decide : (true,true)≠(false,false)),card_threeCell]
  simp

theorem tripleFamily_total : totalDefect tripleFamily=3 := by decide +kernel

theorem opposite_face_set : cornerFaceDomain 3 3 oppositeFamily=Finset.univ.image oppositePoints := by
  decide +kernel

theorem ell_face_set : cornerFaceDomain 3 3 ellFamily=Finset.univ.image ellPoints := by decide +kernel

theorem triple_face_set : cornerFaceDomain 3 3 tripleFamily=Finset.univ.image triplePoints := by decide +kernel

theorem opposite_primal_count : treeCount (cornerPrimal 3 3 oppositeFamily)=2656 := by
  have h:=cornerPrimal_treeCount_eq_faceDeterminant (by decide : 1≤3) (by decide : 1≤3)
    oppositeFamily_ferrers (by rw [oppositeFamily_total]) (by rw [oppositeFamily_total])
  rw [opposite_face_set,opposite_count] at h
  exact_mod_cast h

theorem ell_primal_count : treeCount (cornerPrimal 3 3 ellFamily)=2640 := by
  have h:=cornerPrimal_treeCount_eq_faceDeterminant (by decide : 1≤3) (by decide : 1≤3)
    ellFamily_ferrers (by rw [ellFamily_total]) (by rw [ellFamily_total])
  rw [ell_face_set,ell_count] at h
  exact_mod_cast h

theorem triple_primal_count : treeCount (cornerPrimal 3 3 tripleFamily)=2624 := by
  have h:=cornerPrimal_treeCount_eq_faceDeterminant (by decide : 1≤3) (by decide : 1≤3)
    tripleFamily_ferrers (by rw [tripleFamily_total]) (by rw [tripleFamily_total])
  rw [triple_face_set,triple_count] at h
  exact_mod_cast h

theorem small_primal_cardinalities : (cornerPrimal 3 3 oppositeFamily).card=13 ∧
    (cornerPrimal 3 3 ellFamily).card=13 ∧ (cornerPrimal 3 3 tripleFamily).card=13 := by
  constructor
  · rw [cornerPrimal_card oppositeFamily_ferrers (by rw [oppositeFamily_total])
      (by rw [oppositeFamily_total]),oppositeFamily_total]
  · constructor
    · rw [cornerPrimal_card ellFamily_ferrers (by rw [ellFamily_total])
        (by rw [ellFamily_total]),ellFamily_total]
    · rw [cornerPrimal_card tripleFamily_ferrers (by rw [tripleFamily_total])
        (by rw [tripleFamily_total]),tripleFamily_total]

end
end SpanningTreeIsoperimetry.SmallPrimalComparisons
