module

public import SpanningTreeIsoperimetry.CornerPrimalFaces

@[expose] public section

/-! Strict separation of two adjacent actual primal Ferrers defects. -/
namespace SpanningTreeIsoperimetry.CornerPrimalDomains

open Ferrers CornerEnergy CornerFolds
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def adjacentPrimal (R S : ℕ) (A B : Diagram) : Domain :=
  cornerPrimal R S (twoCornerFamily (true,true) (false,true) A B)

def oppositePrimal (R S : ℕ) (A B : Diagram) : Domain :=
  cornerPrimal R S (twoCornerFamily (true,true) (false,false) A B)

theorem ferrers_fit_of_card {R S : ℕ} {M : Diagram} (hM : IsFerrers M)
    (hR : M.card≤R) (hS : M.card≤S) : M⊆faceRectangle R S := by
  intro p hp
  have hb := ferrers_coordinate_lt_card hM hp
  exact mem_faceRectangle.mpr ⟨by omega,by omega⟩

/-- `prop:separate-corners` for actual primal spanning-tree counts. -/
theorem separate_corners_treeCount {R S : ℕ} (A B : Diagram) (hA : IsFerrers A) (hB : IsFerrers B)
    (hneA : A.Nonempty) (hneB : B.Nonempty) (hR : A.card+B.card≤R) (hS : A.card+B.card≤S) :
    treeCount (adjacentPrimal R S A B)<treeCount (oppositePrimal R S A B) := by
  have ha := Finset.card_pos.mpr hneA
  have hb := Finset.card_pos.mpr hneB
  have hR0 : 1≤R := by omega
  have hS0 : 1≤S := by omega
  have htA := totalDefect_twoCornerFamily (by decide : (true,true)≠(false,true)) A B
  have htB := totalDefect_twoCornerFamily (by decide : (true,true)≠(false,false)) A B
  have hdetA := cornerPrimal_treeCount_eq_faceDeterminant hR0 hS0
    (twoCornerFamily_ferrers (true,true) (false,true) hA hB) (by omega) (by omega)
  have hdetB := cornerPrimal_treeCount_eq_faceDeterminant hR0 hS0
    (twoCornerFamily_ferrers (true,true) (false,false) hA hB) (by omega) (by omega)
  have hfitA := ferrers_fit_of_card hA (show A.card≤R by omega) (show A.card≤S by omega)
  have hfitB := ferrers_fit_of_card hB (show B.card≤R by omega) (show B.card≤S by omega)
  rw [cornerFaceDomain_BL_BR hR0 hS0 A B hfitA hfitB] at hdetA
  rw [cornerFaceDomain_BL_TR hR0 hS0 A B hfitA hfitB] at hdetB
  have h := separate_corners_determinant A B hA hB hneA hneB hR hS 4 le_rfl
  rw [← hdetA,← hdetB] at h
  exact_mod_cast h

/-- The comparison preserves cardinality and realizes both displayed minimal
hulls by connected domains; these are conclusions, not supplied premises. -/
theorem separate_corners_geometry {R S : ℕ} (A B : Diagram) (hA : IsFerrers A) (hB : IsFerrers B)
    (hR : A.card+B.card≤R) (hS : A.card+B.card≤S) :
    (adjacentPrimal R S A B).card=(oppositePrimal R S A B).card ∧
    (domainGraph (adjacentPrimal R S A B)).Connected ∧
    (domainGraph (oppositePrimal R S A B)).Connected ∧
    SquareMaximality.IsRectHull (adjacentPrimal R S A B) 0 0 (R+1) (S+1) ∧
    SquareMaximality.IsRectHull (oppositePrimal R S A B) 0 0 (R+1) (S+1) := by
  have htA := totalDefect_twoCornerFamily (by decide : (true,true)≠(false,true)) A B
  have htB := totalDefect_twoCornerFamily (by decide : (true,true)≠(false,false)) A B
  have hfA := twoCornerFamily_ferrers (true,true) (false,true) hA hB
  have hfB := twoCornerFamily_ferrers (true,true) (false,false) hA hB
  refine ⟨?_,cornerPrimal_connected hfA (by omega),cornerPrimal_connected hfB (by omega),
    cornerPrimal_hull (by omega) (by omega),cornerPrimal_hull (by omega) (by omega)⟩
  rw [adjacentPrimal,oppositePrimal,cornerPrimal_card hfA (by omega) (by omega),
    cornerPrimal_card hfB (by omega) (by omega),htA,htB]

end
end SpanningTreeIsoperimetry.CornerPrimalDomains
