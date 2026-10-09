import SpanningTreeIsoperimetry.CornerSeparationTree
import SpanningTreeIsoperimetry.TwoCornerStrips
import SpanningTreeIsoperimetry.StripTreeComparisons

/-! All four two-strip orientations and their exact equality case for actual
primal spanning-tree counts. -/
namespace SpanningTreeIsoperimetry.CornerPrimalDomains

open Ferrers CornerEnergy CornerFolds CornerStripBridge StripPolarization Polarization DomainIsometries
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def stripDiagram (k : ℕ) (vertical : Bool) : Diagram :=
  if vertical then verticalDiagram k else horizontalStrip k

theorem stripDiagram_ferrers (k : ℕ) (vertical : Bool) : IsFerrers (stripDiagram k vertical) := by
  cases vertical
  · exact horizontalStrip_isFerrers k
  · exact verticalDiagram_ferrers k

@[simp] theorem stripDiagram_card (k : ℕ) (vertical : Bool) : (stripDiagram k vertical).card=k := by
  cases vertical <;> simp [stripDiagram,verticalDiagram]

def twoStripPrimal (r s a b : ℕ) (leftV rightV : Bool) : Domain :=
  cornerPrimal (r-1) (s-1) (twoCornerFamily (true,true) (false,false)
    (stripDiagram a leftV) (stripDiagram b rightV))

theorem opposite_strip_faces {r s : ℕ} (hr : 2≤r) (hs : 2≤s) (a b : ℕ) (leftV rightV : Bool) :
    oppositeCornerFaces (r-1) (s-1) (stripDiagram a leftV) (stripDiagram b rightV)=
      twoOrientedFaces r s a b leftV rightV := by
  ext x
  simp only [oppositeCornerFaces,oppositeColumnFaces,Finset.mem_sdiff,Finset.mem_union,
    mem_image_involution (axialReflection_involutive _),bottomRightDefect,
    mem_image_involution (vertical_involutive _),mem_integerFaces_iff,mem_rectangle,
    axialReflection,verticalReflection,mem_twoOrientedFaces]
  cases leftV <;> cases rightV <;>
    simp only [stripDiagram, Bool.false_eq_true, ↓reduceIte,mem_verticalDiagram,mem_horizontalStrip] <;> omega

theorem twoStripPrimal_count {r s a b : ℕ} (hr : 2≤r) (hs : 2≤s)
    (hsize : a+b<min r s) (leftV rightV : Bool) :
    (treeCount (twoStripPrimal r s a b leftV rightV) : ℝ)=
      faceDeterminant (twoOrientedFaces r s a b leftV rightV) 4 := by
  have hA := stripDiagram_ferrers a leftV
  have hB := stripDiagram_ferrers b rightV
  have hsum := totalDefect_twoCornerFamily (by decide : (true,true)≠(false,false))
    (stripDiagram a leftV) (stripDiagram b rightV)
  simp only [stripDiagram_card] at hsum
  have hdet := cornerPrimal_treeCount_eq_faceDeterminant (show 1≤r-1 by omega) (show 1≤s-1 by omega)
    (twoCornerFamily_ferrers (true,true) (false,false) hA hB) (by omega) (by omega)
  rw [cornerFaceDomain_BL_TR (R := r-1) (S := s-1) (by omega) (by omega) _ _
    (ferrers_fit_of_card hA (by simp only [stripDiagram_card]; omega) (by simp only [stripDiagram_card]; omega))
    (ferrers_fit_of_card hB (by simp only [stripDiagram_card]; omega) (by simp only [stripDiagram_card]; omega)),
    opposite_strip_faces hr hs a b leftV rightV] at hdet
  exact hdet

theorem twoStripPrimal_card {r s a b : ℕ} (hr : 1≤r) (hs : 1≤s)
    (hsize : a+b<min r s) (leftV rightV : Bool) :
    (twoStripPrimal r s a b leftV rightV).card=r*s-(a+b) := by
  have hsum := totalDefect_twoCornerFamily (by decide : (true,true)≠(false,false))
    (stripDiagram a leftV) (stripDiagram b rightV)
  simp only [stripDiagram_card] at hsum
  rw [twoStripPrimal,cornerPrimal_card (twoCornerFamily_ferrers (true,true) (false,false)
    (stripDiagram_ferrers a leftV) (stripDiagram_ferrers b rightV)) (by omega) (by omega),
    hsum,Nat.sub_add_cancel hr,Nat.sub_add_cancel hs]

/-- `prop:two-corner-fold`, with actual primal tree counts for every orientation. -/
theorem two_corner_fold_treeCount {r s b : ℕ} (hrs : r≤s) (hb : 1≤b)
    (hsize : s-r+b+2<r) (leftV rightV : Bool) :
    treeCount (twoStripPrimal r s (s-r+2) b leftV rightV)≤
      treeCount (cornerStrip (r-1) (s+1) (b+1)) := by
  have hsource := twoStripPrimal_count (r := r) (s := s) (a := s-r+2) (b := b) (by omega) (by omega) (by omega) leftV rightV
  have htarget := StripTreeComparisons.cornerStrip_count_face (r := r-1) (s := s+1) (k := b+1)
    (by omega) (by omega) (by omega)
  have he1 : r-1-1=r-2 := by omega
  have he2 : s+1-1=s := by omega
  rw [he1,he2] at htarget
  have h := two_corner_fold_determinant hrs hb hsize leftV rightV 4 le_rfl
  rw [← hsource,← htarget] at h
  exact_mod_cast h

theorem two_corner_fold_treeCount_eq_iff {r s b : ℕ} (hrs : r≤s) (hb : 1≤b)
    (hsize : s-r+b+2<r) (leftV rightV : Bool) :
    treeCount (twoStripPrimal r s (s-r+2) b leftV rightV)=
      treeCount (cornerStrip (r-1) (s+1) (b+1)) ↔ r=4 ∧ s=4 ∧ b=1 := by
  have hsource := twoStripPrimal_count (r := r) (s := s) (a := s-r+2) (b := b) (by omega) (by omega) (by omega) leftV rightV
  have htarget := StripTreeComparisons.cornerStrip_count_face (r := r-1) (s := s+1) (k := b+1)
    (by omega) (by omega) (by omega)
  have he1 : r-1-1=r-2 := by omega
  have he2 : s+1-1=s := by omega
  rw [he1,he2] at htarget
  have h := two_corner_fold_determinant_eq_iff hrs hb hsize leftV rightV 4 le_rfl
  rw [← hsource,← htarget] at h
  exact_mod_cast h

theorem two_corner_fold_cardinality {r s b : ℕ} (hrs : r≤s) (hb : 1≤b)
    (hsize : s-r+b+2<r) (leftV rightV : Bool) :
    (twoStripPrimal r s (s-r+2) b leftV rightV).card=
      (cornerStrip (r-1) (s+1) (b+1)).card := by
  rw [twoStripPrimal_card (r := r) (s := s) (a := s-r+2) (b := b) (by omega) (by omega) (by omega),card_cornerStrip (by omega) (by omega)]
  have hr : r-1+1=r := Nat.sub_add_cancel (by omega)
  have hs : s-r+r=s := Nat.sub_add_cancel hrs
  have harea : (r-1)*(s+1)+(s-r+1)=r*s := by nlinarith
  omega

end
end SpanningTreeIsoperimetry.CornerPrimalDomains
