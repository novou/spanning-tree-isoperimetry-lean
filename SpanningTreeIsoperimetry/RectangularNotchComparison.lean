module

public import SpanningTreeIsoperimetry.SingleCornerSmallOrientation
public import SpanningTreeIsoperimetry.SmallFamilyCountComparison
public import SpanningTreeIsoperimetry.SmallFamilySourceBounds
public import SpanningTreeIsoperimetry.SmallCornerCorrections
public import SpanningTreeIsoperimetry.FluxBounds

@[expose] public section

set_option backward.privateInPublic true

/-! Actual spanning-tree improvements for the two rectangular notch families,
using checked finite corrections, coupled errors and scalar endpoint profiles. -/
namespace SpanningTreeIsoperimetry.RectangularNotchComparison

open Ferrers CornerEnergy CornerPrimalDomains CornerProfileNormalization SingleCornerSmallOrientation
open CrossHullCountComparison SmallFamilySourceBounds SmallFamilyCountComparison
open SmallFamilyProfiles SmallFamilyMonotonicity SmallFamilyCostBounds MulticornerEndpointChecks
open FixedStripEnergyUpper SmallCornerCorrections FluxBounds
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def notch (b : ℕ) (v : Bool) : Diagram := if v then faceRectangle b 2 else faceRectangle 2 b
def notchRow (b : ℕ) : Fin 26 := if b=2 then 23 else 24
def notchCoefficient (b : ℕ) : ℝ := if b=2 then 20 else 70/3

theorem notch_ferrers (b : ℕ) (v : Bool) : IsFerrers (notch b v) := by
  cases v <;> simp only [notch,Bool.false_eq_true,ite_false,ite_true] <;> exact faceRectangle_isFerrers _ _

theorem notch_card (b : ℕ) (v : Bool) : (notch b v).card=2*b := by
  cases v <;> simp [notch,faceRectangle,Nat.mul_comm]

theorem notch_energy (b : ℕ) (v : Bool) : realEnergy (notch b v)=realEnergy (faceRectangle b 2) := by
  cases v
  · have h := realEnergy_transpose (faceRectangle b 2)
    rw [transpose_faceRectangle] at h
    simpa only [notch,Bool.false_eq_true,ite_false] using h
  · rfl

private theorem single_finite_energy {r s : ℕ} (c : Corner) (M : Diagram)
    (hM : ∀ d,IsFerrers (singleFamily c M d))
    (hr : totalDefect (singleFamily c M)≤r-1) (hs : totalDefect (singleFamily c M)≤s-1) :
    finiteSourceEnergy (singleFamily c M) hM hr hs=diagramEnergy r s M := by
  rw [← sourceEnergy_eq_finite hM hr hs]
  change sourceEnergy r s (twoCornerFamily c (opposite c) M ∅)=diagramEnergy r s M
  rw [sourceEnergy_pair r s (opposite_distinct c),diagramEnergy_empty,add_zero]

private theorem notch_quadrant {b : ℕ} (hb : b=2 ∨ b=3) :
    quadrantValue (notchRow b)=realEnergy (faceRectangle b 2) := by
  rcases hb with rfl|rfl <;>
    norm_num [notchRow,quadrantValue,RefinedObstructionPolynomials.square.diagram,
      RefinedObstructionPolynomials.rectangle23.diagram]

private theorem notch_weighted {b : ℕ} (hb : b=2 ∨ b=3) (r : ℝ) :
    weightedLoss Finset.univ (coeff (notchRow b)) shifts r=notchCoefficient b/r^4 := by
  rcases hb with rfl|rfl <;>
    norm_num [notchRow,notchCoefficient,weightedLoss,coeff,shifts,Fin.sum_univ_succ] <;> ring

private theorem notch_correction {b r : ℕ} (hb : b=2 ∨ b=3) (hr : 3*b-1≤r) (v : Bool) :
    notchCoefficient b/(r : ℝ)^4<correction (faceRectangle (r-1) (r+b-1)) (notch b v) := by
  rcases hb with rfl|rfl
  · have h := square_lower (r := r) (s := r+2) (by omega) (by omega)
    cases v <;> simpa only [notch,notchCoefficient,ite_true,Bool.false_eq_true,ite_false,square] using h
  · cases v
    · have h := rectangle_six_lower (r := r) (s := r+3) (a := 2) (b := 3)
        (by omega) (by omega) (Or.inl ⟨rfl,rfl⟩)
      simpa only [notch,notchCoefficient,show (3 : ℕ)≠2 by omega,ite_false,Bool.false_eq_true,div_div] using h
    · have h := rectangle_six_lower (r := r) (s := r+3) (a := 3) (b := 2)
        (by omega) (by omega) (Or.inr ⟨rfl,rfl⟩)
      simpa only [notch,notchCoefficient,show (3 : ℕ)≠2 by omega,ite_false,ite_true,div_div] using h

private theorem notch_target {b r : ℕ} (hb : b=2 ∨ b=3) (hr : 3*b-1≤r)
    (hR : 2≤r-1) (hj : b-1≤r+b+1-1) :
    finiteTargetEnergy hR hj≤targetCap (targetCapKind (notchRow b)) := by
  rcases hb with rfl|rfl
  · have h := finiteTargetEnergy_antitone (r := 4) (s := 6) (R := r-1) (S := r+3) (j := 1)
      (by omega) hR (by omega) (by omega) (by omega) (by omega)
    simpa [notchRow,targetCapKind,targetCap,Nat.add_assoc] using h
  · have h := finite_target_upper (R := r-1) (S := r+4) (j := 2) (by omega) (by omega) (by omega)
    have hleft := fluxBound_antitone_left (r := 7) (R := ((r-1 : ℕ) : ℝ))
      (s := ((r+4 : ℕ) : ℝ)) (k := 2) (by norm_num)
      (by exact_mod_cast (show 7≤r-1 by omega)) (by norm_num)
    have hright := fluxBound_antitone_right (r := 7) (s := 12) (S := ((r+4 : ℕ) : ℝ))
      (k := 2) (by norm_num) (by norm_num) (by exact_mod_cast (show 12≤r+4 by omega))
    have hh := h.trans (add_le_add (le_refl (realEnergy (horizontalStrip 2))) (hleft.trans hright))
    simpa [notchRow,targetCapKind,targetCap,Nat.add_assoc] using hh

private theorem notch_area {b r : ℕ} (hb : 2≤b) (hr : 1≤r) :
    r*(r+b)+(b-1)=(r-1)*(r+b+1)+2*b := by
  have hsub := Nat.sub_add_cancel hr
  have hp := congrArg (fun x : ℕ => x*(r+b+1)) hsub
  have hbase : r*(r+b)=(r-1)*(r+b+1)+(b+1) := by nlinarith
  omega

private theorem count_lt_of_notch_profile {b r : ℕ} (hb : b=2 ∨ b=3) (hr : 3*b-1≤r)
    (c : Corner) (v : Bool)
    (hcost : endpointCost (notchRow b) r<quadrantFloor (notchRow b)) :
    treeCount (cornerPrimal (r-1) (r+b-1) (singleFamily c (notch b v)))<
      treeCount (cornerStrip (r-1) (r+b+1) (b-1)) := by
  have hb2 : 2≤b := by rcases hb with rfl|rfl <;> omega
  have hb3 : b≤3 := by rcases hb with rfl|rfl <;> omega
  have hr5 : 5≤r := by omega
  have hM := singleFamily_ferrers c (notch_ferrers b v)
  have hshort : totalDefect (singleFamily c (notch b v))≤r-1 := by
    rw [singleFamily_total,notch_card]
    omega
  have hlong : totalDefect (singleFamily c (notch b v))≤r+b-1 := by
    rw [singleFamily_total,notch_card]
    omega
  have htarget : b-1≤r+b+1-1 := by omega
  have harea : r*(r+b)+(b-1)=(r-1)*(r+b+1)+totalDefect (singleFamily c (notch b v)) := by
    rw [singleFamily_total,notch_card]
    exact notch_area hb2 (by omega)
  apply count_lt_of_profile (R := r-1) (r := r) (s := r+b) (S := r+b+1) (a := b) (h := 1)
    (j := b-1) (by omega) (by omega) (by omega) rfl rfl (by omega)
    (singleFamily c (notch b v)) hM hshort hlong htarget harea (notchRow b)
  · rcases hb with rfl|rfl <;> norm_num [notchRow,gap]
  · rcases hb with rfl|rfl <;> norm_num [notchRow,hullShift]
  · rcases hb with rfl|rfl <;> norm_num [notchRow,sourceShift]
  · rw [if_neg (show r-1≠3 by omega)]
    rcases hb with rfl|rfl <;> norm_num [notchRow,errorCoeff]
  · exact hcost
  · exact notch_target hb hr (by omega) htarget
  · rw [single_finite_energy c (notch b v) hM hshort hlong,diagramEnergy,
      notch_weighted hb,notch_energy]
    have hbase := (quadrantFloor_lt (notchRow b)).trans_eq (notch_quadrant hb)
    have hcorr := notch_correction hb hr v
    exact (add_lt_add hbase hcorr).le

/-- The square-notch family, including its separate least endpoint r=5. -/
theorem square_notch_count {r : ℕ} (hr : 5≤r) (c : Corner) (v : Bool) :
    treeCount (cornerPrimal (r-1) (r+2-1) (singleFamily c (notch 2 v)))<
      treeCount (cornerStrip (r-1) (r+3) 1) := by
  apply count_lt_of_notch_profile (Or.inl rfl) (by omega) c v
  by_cases he : r=5
  · subst r
    exact extra_five_lt_floor (i := 23) (Or.inr (Or.inr rfl))
  · apply endpointCost_lt_floor (notchRow 2)
    norm_num [notchRow,leftEnd]
    exact_mod_cast (show 6≤r by omega)

/-- Both orientations of a2×3 notch are strictly improved by the longer hull. -/
theorem rectangle_notch_count {r : ℕ} (hr : 8≤r) (c : Corner) (v : Bool) :
    treeCount (cornerPrimal (r-1) (r+3-1) (singleFamily c (notch 3 v)))<
      treeCount (cornerStrip (r-1) (r+4) 2) := by
  apply count_lt_of_notch_profile (Or.inr rfl) (by omega) c v
  apply endpointCost_lt_floor (notchRow 3)
  norm_num [notchRow,leftEnd]
  exact_mod_cast hr

/-- The strict count competitors have exactly the same vertex cardinality. -/
theorem notch_competitor_card {b r : ℕ} (hb : b=2 ∨ b=3) (hr : 3*b-1≤r) (c : Corner) (v : Bool) :
    (cornerStrip (r-1) (r+b+1) (b-1)).card=
      (cornerPrimal (r-1) (r+b-1) (singleFamily c (notch b v))).card := by
  have hb2 : 2≤b := by rcases hb with rfl|rfl <;> omega
  have hr5 : 5≤r := by omega
  rw [card_cornerStrip (by omega : 1≤r-1) (by omega : b-1≤r+b+1),
    single_card c (notch_ferrers b v) (by rw [notch_card]; omega)
      (by rw [notch_card]; omega),notch_card,
    Nat.sub_add_cancel (show 1≤r by omega),Nat.sub_add_cancel (show 1≤r+b by omega)]
  have h := notch_area hb2 (show 1≤r by omega)
  omega

theorem notch_not_maximal {b r : ℕ} (hb : b=2 ∨ b=3) (hr : 3*b-1≤r) (c : Corner) (v : Bool) :
    ¬IsMaximizer (cornerPrimal (r-1) (r+b-1) (singleFamily c (notch b v))) := by
  have hb2 : 2≤b := by rcases hb with rfl|rfl <;> omega
  have hr5 : 5≤r := by omega
  have hstrict : treeCount (cornerPrimal (r-1) (r+b-1) (singleFamily c (notch b v)))<
      treeCount (cornerStrip (r-1) (r+b+1) (b-1)) := by
    rcases hb with rfl|rfl
    · simpa only [show r+2+1=r+3 by omega] using square_notch_count (by omega) c v
    · simpa only [show r+3+1=r+4 by omega] using rectangle_notch_count (by omega) c v
  have hc := CanonicalStrips.cornerStrip_connected_of_short_deficit (r := r-1) (s := r+b+1) (k := b-1)
    (by omega) (by omega) (by omega)
  intro hm
  have hle := hm.2 _ (notch_competitor_card hb hr c v) hc
  omega

end
end SpanningTreeIsoperimetry.RectangularNotchComparison
