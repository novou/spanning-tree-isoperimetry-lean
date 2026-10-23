module

public import SpanningTreeIsoperimetry.RectangleEnergyBounds
public import SpanningTreeIsoperimetry.ThreeCellEnergy

@[expose] public section

set_option backward.privateInPublic true

/-! Straight strips uniquely minimize the energy of every Ferrers defect,
with a common positive gap for every other shape. -/
namespace SpanningTreeIsoperimetry.StripRigidity
open Ferrers CornerEnergy RectangleEnergyBounds

def IsStraightStrip (M : Diagram) : Prop :=
  M=horizontalStrip M.card ∨ M=transpose (horizontalStrip M.card)

private theorem rectangle_card (r s : ℕ) : (faceRectangle r s).card=r*s := by
  simp [faceRectangle]

theorem rectangle_horizontal (r : ℕ) : faceRectangle r 1=horizontalStrip r := by
  ext p
  rw [mem_faceRectangle,mem_horizontalStrip]
  omega

theorem rectangle_vertical (s : ℕ) : faceRectangle 1 s=transpose (horizontalStrip s) := by
  rw [← transpose_faceRectangle s 1,rectangle_horizontal]

theorem straight_energy {M : Diagram} (h : IsStraightStrip M) :
    realEnergy M=realEnergy (horizontalStrip M.card) := by
  rcases h with h|h
  · exact congrArg realEnergy h
  · exact (congrArg realEnergy h).trans (realEnergy_transpose _)

/-- Manuscript `prop:strip-rigidity`, including its quantitative shape gap. -/
theorem nonstrip_energy_gap {M : Diagram} (hM : IsFerrers M) (hne : M.Nonempty)
    (hstrip : ¬IsStraightStrip M) :
    (1 : ℝ)/4000<realEnergy M-realEnergy (horizontalStrip M.card) := by
  by_cases hrect : IsRectangle M
  · obtain ⟨r,s,he⟩:=hrect
    change M=faceRectangle r s at he
    subst M
    have hc := Finset.card_pos.mpr hne
    rw [rectangle_card] at hc
    have hr : 0<r := by nlinarith
    have hs : 0<s := by nlinarith
    have hr1 : r≠1 := by
      intro h
      subst r
      apply hstrip
      right
      simpa only [rectangle_card,one_mul] using rectangle_vertical s
    have hs1 : s≠1 := by
      intro h
      subst s
      apply hstrip
      left
      simpa only [rectangle_card,mul_one] using rectangle_horizontal r
    have hr2 : 2≤r := by omega
    have hs2 : 2≤s := by omega
    have hbound := UniformStripEnergy.realEnergy_strip_le_limit (faceRectangle r s).card
    by_cases hr3 : 3≤r
    · have hm := rectangle_energy_mono (by decide : 0<3) (by decide : 0<2) hr3 hs2
      linarith [rectangle_strip_limit_gap]
    · by_cases hs3 : 3≤s
      · have hm := rectangle_energy_mono (by decide : 0<3) (by decide : 0<2) hs3 hr2
        rw [← transpose_faceRectangle r s,realEnergy_transpose] at hm
        linarith [rectangle_strip_limit_gap]
      · have hre : r=2 := by omega
        have hse : s=2 := by omega
        subst r
        subst s
        rw [rectangle_card]
        norm_num
        linarith [square_strip_four_gap]
  · linarith [ThreeCellEnergy.nonrectangle_strip_gap hM hne hrect M.card]

theorem nonempty_of_not_straight {M : Diagram} (h : ¬IsStraightStrip M) : M.Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro he
  subst M
  apply h
  left
  simp [horizontalStrip]

theorem strip_energy_minimal {M : Diagram} (hM : IsFerrers M) :
    realEnergy (horizontalStrip M.card)≤realEnergy M := by
  by_cases hs : IsStraightStrip M
  · exact (straight_energy hs).ge
  · linarith [nonstrip_energy_gap hM (nonempty_of_not_straight hs) hs]

theorem strip_energy_eq_iff {M : Diagram} (hM : IsFerrers M) :
    realEnergy M=realEnergy (horizontalStrip M.card) ↔ IsStraightStrip M := by
  constructor
  · intro he
    by_contra hs
    have h := nonstrip_energy_gap hM (nonempty_of_not_straight hs) hs
    rw [he,sub_self] at h
    norm_num at h
  · exact straight_energy

end SpanningTreeIsoperimetry.StripRigidity
