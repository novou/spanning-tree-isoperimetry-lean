module

public import SpanningTreeIsoperimetry.StripRigidity
public import SpanningTreeIsoperimetry.StripStrictness

@[expose] public section

/-! Any finite family of Ferrers defects concentrates in one straight strip.
The equality case and a uniform gap follow from the closed shape and merge gaps. -/
namespace SpanningTreeIsoperimetry.CornerConcentration
open Ferrers CornerEnergy StripRigidity
open scoped BigOperators Classical
variable {ι : Type*} [DecidableEq ι]

def IsConcentrated (I : Finset ι) (M : ι → Diagram) : Prop :=
  ∃ i∈I, (M i).Nonempty ∧ IsStraightStrip (M i) ∧ ∀ j∈I, j≠i → M j=∅

theorem strip_merge_le (a b : ℕ) :
    realEnergy (horizontalStrip (a+b))≤realEnergy (horizontalStrip a)+realEnergy (horizontalStrip b) := by
  by_cases ha : a=0
  · simp [ha]
  by_cases hb : b=0
  · simp [hb]
  exact (realEnergy_strip_concentration_strict (by omega) (by omega)).le

theorem strip_sum_le (I : Finset ι) (k : ι → ℕ) :
    realEnergy (horizontalStrip (∑ i∈I,k i))≤∑ i∈I,realEnergy (horizontalStrip (k i)) := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    have hs:=strip_merge_le (k i) (∑ j∈I,k j)
    linarith

theorem concentration_minimal (I : Finset ι) (M : ι → Diagram)
    (hM : ∀ i∈I, IsFerrers (M i)) :
    realEnergy (horizontalStrip (∑ i∈I,(M i).card))≤∑ i∈I,realEnergy (M i) :=
  (strip_sum_le I (fun i => (M i).card)).trans
    (Finset.sum_le_sum (fun i hi => strip_energy_minimal (hM i hi)))

noncomputable def concentrationGap : ℝ :=
  min ((1 : ℝ)/4000) ((2*realEnergy (horizontalStrip 1)-realEnergy (horizontalStrip 2))/2)

theorem concentrationGap_pos : 0<concentrationGap := by
  apply lt_min
  · norm_num
  · exact half_pos realEnergy_strip_gap_pos

theorem two_positive_strip_gap (I : Finset ι) (k : ι → ℕ) {i j : ι}
    (hi : i∈I) (hj : j∈I) (hji : j≠i) (hki : 0<k i) (hkj : 0<k j) :
    2*realEnergy (horizontalStrip 1)-realEnergy (horizontalStrip 2)≤
      (∑ a∈I,realEnergy (horizontalStrip (k a)))-realEnergy (horizontalStrip (∑ a∈I,k a)) := by
  let B := ∑ a∈I.erase i,k a
  have hj' : j∈I.erase i := Finset.mem_erase.mpr ⟨hji,hj⟩
  have hsingle : k j≤B := Finset.single_le_sum (fun a _ => Nat.zero_le (k a)) hj'
  have hB : 1≤B := by omega
  have hp := realEnergy_strip_concentration_gap (by omega : 1≤k i) hB
  have ho := strip_sum_le (I.erase i) k
  have hk : k i+B=∑ a∈I,k a := by
    have h:=Finset.sum_erase_add I k hi
    dsimp [B]
    omega
  have hs : realEnergy (horizontalStrip (k i))+(∑ a∈I.erase i,realEnergy (horizontalStrip (k a)))=
      ∑ a∈I,realEnergy (horizontalStrip (k a)) := by
    simpa only [add_comm] using Finset.sum_erase_add I (fun a => realEnergy (horizontalStrip (k a))) hi
  rw [hk] at hp
  change realEnergy (horizontalStrip B)≤_ at ho
  linarith

/-- The absolute shape gap and the strip merge gap apply to every family size. -/
theorem concentration_strict_gap (I : Finset ι) (M : ι → Diagram)
    (hM : ∀ i∈I, IsFerrers (M i)) (hK : 0<∑ i∈I,(M i).card)
    (hn : ¬IsConcentrated I M) :
    concentrationGap<(∑ i∈I,realEnergy (M i))-
      realEnergy (horizontalStrip (∑ i∈I,(M i).card)) := by
  by_cases hbad : ∃ i∈I, ¬IsStraightStrip (M i)
  · obtain ⟨i,hi,hbad⟩:=hbad
    have hg:=nonstrip_energy_gap (hM i hi) (nonempty_of_not_straight hbad) hbad
    have hs := Finset.single_le_sum
      (fun j hj => sub_nonneg.mpr (strip_energy_minimal (hM j hj))) hi
    have hw:=strip_sum_le I (fun i => (M i).card)
    rw [Finset.sum_sub_distrib] at hs
    have he : concentrationGap≤(1 : ℝ)/4000 := min_le_left _ _
    linarith
  · have hstraight : ∀ i∈I, IsStraightStrip (M i) := by simpa only [not_exists,not_and,not_not] using hbad
    have hex : ∃ i∈I, (M i).Nonempty := by
      by_contra hn
      push_neg at hn
      have hz : ∑ i∈I,(M i).card=0 := Finset.sum_eq_zero (fun i hi =>
        Finset.card_eq_zero.mpr (hn i hi))
      omega
    obtain ⟨i,hi,hni⟩:=hex
    have hexj : ∃ j∈I, j≠i ∧ (M j).Nonempty := by
      by_contra hj
      apply hn
      refine ⟨i,hi,hni,hstraight i hi,?_⟩
      intro j hjI hji
      by_contra hjM
      exact hj ⟨j,hjI,hji,Finset.nonempty_iff_ne_empty.mpr hjM⟩
    obtain ⟨j,hj,hji,hnj⟩:=hexj
    have hg := two_positive_strip_gap I (fun i => (M i).card) hi hj hji
      (Finset.card_pos.mpr hni) (Finset.card_pos.mpr hnj)
    have hs : (∑ i∈I,realEnergy (M i))=∑ i∈I,realEnergy (horizontalStrip (M i).card) :=
      Finset.sum_congr rfl (fun i hi => straight_energy (hstraight i hi))
    have he : concentrationGap≤
        (2*realEnergy (horizontalStrip 1)-realEnergy (horizontalStrip 2))/2 := min_le_right _ _
    rw [hs]
    linarith [realEnergy_strip_gap_pos]

theorem concentrated_energy {I : Finset ι} {M : ι → Diagram} (h : IsConcentrated I M) :
    (∑ i∈I,realEnergy (M i))=realEnergy (horizontalStrip (∑ i∈I,(M i).card)) := by
  obtain ⟨i,hi,hne,hs,hothers⟩:=h
  have hc : (∑ j∈I,(M j).card)=(M i).card := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      rw [hothers j hj hji]
      simp
    · intro hn
      exact (hn hi).elim
  have he : (∑ j∈I,realEnergy (M j))=realEnergy (M i) := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      rw [hothers j hj hji,realEnergy_empty]
    · intro hn
      exact (hn hi).elim
  rw [hc,he]
  exact straight_energy hs

/-- Manuscript `prop:concentration`, including the full equality condition. -/
theorem concentration_eq_iff (I : Finset ι) (M : ι → Diagram)
    (hM : ∀ i∈I, IsFerrers (M i)) (hK : 0<∑ i∈I,(M i).card) :
    (∑ i∈I,realEnergy (M i))=realEnergy (horizontalStrip (∑ i∈I,(M i).card)) ↔ IsConcentrated I M := by
  constructor
  · intro he
    by_contra hn
    have hg:=concentration_strict_gap I M hM hK hn
    rw [he,sub_self] at hg
    linarith [concentrationGap_pos]
  · exact concentrated_energy

end SpanningTreeIsoperimetry.CornerConcentration
