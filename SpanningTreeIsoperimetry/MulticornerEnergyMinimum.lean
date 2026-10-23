module

public import SpanningTreeIsoperimetry.StripSupportingLines
public import SpanningTreeIsoperimetry.CanonicalSmallBaseline

@[expose] public section

/-! Actual quadrant lower bounds for families with at least two or three
nonempty corners, using strip minimality and discrete concavity. -/
namespace SpanningTreeIsoperimetry.MulticornerEnergyMinimum
open Ferrers CornerEnergy CornerConcentration StripRigidity StripSupportingLines
open scoped Classical BigOperators
noncomputable section
variable {ι : Type*} [DecidableEq ι]

theorem two_nonempty_minimum (I : Finset ι) (M : ι → Diagram)
    (hM : ∀ i∈I, IsFerrers (M i)) {i j : ι} (hi : i∈I) (hj : j∈I) (hji : j≠i)
    (hneI : (M i).Nonempty) (hneJ : (M j).Nonempty) :
    realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip ((∑ a∈I,(M a).card)-1))≤
      ∑ a∈I,realEnergy (M a) := by
  let J := I.erase i
  have hjJ : j∈J := Finset.mem_erase.mpr ⟨hji,hj⟩
  have ha : 1≤(M i).card := by have h:=Finset.card_pos.mpr hneI; omega
  have hb : 1≤∑ a∈J,(M a).card := by
    have h := Finset.single_le_sum (s := J) (f := fun a => (M a).card)
      (fun a _ => Nat.zero_le _) hjJ
    have hp := Finset.card_pos.mpr hneJ
    omega
  have hcard : (M i).card+(∑ a∈J,(M a).card)=∑ a∈I,(M a).card :=
    Finset.add_sum_erase I (fun a => (M a).card) hi
  have he : realEnergy (M i)+(∑ a∈J,realEnergy (M a))=∑ a∈I,realEnergy (M a) :=
    Finset.add_sum_erase I (fun a => realEnergy (M a)) hi
  have hs := two_strip_energy_minimum (M i).card (∑ a∈J,(M a).card) ha hb
  rw [hcard] at hs
  have hrest := concentration_minimal J M (fun a ha => hM a (Finset.mem_of_mem_erase ha))
  have hsingle := strip_energy_minimal (hM i hi)
  linarith only [hs,hrest,hsingle,he]

theorem three_nonempty_minimum (I : Finset ι) (M : ι → Diagram)
    (hM : ∀ i∈I, IsFerrers (M i)) {i j l : ι} (hi : i∈I) (hj : j∈I) (hl : l∈I)
    (hji : j≠i) (hli : l≠i) (hlj : l≠j)
    (hneI : (M i).Nonempty) (hneJ : (M j).Nonempty) (hneL : (M l).Nonempty) :
    2*realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip ((∑ a∈I,(M a).card)-2))≤
      ∑ a∈I,realEnergy (M a) := by
  let J := I.erase i
  have hjJ : j∈J := Finset.mem_erase.mpr ⟨hji,hj⟩
  have hlJ : l∈J := Finset.mem_erase.mpr ⟨hli,hl⟩
  have ha : 1≤(M i).card := by have h:=Finset.card_pos.mpr hneI; omega
  have hrest := two_nonempty_minimum J M (fun a ha => hM a (Finset.mem_of_mem_erase ha)) hjJ hlJ hlj hneJ hneL
  have hb : 2≤∑ a∈J,(M a).card := by
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun a => (M a).card)
      (show ({j,l} : Finset ι)⊆J by simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]; exact ⟨hjJ,hlJ⟩)
      (fun a _ _ => Nat.zero_le (M a).card)
    rw [Finset.sum_pair hlj.symm] at hsum
    have hpj:=Finset.card_pos.mpr hneJ
    have hpl:=Finset.card_pos.mpr hneL
    omega
  have hcard : (M i).card+(∑ a∈J,(M a).card)=∑ a∈I,(M a).card :=
    Finset.add_sum_erase I (fun a => (M a).card) hi
  have he : realEnergy (M i)+(∑ a∈J,realEnergy (M a))=∑ a∈I,realEnergy (M a) :=
    Finset.add_sum_erase I (fun a => realEnergy (M a)) hi
  have hs := two_strip_energy_minimum (M i).card ((∑ a∈J,(M a).card)-1) ha (by omega)
  rw [show (M i).card+((∑ a∈J,(M a).card)-1)-1=(∑ a∈I,(M a).card)-2 by omega] at hs
  have hsingle := strip_energy_minimal (hM i hi)
  linarith only [hs,hrest,hsingle,he]

theorem not_concentrated_of_two (I : Finset ι) (M : ι → Diagram)
    {i j : ι} (hi : i∈I) (hj : j∈I) (hji : j≠i)
    (hneI : (M i).Nonempty) (hneJ : (M j).Nonempty) : ¬IsConcentrated I M := by
  rintro ⟨c,hc,hne,hstrip,hother⟩
  by_cases hic : i=c
  · have he := hother j hj (by simpa only [← hic] using hji)
    exact hneJ.ne_empty he
  · exact hneI.ne_empty (hother i hi hic)

end
end SpanningTreeIsoperimetry.MulticornerEnergyMinimum
