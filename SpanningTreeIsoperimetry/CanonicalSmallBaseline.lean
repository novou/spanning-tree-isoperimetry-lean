module

public import SpanningTreeIsoperimetry.RefinedSmallEnergyUpper
public import SpanningTreeIsoperimetry.StripSupportingLines
public import SpanningTreeIsoperimetry.SmallShapeCatalogue
public import SpanningTreeIsoperimetry.CornerConcentration
public import SpanningTreeIsoperimetry.CornerPrimalDomains

@[expose] public section

/-! Exact quadrant-energy baselines for every nonconcentrated family of
size two, three, or four. The square comparison retains its actual energy. -/
namespace SpanningTreeIsoperimetry.CanonicalSmallBaseline
open Ferrers CornerEnergy CornerPrimalDomains CornerConcentration StripRigidity
  RefinedSmallEnergyUpper RefinedStripEnergy
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def support (M : Corner → Diagram) : Finset Corner := Finset.univ.filter (fun c => M c≠∅)

theorem support_nonempty {M : Corner → Diagram} {c : Corner} (hc : c∈support M) : (M c).Nonempty :=
  Finset.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp hc).2

theorem outside_support {M : Corner → Diagram} {c : Corner} (hc : c∉support M) : M c=∅ := by
  by_contra h
  exact hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)

theorem support_energy (M : Corner → Diagram) : (∑ c∈support M,realEnergy (M c))=∑ c,realEnergy (M c) := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro c hc hn
  rw [outside_support hn,realEnergy_empty]

theorem support_size (M : Corner → Diagram) : (∑ c∈support M,(M c).card)=totalDefect M := by
  change (∑ c∈support M,(M c).card)=∑ c : Corner,(M c).card
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro c hc hn
  rw [outside_support hn]
  rfl

theorem support_card_le_total (M : Corner → Diagram) : (support M).card≤totalDefect M := by
  have h := Finset.sum_le_sum (s := support M) (fun c hc =>
    show 1≤(M c).card by have hp:=Finset.card_pos.mpr (support_nonempty hc); omega)
  have hc : (∑ _c∈support M, (1 : ℕ))=(support M).card := by simp
  rw [hc,support_size] at h
  exact h

theorem support_pos {M : Corner → Diagram} (hk : 0<totalDefect M) : 0<(support M).card := by
  by_contra hn
  have he : support M=∅ := Finset.card_eq_zero.mp (by omega)
  have h := support_size M
  rw [he,Finset.sum_empty] at h
  omega

theorem one_support_nonstrip {M : Corner → Diagram} (hn : ¬IsConcentrated Finset.univ M)
    (hs : (support M).card=1) :
    ∃ c, (M c).Nonempty ∧ ¬IsStraightStrip (M c) ∧
      totalDefect M=(M c).card ∧ (∑ d,realEnergy (M d))=realEnergy (M c) := by
  obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hs
  have hmem : c∈support M := by rw [hc]; simp
  have he := support_energy M
  have hk := support_size M
  rw [hc,Finset.sum_singleton] at he hk
  refine ⟨c,support_nonempty hmem,?_,hk.symm,he.symm⟩
  intro hstrip
  apply hn
  refine ⟨c,Finset.mem_univ _,support_nonempty hmem,hstrip,?_⟩
  intro d hd hdc
  apply outside_support
  rw [hc,Finset.mem_singleton]
  exact hdc

theorem total_one_concentrated {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c))
    (hk : totalDefect M=1) : IsConcentrated Finset.univ M := by
  by_contra hn
  have hp := support_pos (M := M) (by omega)
  have hle := support_card_le_total M
  obtain ⟨c,hne,hns,hcard,he⟩ := one_support_nonstrip hn (by omega)
  exact hns (SmallShapeCatalogue.ferrers_two_cell_strip (hM c) (by omega))

theorem support_energy_lower {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c)) :
    ((support M).card : ℝ)*realEnergy (horizontalStrip 1)≤∑ c,realEnergy (M c) := by
  have hs := Finset.sum_le_sum (s := support M) (fun c hc =>
    (realEnergy_strip_monotone (show 1≤(M c).card by have h:=Finset.card_pos.mpr (support_nonempty hc); omega)).trans
      (strip_energy_minimal (hM c)))
  simpa only [Finset.sum_const,nsmul_eq_mul,support_energy] using hs

theorem nonstrip_ge_square {M : Diagram} (hM : IsFerrers M) (hn : ¬IsStraightStrip M) :
    realEnergy (faceRectangle 2 2)≤realEnergy M := by
  have hne := nonempty_of_not_straight hn
  by_cases hr : IsRectangle M
  · obtain ⟨r,s,he⟩ := hr
    change M=faceRectangle r s at he
    subst M
    have hc : 0<r*s := by simpa [faceRectangle] using Finset.card_pos.mpr hne
    have hr0 : 0<r := by nlinarith
    have hs0 : 0<s := by nlinarith
    have hr1 : r≠1 := by
      intro h
      subst r
      apply hn
      right
      simpa [faceRectangle] using rectangle_vertical s
    have hs1 : s≠1 := by
      intro h
      subst s
      apply hn
      left
      simpa [faceRectangle] using rectangle_horizontal r
    exact rectangle_energy_mono (by norm_num : 0<2) (by norm_num : 0<2) (by omega) (by omega)
  · have hh := realEnergy_threeCell hM hne hr
    have hnon : 0≤((maximalCells M).card-2 : ℕ)*realEnergy {(0,0)} :=
      mul_nonneg (Nat.cast_nonneg _) (realEnergy_nonneg _)
    linarith [ThreeCellEnergy.realEnergy_ell_gt,square_energy_upper]

theorem family_two_baseline {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c))
    (hk : totalDefect M=2) (hn : ¬IsConcentrated Finset.univ M) :
    2*realEnergy (horizontalStrip 1)≤∑ c,realEnergy (M c) := by
  have hp := support_pos (M := M) (by omega)
  have hs : 2≤(support M).card := by
    by_contra hh
    obtain ⟨c,hne,hns,hcard,henergy⟩ := one_support_nonstrip hn (by omega)
    exact hns (SmallShapeCatalogue.ferrers_two_cell_strip (hM c) (by omega))
  have hm := mul_le_mul_of_nonneg_right (show (2 : ℝ)≤(support M).card by exact_mod_cast hs)
    (realEnergy_nonneg (horizontalStrip 1))
  exact hm.trans (support_energy_lower hM)

theorem family_three_baseline {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c))
    (hk : totalDefect M=3) (hn : ¬IsConcentrated Finset.univ M) :
    realEnergy threeCell≤∑ c,realEnergy (M c) := by
  have hp := support_pos (M := M) (by omega)
  by_cases hs3 : 3≤(support M).card
  · have hm := mul_le_mul_of_nonneg_right (show (3 : ℝ)≤(support M).card by exact_mod_cast hs3)
      (realEnergy_nonneg (horizontalStrip 1))
    have hb := hm.trans (support_energy_lower hM)
    linarith [ell_energy_upper,(strip_energy_bounds_1).1]
  · by_cases hs2 : (support M).card=2
    · obtain ⟨c,d,hcd,hs⟩ := Finset.card_eq_two.mp hs2
      have hc : c∈support M := by rw [hs]; simp
      have hd : d∈support M := by rw [hs]; simp
      have he := support_energy M
      have hcard := support_size M
      rw [hs,Finset.sum_pair hcd] at he hcard
      have hsplit := StripSupportingLines.two_strip_energy_minimum (M c).card (M d).card
        (by have h:=Finset.card_pos.mpr (support_nonempty hc); omega)
        (by have h:=Finset.card_pos.mpr (support_nonempty hd); omega)
      rw [show (M c).card+(M d).card-1=2 by omega] at hsplit
      linarith [strip_energy_minimal (hM c),strip_energy_minimal (hM d),ell_lt_singleton_pair]
    · obtain ⟨c,hne,hns,hcard,he⟩ := one_support_nonstrip hn (by omega)
      obtain hstrip|hell := SmallShapeCatalogue.ferrers_three_cell_catalogue (hM c) (by omega)
      · exact False.elim (hns hstrip)
      · rw [he,hell]

theorem family_four_baseline {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c))
    (hk : totalDefect M=4) (hn : ¬IsConcentrated Finset.univ M) :
    realEnergy (faceRectangle 2 2)≤∑ c,realEnergy (M c) := by
  have hp := support_pos (M := M) (by omega)
  by_cases hs2 : 2≤(support M).card
  · have hm := mul_le_mul_of_nonneg_right (show (2 : ℝ)≤(support M).card by exact_mod_cast hs2)
      (realEnergy_nonneg (horizontalStrip 1))
    have hb := hm.trans (support_energy_lower hM)
    linarith [square_energy_upper,(strip_energy_bounds_1).1]
  · obtain ⟨c,hne,hns,hcard,he⟩ := one_support_nonstrip hn (by omega)
    rw [he]
    exact nonstrip_ge_square (hM c) hns

end
end SpanningTreeIsoperimetry.CanonicalSmallBaseline
