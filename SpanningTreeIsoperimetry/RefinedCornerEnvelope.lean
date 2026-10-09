import SpanningTreeIsoperimetry.RefinedObstructionEnergy_ell
import SpanningTreeIsoperimetry.RefinedObstructionEnergy_square
import SpanningTreeIsoperimetry.RefinedObstructionEnergy_rectangle23
import SpanningTreeIsoperimetry.RefinedObstructionEnergy_rectangle24
import SpanningTreeIsoperimetry.RefinedObstructionEnergy_rectangle25
import SpanningTreeIsoperimetry.RefinedObstructionEnergy_square33
import SpanningTreeIsoperimetry.RefinedObstructionEnergy_tier32
import SpanningTreeIsoperimetry.RefinedObstructionEnergy_tier41
import SpanningTreeIsoperimetry.RefinedObstructionEnergy_tier311
import SpanningTreeIsoperimetry.StripSupportingLines
import SpanningTreeIsoperimetry.CornerConcentration

/-! The refined actual corner-energy envelope. Its numerical inputs are
closed-form actual Green determinants, not hypotheses of the final bound. -/
namespace SpanningTreeIsoperimetry.RefinedCornerEnvelope
open Ferrers CornerEnergy StripRigidity TwoTierFerrers
open RefinedObstructionEnergy RefinedStripEnergy StripSupportingLines
open scoped Classical BigOperators
noncomputable section

def bound (k : ℕ) : ℝ :=
  if k=2 then 5987/100000 else if k=3 then 6714/100000 else
  if k=4 then 5674/100000 else if k=6 then 6522/100000 else
  if k=8 then 7054/100000 else 7421/100000

theorem bound_le_constant (k : ℕ) : bound k≤(7421 : ℝ)/100000 := by
  unfold bound
  split_ifs <;> norm_num

theorem bound_le_ell {k : ℕ} (hk : 2≤k) (hk4 : k≤4) : bound k≤(6714 : ℝ)/100000 := by
  interval_cases k <;> norm_num [bound]

private theorem rectangle_card (r s : ℕ) : (faceRectangle r s).card=r*s := by
  simp [faceRectangle]

private theorem two_row_bound {r : ℕ} (hr : 2≤r) :
    bound (r*2)<realEnergy (faceRectangle r 2) := by
  by_cases hsmall : r≤4
  · interval_cases r
    · norm_num [bound]
      exact square.energy_lower
    · norm_num [bound]
      exact rectangle23.energy_lower
    · norm_num [bound]
      exact rectangle24.energy_lower
  · have hm := rectangle_energy_mono (by decide : 0<5) (by decide : 0<2)
      (show 5≤r by omega) (le_refl 2)
    have hn := rectangle25.energy_lower
    change (7421 : ℝ)/100000<realEnergy (faceRectangle 5 2) at hn
    exact lt_of_le_of_lt (bound_le_constant _) (hn.trans_le hm)

theorem rectangle_bound {r s : ℕ} (hr : 2≤r) (hs : 2≤s) :
    bound (r*s)<realEnergy (faceRectangle r s) := by
  by_cases hr3 : 3≤r
  · by_cases hs3 : 3≤s
    · have hm := rectangle_energy_mono (by decide : 0<3) (by decide : 0<3) hr3 hs3
      have hn := square33.energy_lower
      change (7421 : ℝ)/100000<realEnergy (faceRectangle 3 3) at hn
      exact lt_of_le_of_lt (bound_le_constant _) (hn.trans_le hm)
    · have hse : s=2 := by omega
      subst s
      exact two_row_bound hr
  · have hre : r=2 := by omega
    subst r
    have hh := two_row_bound hs
    rw [← transpose_faceRectangle 2 s,realEnergy_transpose] at hh
    simpa only [Nat.mul_comm] using hh

private theorem rectangle_sides_of_nonstrip {r s : ℕ}
    (hne : (faceRectangle r s).Nonempty) (hn : ¬IsStraightStrip (faceRectangle r s)) :
    2≤r ∧ 2≤s := by
  have hc := Finset.card_pos.mpr hne
  rw [rectangle_card] at hc
  have hr : 0<r := by nlinarith
  have hs : 0<s := by nlinarith
  have hr1 : r≠1 := by
    intro h
    subst r
    apply hn
    right
    simpa only [rectangle_card,one_mul] using rectangle_vertical s
  have hs1 : s≠1 := by
    intro h
    subst s
    apply hn
    left
    simpa only [rectangle_card,mul_one] using rectangle_horizontal r
  omega

private theorem ell_lower : (6714 : ℝ)/100000<realEnergy threeCell := by
  have he : RefinedObstructionPolynomials.ell.diagram=threeCell := by decide +kernel
  norm_num
  simpa only [he] using ell.energy_lower

private theorem nonrectangle_ge_ell {M : Diagram} (hM : IsFerrers M)
    (hne : M.Nonempty) (hr : ¬IsRectangle M) : realEnergy threeCell≤realEnergy M := by
  have hh := realEnergy_threeCell hM hne hr
  have hp : 0≤((maximalCells M).card-2 : ℕ)*realEnergy {(0,0)} :=
    mul_nonneg (Nat.cast_nonneg _) (realEnergy_nonneg _)
  linarith

theorem nonstrip_absolute_lower {M : Diagram} (hM : IsFerrers M)
    (hn : ¬IsStraightStrip M) : (5674 : ℝ)/100000<realEnergy M := by
  have hne := nonempty_of_not_straight hn
  by_cases hr : IsRectangle M
  · obtain ⟨r,s,he⟩ := hr
    change M=faceRectangle r s at he
    subst M
    obtain ⟨hr2,hs2⟩ := rectangle_sides_of_nonstrip hne hn
    have hm := rectangle_energy_mono (by decide : 0<2) (by decide : 0<2) hr2 hs2
    norm_num
    exact square.energy_lower.trans_le hm
  · linarith [ell_lower,nonrectangle_ge_ell hM hne hr]

theorem single_nonstrip_bound {M : Diagram} (hM : IsFerrers M) (hk : 2≤M.card)
    (hn : ¬IsStraightStrip M) : bound M.card<realEnergy M := by
  have hne := nonempty_of_not_straight hn
  by_cases hr : IsRectangle M
  · obtain ⟨r,s,he⟩ := hr
    change M=faceRectangle r s at he
    subst M
    obtain ⟨hr2,hs2⟩ := rectangle_sides_of_nonstrip hne hn
    rw [rectangle_card]
    exact rectangle_bound hr2 hs2
  by_cases hmax : 3≤(maximalCells M).card
  · have hm := realEnergy_maximalCells M
    have he : realEnergy {(0,0)}=realEnergy (horizontalStrip 1) := by congr 1
    rw [he] at hm
    have h3 : (3 : ℝ)≤(maximalCells M).card := by exact_mod_cast hmax
    have hp := mul_le_mul_of_nonneg_right h3 (realEnergy_nonneg (horizontalStrip 1))
    linarith [(strip_energy_bounds_1).1,bound_le_constant M.card]
  by_cases hsize : 5≤M.card
  · have hc : (maximalCells M).card=2 := by
      have hh := two_le_maximal_card_of_nonrectangle hM hne hr
      omega
    rcases two_maxima_large_seed_bound hM hc hsize with hh|hh|hh
    · have hl := tier32.energy_lower
      change (7421 : ℝ)/100000<realEnergy (twoTier 2 1 1 1) at hl
      exact lt_of_le_of_lt (bound_le_constant _) (hl.trans_le hh)
    · have hl := tier41.energy_lower
      change (7421 : ℝ)/100000<realEnergy (twoTier 1 3 1 1) at hl
      exact lt_of_le_of_lt (bound_le_constant _) (hl.trans_le hh)
    · have hl := tier311.energy_lower
      change (7421 : ℝ)/100000<realEnergy (twoTier 1 2 1 2) at hl
      exact lt_of_le_of_lt (bound_le_constant _) (hl.trans_le hh)
  · exact lt_of_le_of_lt (bound_le_ell hk (by omega))
      (ell_lower.trans_le (nonrectangle_ge_ell hM hne hr))

theorem nonempty_energy_lower {M : Diagram} (hM : IsFerrers M) (hne : M.Nonempty) :
    realEnergy (horizontalStrip 1)≤realEnergy M :=
  (realEnergy_strip_monotone (show 1≤M.card by have hh:=Finset.card_pos.mpr hne; omega)).trans
    (strip_energy_minimal hM)

theorem two_strip_bound {a b : ℕ} (ha : 1≤a) (hb : 1≤b) :
    bound (a+b)<realEnergy (horizontalStrip a)+realEnergy (horizontalStrip b) := by
  have hm := two_strip_energy_minimum a b ha hb
  have hk2 : 2≤a+b := by omega
  by_cases hk5 : 5≤a+b
  · have h4 := realEnergy_strip_monotone (show 4≤a+b-1 by omega)
    linarith [bound_le_constant (a+b),(strip_energy_bounds_1).1,(strip_energy_bounds_4).1]
  · generalize he : a+b=k at *
    interval_cases k <;> norm_num [bound] at hm ⊢ <;>
      linarith [(strip_energy_bounds_1).1,(strip_energy_bounds_2).1,(strip_energy_bounds_3).1]

theorem two_nonempty_bound {M N : Diagram} (hM : IsFerrers M) (hN : IsFerrers N)
    (hm : M.Nonempty) (hn : N.Nonempty) :
    bound (M.card+N.card)<realEnergy M+realEnergy N := by
  by_cases hms : IsStraightStrip M
  · by_cases hns : IsStraightStrip N
    · rw [straight_energy hms,straight_energy hns]
      exact two_strip_bound (by have hh:=Finset.card_pos.mpr hm; omega)
        (by have hh:=Finset.card_pos.mpr hn; omega)
    · have hl := nonstrip_absolute_lower hN hns
      have hm' := nonempty_energy_lower hM hm
      linarith [bound_le_constant (M.card+N.card),(strip_energy_bounds_1).1]
  · have hl := nonstrip_absolute_lower hM hms
    have hn' := nonempty_energy_lower hN hn
    linarith [bound_le_constant (M.card+N.card),(strip_energy_bounds_1).1]

/-- The refined envelope for every finite family, hence in particular the
four geometric corners. No energy or numerical premise is left unproved. -/
theorem family_bound {ι : Type*} [DecidableEq ι] (I : Finset ι) (M : ι → Diagram)
    (hM : ∀ i∈I, IsFerrers (M i)) (hk : 2≤∑ i∈I,(M i).card)
    (hn : ¬CornerConcentration.IsConcentrated I M) :
    bound (∑ i∈I,(M i).card)<∑ i∈I,realEnergy (M i) := by
  let S := I.filter (fun i => M i≠∅)
  have hSI : S⊆I := Finset.filter_subset _ _
  have hne (i) (hi : i∈S) : (M i).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (Finset.mem_filter.mp hi).2
  have hzero (i) (hi : i∈I) (hni : i∉S) : M i=∅ := by
    by_contra hh
    exact hni (Finset.mem_filter.mpr ⟨hi,hh⟩)
  have hsE : (∑ i∈S,realEnergy (M i))=∑ i∈I,realEnergy (M i) := by
    apply Finset.sum_subset hSI
    intro i hi hni
    rw [hzero i hi hni,realEnergy_empty]
  have hsK : (∑ i∈S,(M i).card)=∑ i∈I,(M i).card := by
    apply Finset.sum_subset hSI
    intro i hi hni
    rw [hzero i hi hni]
    rfl
  have hspos : 0<S.card := by
    by_contra hh
    have hs0 : S=∅ := Finset.card_eq_zero.mp (by omega)
    rw [hs0,Finset.sum_empty] at hsK
    omega
  by_cases hs3 : 3≤S.card
  · have hb := Finset.sum_le_sum (fun i hi => nonempty_energy_lower (hM i (hSI hi)) (hne i hi))
    simp only [Finset.sum_const,nsmul_eq_mul] at hb
    rw [hsE] at hb
    have h3 : (3 : ℝ)≤S.card := by exact_mod_cast hs3
    have hm := mul_le_mul_of_nonneg_right h3 (realEnergy_nonneg (horizontalStrip 1))
    linarith [bound_le_constant (∑ i∈I,(M i).card),(strip_energy_bounds_1).1]
  by_cases hs2 : S.card=2
  · obtain ⟨i,j,hij,hS⟩ := Finset.card_eq_two.mp hs2
    have hi : i∈S := by rw [hS]; simp
    have hj : j∈S := by rw [hS]; simp
    have hh := two_nonempty_bound (hM i (hSI hi)) (hM j (hSI hj)) (hne i hi) (hne j hj)
    rw [hS,Finset.sum_pair hij] at hsE hsK
    simpa only [hsE,hsK] using hh
  · have hs1 : S.card=1 := by omega
    obtain ⟨i,hS⟩ := Finset.card_eq_one.mp hs1
    have hi : i∈S := by rw [hS]; simp
    have ho (j) (hj : j∈I) (hji : j≠i) : M j=∅ := by
      apply hzero j hj
      rw [hS,Finset.mem_singleton]
      exact hji
    have hns : ¬IsStraightStrip (M i) := by
      intro hh
      exact hn ⟨i,hSI hi,hne i hi,hh,ho⟩
    rw [hS,Finset.sum_singleton] at hsE hsK
    have hh := single_nonstrip_bound (hM i (hSI hi)) (show 2≤(M i).card by omega) hns
    simpa only [hsE,hsK] using hh

end
end SpanningTreeIsoperimetry.RefinedCornerEnvelope
