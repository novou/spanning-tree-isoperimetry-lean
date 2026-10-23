module

public import SpanningTreeIsoperimetry.SmallCornerCorrections

@[expose] public section

/-! Weighted finite-correction lower bounds for the strip pairs in the
small-family table. All sizes are primal side lengths. -/
namespace SpanningTreeIsoperimetry.SmallFamilyStripCorrections
open Ferrers CornerEnergy SmallCornerCorrections
noncomputable section

def weight (r i : ℕ) : ℝ := 1/((r : ℝ)-i)^4

theorem weight_nonneg (r i : ℕ) : 0≤weight r i := by unfold weight; positivity

theorem single_square_weight {r : ℕ} (hr : 2≤r) : (12/5 : ℝ)*weight r 0<single r r := by
  convert single_square_lower hr using 1 <;>
    simp only [weight,Nat.cast_zero,sub_zero,div_eq_mul_inv,mul_inv_rev] <;> ring

theorem single_ordered_weight {r s : ℕ} (hr : 2≤r) (hrs : r≤s) :
    (5/3 : ℝ)*weight r 0<single r s := by
  convert single_ordered_lower hr hrs using 1 <;>
    simp only [weight,Nat.cast_zero,sub_zero,div_eq_mul_inv,mul_inv_rev] <;> ring

theorem square_shift_weight {r i : ℕ} (hi : i+2≤r) :
    (5/3 : ℝ)*weight r i<single r (r-i) := by
  have h := single_lower (by omega : 2≤r) (by omega : 2≤r-i)
  rw [min_eq_right (by omega : r-i≤r),Nat.cast_sub (by omega : i≤r)] at h
  convert h using 1 <;> simp only [weight,div_eq_mul_inv,mul_inv_rev] <;> ring

theorem strip_two_weight {r s : ℕ} (hr : 5≤r) (hs : 3≤s) :
    (21/4 : ℝ)*weight r 0<strip r s 2 := by
  convert strip_two_lower hr hs using 1 <;>
    simp only [weight,Nat.cast_zero,sub_zero,div_eq_mul_inv,mul_inv_rev] <;> ring

theorem square_weight {r s : ℕ} (hr : 5≤r) (hs : 3≤s) :
    (20 : ℝ)*weight r 0<square r s := by
  convert square_lower hr hs using 1 <;>
    simp only [weight,Nat.cast_zero,sub_zero,div_eq_mul_inv,mul_inv_rev] <;> ring

theorem pair_ge_cells (r s p q : ℕ) :
    ((p : ℝ)+q)*single r s≤strip r s p+strip r s q := by
  linarith only [strip_ge_cells r s p,strip_ge_cells r s q]

theorem pair_square_cells {r p q : ℕ} (hr : 2≤r) :
    ((p : ℝ)+q)*(12/5)*weight r 0≤strip r r p+strip r r q := by
  have h := mul_le_mul_of_nonneg_left (single_square_weight hr).le
    (show 0≤(p : ℝ)+q by positivity)
  have hp := pair_ge_cells r r p q
  nlinarith only [h,hp]

theorem pair_ordered_cells {r s p q : ℕ} (hr : 2≤r) (hrs : r≤s) :
    ((p : ℝ)+q)*(5/3)*weight r 0≤strip r s p+strip r s q := by
  have h := mul_le_mul_of_nonneg_left (single_ordered_weight hr hrs).le
    (show 0≤(p : ℝ)+q by positivity)
  have hp := pair_ge_cells r s p q
  nlinarith only [h,hp]

theorem pair_one_two {r s : ℕ} (hr : 5≤r) (hrs : r≤s) :
    (83/12 : ℝ)*weight r 0≤strip r s 1+strip r s 2 := by
  have h1 := single_ordered_weight (by omega : 2≤r) hrs
  have h2 := strip_two_weight hr (by omega : 3≤s)
  rw [strip_one]
  linarith only [h1,h2]

theorem pair_two_two {r s : ℕ} (hr : 5≤r) (hrs : r≤s) :
    (21/2 : ℝ)*weight r 0≤strip r s 2+strip r s 2 := by
  have h2 := strip_two_weight hr (by omega : 3≤s)
  linarith only [h2]

theorem pair_one_three_square {r : ℕ} (hr : 5≤r) :
    (24/5 : ℝ)*weight r 0+(5/3)*(weight r 1+weight r 2)≤strip r r 1+strip r r 3 := by
  have ht := strip_transfer r r (by decide : 1≤3)
  norm_num [Finset.sum_Ico_succ_top,strip_one] at ht
  have h0 := single_square_weight (by omega : 2≤r)
  have h1 := square_shift_weight (r := r) (i := 1) (by omega)
  have h2 := square_shift_weight (r := r) (i := 2) (by omega)
  rw [strip_one]
  linarith only [ht,h0,h1,h2]

theorem pair_one_three_gap_two {r : ℕ} (hr : 5≤r) :
    (559/60 : ℝ)*weight r 0≤strip r (r+2) 1+strip r (r+2) 3 := by
  have ht := strip_transfer r (r+2) (by decide : 2≤3)
  norm_num [Finset.sum_Ico_succ_top] at ht
  have h0 := single_ordered_weight (by omega : 2≤r) (by omega : r≤r+2)
  have h2 := strip_two_weight hr (by omega : 3≤r+2)
  have hs := single_square_weight (by omega : 2≤r)
  rw [strip_one]
  linarith only [ht,h0,h2,hs]

theorem pair_one_four_square {r : ℕ} (hr : 6≤r) :
    (153/20 : ℝ)*weight r 0+(5/3)*weight r 2+(3/4)*weight r 3≤strip r r 1+strip r r 4 := by
  have ht := strip_transfer r r (by decide : 2≤4)
  norm_num [Finset.sum_Ico_succ_top] at ht
  have h0 := single_square_weight (by omega : 2≤r)
  have h2 := strip_two_weight (by omega : 5≤r) (by omega : 3≤r)
  have h3 := square_shift_weight (r := r) (i := 2) (by omega)
  have h4 := square_shift_weight (r := r) (i := 3) (by omega)
  rw [strip_one]
  linarith only [ht,h0,h2,h3,h4,weight_nonneg r 3]

theorem pair_one_four_ordered {r s : ℕ} (hr : 5≤r) (hrs : r≤s) :
    (73/6 : ℝ)*weight r 0≤strip r s 1+strip r s 4 := by
  have h0 := single_ordered_weight (by omega : 2≤r) hrs
  have h2 := strip_two_weight hr (by omega : 3≤s)
  have h4 := strip_four_ge_twice_two r s
  rw [strip_one]
  linarith only [h0,h2,h4]

theorem pair_one_five_square {r : ℕ} (hr : 7≤r) :
    (36/5 : ℝ)*weight r 0+(5/3)*(weight r 1+weight r 2+weight r 3)≤
      strip r r 1+strip r r 5 := by
  have ht := strip_transfer r r (by decide : 1≤5)
  norm_num [Finset.sum_Ico_succ_top,strip_one] at ht
  have h0 := single_square_weight (by omega : 2≤r)
  have h1 := square_shift_weight (r := r) (i := 1) (by omega)
  have h2 := square_shift_weight (r := r) (i := 2) (by omega)
  have h3 := square_shift_weight (r := r) (i := 3) (by omega)
  have h4 := single_shift r r 4
  rw [strip_one]
  linarith only [ht,h0,h1,h2,h3,h4]

end
end SpanningTreeIsoperimetry.SmallFamilyStripCorrections
