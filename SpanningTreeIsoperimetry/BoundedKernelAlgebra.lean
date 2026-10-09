import SpanningTreeIsoperimetry.BoundedKernelProduct

/-! Concrete product bounds and associativity for uniformly row-summable
kernels. All rearrangements are justified by absolute double summability. -/
namespace SpanningTreeIsoperimetry.BoundedKernelAlgebra
open BoundedKernelProduct SummableKernelProduct
noncomputable section

def rowPair (A B : Kernel) (i : ℕ) (p : ℕ×ℕ) : ℝ := |A i p.1| * |B p.1 p.2|

theorem weighted_row_summable {A B : Kernel} {C D : ℝ}
    (hA : RowBound A C) (hB : RowBound B D) (i : ℕ) :
    Summable (fun k => |A i k| * rowNorm B k) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (rowNorm_nonneg B k))
    (fun k => mul_le_mul_of_nonneg_left (hB.bound k) (abs_nonneg _)) ((hA.summable i).mul_right D)

theorem rowPair_summable {A B : Kernel} {C D : ℝ}
    (hA : RowBound A C) (hB : RowBound B D) (i : ℕ) : Summable (rowPair A B i) := by
  apply (summable_prod_of_nonneg (f := rowPair A B i)
    (fun p => mul_nonneg (abs_nonneg _) (abs_nonneg _))).mpr
  constructor
  · intro k
    exact (hB.summable k).mul_left |A i k|
  · simpa only [rowPair,tsum_mul_left,rowNorm] using weighted_row_summable hA hB i

theorem entry_product_summable {A B : Kernel} {C D : ℝ}
    (hA : RowBound A C) (hB : RowBound B D) (i j : ℕ) :
    Summable (fun k => |A i k*B k j|) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ ((hA.summable i).mul_right D)
  intro k
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (entry_le hB k j) (abs_nonneg _)

theorem product_abs_le {A B : Kernel} {C D : ℝ}
    (hA : RowBound A C) (hB : RowBound B D) (i j : ℕ) :
    |product A B i j|≤rowProductNorm A B i j := by
  simpa only [product,rowProductNorm,Real.norm_eq_abs,abs_mul] using
    norm_tsum_le_tsum_norm (f := fun k => A i k*B k j)
      (by simpa only [Real.norm_eq_abs] using entry_product_summable hA hB i j)

theorem product_row_majorant_summable {A B : Kernel} {C D : ℝ}
    (hA : RowBound A C) (hB : RowBound B D) (i : ℕ) :
    Summable (fun j => rowProductNorm A B i j) :=
  (rowPair_summable hA hB i).prod_symm.prod

theorem product_row_summable {A B : Kernel} {C D : ℝ}
    (hA : RowBound A C) (hB : RowBound B D) (i : ℕ) : Summable (fun j => |product A B i j|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (product_abs_le hA hB i)
    (product_row_majorant_summable hA hB i)

theorem sum_product_row_majorant {A B : Kernel} {C D : ℝ}
    (hA : RowBound A C) (hB : RowBound B D) (i : ℕ) :
    (∑' j,rowProductNorm A B i j)=∑' k,|A i k| * rowNorm B k := by
  have hs := rowPair_summable hA hB i
  calc
    _=(∑' p : ℕ×ℕ,rowPair A B i p.swap) := hs.prod_symm.tsum_prod.symm
    _=(∑' p : ℕ×ℕ,rowPair A B i p) := (Equiv.prodComm ℕ ℕ).tsum_eq _
    _=(∑' k,∑' j,rowPair A B i (k,j)) := hs.tsum_prod
    _=_ := by simp only [rowPair,tsum_mul_left,rowNorm]

theorem product_row_bound {A B : Kernel} {C D : ℝ}
    (hA : RowBound A C) (hB : RowBound B D) (i : ℕ) : rowNorm (product A B) i≤C*D := by
  let r : ℕ → ℝ := rowProductNorm A B i
  let w : ℕ → ℝ := fun k => |A i k| * rowNorm B k
  let u : ℕ → ℝ := fun k => |A i k| * D
  have hr : Summable r := product_row_majorant_summable hA hB i
  have hw : Summable w := weighted_row_summable hA hB i
  have hu : Summable u := (hA.summable i).mul_right D
  have he : rowNorm (product A B) i≤∑' j,r j :=
    (product_row_summable hA hB i).tsum_le_tsum (g := r) (product_abs_le hA hB i) hr
  change rowNorm (product A B) i≤∑' j,rowProductNorm A B i j at he
  rw [sum_product_row_majorant hA hB i] at he
  have hb : (∑' k,w k)≤∑' k,u k := hw.tsum_le_tsum (g := u)
    (fun k => mul_le_mul_of_nonneg_left (hB.bound k) (abs_nonneg _)) hu
  have hb' : (∑' k,|A i k| * rowNorm B k)≤rowNorm A i*D := by
    simpa only [w,u,tsum_mul_right,rowNorm] using hb
  exact he.trans (hb'.trans (mul_le_mul_of_nonneg_right (hA.bound i) hB.nonneg))

theorem rowBound_product {A B : Kernel} {C D : ℝ}
    (hA : RowBound A C) (hB : RowBound B D) : RowBound (product A B) (C*D) :=
  ⟨mul_nonneg hA.nonneg hB.nonneg,product_row_summable hA hB,product_row_bound hA hB⟩

theorem triple_entry_summable {A B E : Kernel} {C D F : ℝ}
    (hA : RowBound A C) (hB : RowBound B D) (hE : RowBound E F) (i j : ℕ) :
    Summable (fun p : ℕ×ℕ => (A i p.1*B p.1 p.2)*E p.2 j) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((rowPair_summable hA hB i).mul_right F)
  intro p
  simp only [Real.norm_eq_abs,abs_mul,rowPair]
  exact mul_le_mul_of_nonneg_left (entry_le hE p.2 j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem product_assoc {A B E : Kernel} {C D F : ℝ}
    (hA : RowBound A C) (hB : RowBound B D) (hE : RowBound E F) :
    product (product A B) E=product A (product B E) := by
  ext i j
  let f : ℕ×ℕ → ℝ := fun p => (A i p.1*B p.1 p.2)*E p.2 j
  have hs : Summable f := triple_entry_summable hA hB hE i j
  calc
    product (product A B) E i j=(∑' l,∑' k,f (k,l)) := by
      simp only [product,tsum_mul_right,f]
    _=(∑' p : ℕ×ℕ,f p.swap) := hs.prod_symm.tsum_prod.symm
    _=(∑' p : ℕ×ℕ,f p) := (Equiv.prodComm ℕ ℕ).tsum_eq _
    _=(∑' k,∑' l,f (k,l)) := hs.tsum_prod
    _=product A (product B E) i j := by
      simp only [product,tsum_mul_left,f,mul_assoc]

end
end SpanningTreeIsoperimetry.BoundedKernelAlgebra
