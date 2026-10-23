module

public import SpanningTreeIsoperimetry.SummableKernelProduct

@[expose] public section

/-! Multiplication by concrete row/column-summable kernels preserves the
entrywise summable ideal. No ambient operator algebra is assumed. -/
namespace SpanningTreeIsoperimetry.BoundedKernelProduct
open SummableKernelProduct AbsolutelySummableDeterminant
noncomputable section

structure RowBound (B : Kernel) (C : ℝ) : Prop where
  nonneg : 0≤C
  summable : ∀ i,Summable (fun j => |B i j|)
  bound : ∀ i,rowNorm B i≤C

def transpose (A : Kernel) : Kernel := fun i j => A j i
abbrev ColumnBound (B : Kernel) (C : ℝ) := RowBound (transpose B) C

theorem entry_le {B : Kernel} {C : ℝ} (hB : RowBound B C) (i j : ℕ) : |B i j|≤C :=
  ((hB.summable i).le_tsum j (fun _ _ => abs_nonneg _)).trans (hB.bound i)

def tripleNorm (A B : Kernel) (p : (ℕ×ℕ)×ℕ) : ℝ := |A p.1.1 p.1.2| * |B p.1.2 p.2|

def swapLast : (ℕ×ℕ)×ℕ ≃ (ℕ×ℕ)×ℕ where
  toFun p := ((p.1.1,p.2),p.1.2)
  invFun p := ((p.1.1,p.2),p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem weighted_rows_summable {A B : Kernel} (hA : Summable (entryNorm A))
    {C : ℝ} (hB : RowBound B C) :
    Summable (fun p : ℕ×ℕ => |A p.1 p.2| * rowNorm B p.2) := by
  apply Summable.of_nonneg_of_le (fun p => mul_nonneg (abs_nonneg _) (rowNorm_nonneg B p.2))
    (fun p => mul_le_mul_of_nonneg_left (hB.bound p.2) (abs_nonneg _)) (hA.mul_right C)

theorem triple_summable {A B : Kernel} (hA : Summable (entryNorm A))
    {C : ℝ} (hB : RowBound B C) : Summable (tripleNorm A B) := by
  apply (summable_prod_of_nonneg (f := tripleNorm A B)
    (fun p => mul_nonneg (abs_nonneg _) (abs_nonneg _))).mpr
  constructor
  · intro p
    exact (hB.summable p.2).mul_left |A p.1 p.2|
  · simpa only [tripleNorm,tsum_mul_left,rowNorm] using weighted_rows_summable hA hB

def rowProductNorm (A B : Kernel) (i j : ℕ) : ℝ := ∑' k,|A i k| * |B k j|

theorem rowProductNorm_summable {A B : Kernel} (hA : Summable (entryNorm A))
    {C : ℝ} (hB : RowBound B C) :
    Summable (fun p : ℕ×ℕ => rowProductNorm A B p.1 p.2) := by
  have hs := (triple_summable hA hB).comp_injective swapLast.injective
  exact hs.prod

theorem entry_norm_summable {A B : Kernel} (hA : Summable (entryNorm A))
    {C : ℝ} (hB : RowBound B C) (i j : ℕ) :
    Summable (fun k => |A i k*B k j|) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ ((row_summable hA i).mul_right C)
  intro k
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (entry_le hB k j) (abs_nonneg _)

theorem product_abs_le {A B : Kernel} (hA : Summable (entryNorm A))
    {C : ℝ} (hB : RowBound B C) (i j : ℕ) :
    |product A B i j|≤rowProductNorm A B i j := by
  simpa only [product,rowProductNorm,Real.norm_eq_abs,abs_mul] using
    norm_tsum_le_tsum_norm (f := fun k => A i k*B k j)
      (by simpa only [Real.norm_eq_abs] using entry_norm_summable hA hB i j)

theorem right_summable {A B : Kernel} (hA : Summable (entryNorm A))
    {C : ℝ} (hB : RowBound B C) : Summable (entryNorm (product A B)) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun p => product_abs_le hA hB p.1 p.2)
    (rowProductNorm_summable hA hB)

theorem tsum_rowProductNorm {A B : Kernel} (hA : Summable (entryNorm A))
    {C : ℝ} (hB : RowBound B C) :
    (∑' p : ℕ×ℕ,rowProductNorm A B p.1 p.2)=
      ∑' p : ℕ×ℕ,|A p.1 p.2| * rowNorm B p.2 := by
  have hs := triple_summable hA hB
  have ht := hs.comp_injective swapLast.injective
  calc
    _=(∑' q : (ℕ×ℕ)×ℕ,tripleNorm A B (swapLast q)) := ht.tsum_prod.symm
    _=(∑' q : (ℕ×ℕ)×ℕ,tripleNorm A B q) := swapLast.tsum_eq _
    _=(∑' p : ℕ×ℕ,∑' j : ℕ,tripleNorm A B (p,j)) := hs.tsum_prod
    _=_ := by simp only [tripleNorm,tsum_mul_left,rowNorm]

theorem right_mass_le {A B : Kernel} (hA : Summable (entryNorm A))
    {C : ℝ} (hB : RowBound B C) : totalMass (product A B)≤totalMass A*C := by
  let r : ℕ×ℕ → ℝ := fun p => rowProductNorm A B p.1 p.2
  let w : ℕ×ℕ → ℝ := fun p => |A p.1 p.2| * rowNorm B p.2
  let u : ℕ×ℕ → ℝ := fun p => entryNorm A p*C
  have hp : Summable (entryNorm (product A B)) := right_summable hA hB
  have hr : Summable r := rowProductNorm_summable hA hB
  have hw : Summable w := weighted_rows_summable hA hB
  have hu : Summable u := hA.mul_right C
  have hb : totalMass (product A B)≤∑' p : ℕ×ℕ,r p :=
    hp.tsum_le_tsum (g := r) (fun p => product_abs_le hA hB p.1 p.2) hr
  change totalMass (product A B)≤∑' p : ℕ×ℕ,rowProductNorm A B p.1 p.2 at hb
  rw [tsum_rowProductNorm hA hB] at hb
  have hc : (∑' p : ℕ×ℕ,w p)≤∑' p : ℕ×ℕ,u p :=
    hw.tsum_le_tsum (g := u)
      (fun p => mul_le_mul_of_nonneg_left (hB.bound p.2) (abs_nonneg _)) hu
  exact hb.trans (by simpa only [w,u,tsum_mul_right,totalMass,entryNorm] using hc)


theorem transpose_summable {A : Kernel} (hA : Summable (entryNorm A)) :
    Summable (entryNorm (transpose A)) := hA.prod_symm

theorem transpose_mass (A : Kernel) : totalMass (transpose A)=totalMass A :=
  (Equiv.prodComm ℕ ℕ).tsum_eq (entryNorm A)

theorem transpose_product (A B : Kernel) : transpose (product A B)=product (transpose B) (transpose A) := by
  ext i j
  simp only [transpose,product,mul_comm]

theorem transpose_transpose (A : Kernel) : transpose (transpose A)=A := rfl

theorem left_summable {A B : Kernel} {C : ℝ} (hA : ColumnBound A C)
    (hB : Summable (entryNorm B)) : Summable (entryNorm (product A B)) := by
  have hs := transpose_summable (right_summable (transpose_summable hB) hA)
  simpa only [← transpose_product,transpose_transpose] using hs

theorem left_mass_le {A B : Kernel} {C : ℝ} (hA : ColumnBound A C)
    (hB : Summable (entryNorm B)) : totalMass (product A B)≤C*totalMass B := by
  have hb := right_mass_le (transpose_summable hB) hA
  simpa only [← transpose_product,transpose_mass,mul_comm] using hb

end
end SpanningTreeIsoperimetry.BoundedKernelProduct
