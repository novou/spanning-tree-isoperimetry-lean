module

public import SpanningTreeIsoperimetry.BoundedKernelProduct
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

/-! Actual Toeplitz and Hankel kernels of weighted absolutely summable
real Laurent coefficients. Integer differences are never truncated. -/
namespace SpanningTreeIsoperimetry.ToeplitzHankelKernels
open AbsolutelySummableDeterminant SummableKernelProduct BoundedKernelProduct
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev Laurent := ℤ → ℝ
def weightedTerm (a : Laurent) (n : ℤ) : ℝ := (1+(n.natAbs : ℝ))*|a n|
abbrev WeightedSummable (a : Laurent) : Prop := Summable (weightedTerm a)
def mass (a : Laurent) : ℝ := ∑' n : ℤ,|a n|
def weightedMass (a : Laurent) : ℝ := ∑' n : ℤ,weightedTerm a n
def flip (a : Laurent) : Laurent := fun n => a (-n)

def T (a : Laurent) : Kernel := fun i j => a ((i : ℤ)-j)
def hankelOffset (a : Laurent) (d : ℕ) : Kernel := fun i j => a ((i+j+d : ℕ) : ℤ)
def H (a : Laurent) : Kernel := hankelOffset a 1
def Hshift (a : Laurent) : Kernel := hankelOffset a 2
def M (a : Laurent) : Kernel := T a-Hshift a

theorem weightedTerm_nonneg (a : Laurent) (n : ℤ) : 0≤weightedTerm a n := by
  unfold weightedTerm
  positivity

theorem mass_nonneg (a : Laurent) : 0≤mass a := tsum_nonneg (fun _ => abs_nonneg _)

theorem summable_abs {a : Laurent} (ha : WeightedSummable a) : Summable (fun n : ℤ => |a n|) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ ha
  intro n
  unfold weightedTerm
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n.natAbs) (abs_nonneg (a n))]

theorem abs_le_mass {a : Laurent} (ha : Summable (fun n => |a n|)) (n : ℤ) : |a n|≤mass a :=
  ha.le_tsum n (fun _ _ => abs_nonneg _)

theorem weighted_flip {a : Laurent} (ha : WeightedSummable a) : WeightedSummable (flip a) := by
  have hs := ha.comp_injective (show Function.Injective (fun n : ℤ => -n) from neg_injective)
  change Summable (fun n : ℤ => (1+(n.natAbs : ℝ))*|a (-n)|)
  simpa only [weightedTerm,Function.comp_def,Int.natAbs_neg] using hs

theorem rowBound_T {a : Laurent} (ha : Summable (fun n => |a n|)) : RowBound (T a) (mass a) := by
  refine ⟨mass_nonneg a,?_,?_⟩
  · intro i
    exact ha.comp_injective (show Function.Injective (fun j : ℕ => (i : ℤ)-j) by
      intro j k h; dsimp only at h; omega)
  · intro i
    exact tsum_comp_le_tsum_of_inj ha (fun _ => abs_nonneg _)
      (show Function.Injective (fun j : ℕ => (i : ℤ)-j) by intro j k h; dsimp only at h; omega)

theorem columnBound_T {a : Laurent} (ha : Summable (fun n => |a n|)) : ColumnBound (T a) (mass a) := by
  refine ⟨mass_nonneg a,?_,?_⟩
  · intro i
    exact ha.comp_injective (show Function.Injective (fun j : ℕ => (j : ℤ)-i) by
      intro j k h; dsimp only at h; omega)
  · intro i
    exact tsum_comp_le_tsum_of_inj ha (fun _ => abs_nonneg _)
      (show Function.Injective (fun j : ℕ => (j : ℤ)-i) by intro j k h; dsimp only at h; omega)

theorem rowBound_hankelOffset {a : Laurent} (ha : Summable (fun n => |a n|)) (d : ℕ) :
    RowBound (hankelOffset a d) (mass a) := by
  refine ⟨mass_nonneg a,?_,?_⟩
  · intro i
    exact ha.comp_injective (show Function.Injective (fun j : ℕ => ((i+j+d : ℕ) : ℤ)) by
      intro j k h; dsimp only at h; omega)
  · intro i
    exact tsum_comp_le_tsum_of_inj ha (fun _ => abs_nonneg _)
      (show Function.Injective (fun j : ℕ => ((i+j+d : ℕ) : ℤ)) by intro j k h; dsimp only at h; omega)

theorem columnBound_hankelOffset {a : Laurent} (ha : Summable (fun n => |a n|)) (d : ℕ) :
    ColumnBound (hankelOffset a d) (mass a) := by
  have he : transpose (hankelOffset a d)=hankelOffset a d := by
    ext i j
    simp [transpose,hankelOffset,Nat.add_comm]
  change RowBound (transpose (hankelOffset a d)) (mass a)
  rw [he]
  exact rowBound_hankelOffset ha d

theorem rowBound_H {a : Laurent} (ha : Summable (fun n => |a n|)) : RowBound (H a) (mass a) :=
  rowBound_hankelOffset ha 1
theorem columnBound_H {a : Laurent} (ha : Summable (fun n => |a n|)) : ColumnBound (H a) (mass a) :=
  columnBound_hankelOffset ha 1
theorem rowBound_Hshift {a : Laurent} (ha : Summable (fun n => |a n|)) : RowBound (Hshift a) (mass a) :=
  rowBound_hankelOffset ha 2
theorem columnBound_Hshift {a : Laurent} (ha : Summable (fun n => |a n|)) : ColumnBound (Hshift a) (mass a) :=
  columnBound_hankelOffset ha 2

private theorem sub_rowBound {A B : Kernel} {C D : ℝ} (hA : RowBound A C) (hB : RowBound B D) :
    RowBound (A-B) (C+D) := by
  have hbound (i j : ℕ) : |A i j-B i j|≤|A i j|+|B i j| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (A i j) (-B i j)
  have hs (i : ℕ) : Summable (fun j => |A i j-B i j|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (hbound i)
      ((hA.summable i).add (hB.summable i))
  refine ⟨add_nonneg hA.nonneg hB.nonneg,hs,?_⟩
  intro i
  have hb := (hs i).tsum_le_tsum (hbound i)
    ((hA.summable i).add (hB.summable i))
  rw [(hA.summable i).tsum_add (hB.summable i)] at hb
  exact hb.trans (add_le_add (hA.bound i) (hB.bound i))

theorem rowBound_M {a : Laurent} (ha : Summable (fun n => |a n|)) : RowBound (M a) (2*mass a) := by
  simpa only [M,two_mul] using sub_rowBound (rowBound_T ha) (rowBound_Hshift ha)

theorem columnBound_M {a : Laurent} (ha : Summable (fun n => |a n|)) : ColumnBound (M a) (2*mass a) := by
  have he : transpose (M a)=transpose (T a)-transpose (Hshift a) := rfl
  change RowBound (transpose (M a)) (2*mass a)
  rw [he,two_mul]
  exact sub_rowBound (columnBound_T ha) (columnBound_Hshift ha)

theorem weighted_tail_summable {a : Laurent} (ha : WeightedSummable a) (d : ℕ) :
    Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)*|a ((n+d : ℕ) : ℤ)|) := by
  have hs := ha.comp_injective (show Function.Injective (fun n : ℕ => ((n+d : ℕ) : ℤ)) by
    intro m n h; dsimp only at h; omega)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
  intro n
  simp only [Function.comp_def,weightedTerm,Int.natAbs_natCast]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  exact_mod_cast (show n+1≤1+(n+d) by omega)

theorem antidiagonal_entry_sum (a : Laurent) (d n : ℕ) :
    (∑ p∈Finset.antidiagonal n,entryNorm (hankelOffset a d) p)=
      ((n+1 : ℕ) : ℝ)*|a ((n+d : ℕ) : ℤ)| := by
  have he : (∑ p∈Finset.antidiagonal n,entryNorm (hankelOffset a d) p)=
      ∑ _p∈Finset.antidiagonal n,|a ((n+d : ℕ) : ℤ)| := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [entryNorm,hankelOffset,Finset.mem_antidiagonal.mp hp]
  rw [he,Finset.sum_const,Finset.Nat.card_antidiagonal,nsmul_eq_mul]

theorem hankelOffset_summable {a : Laurent} (ha : WeightedSummable a) (d : ℕ) :
    Summable (entryNorm (hankelOffset a d)) := by
  have hs : Summable (fun p : Σ n : ℕ,Finset.antidiagonal n => entryNorm (hankelOffset a d) p.2.val) := by
    apply (summable_sigma_of_nonneg
      (f := fun p : Σ n : ℕ,Finset.antidiagonal n => entryNorm (hankelOffset a d) p.2.val)
      (fun p => abs_nonneg (hankelOffset a d p.2.val.1 p.2.val.2))).mpr
    constructor
    · intro n
      exact (hasSum_fintype _).summable
    · simpa only [tsum_fintype,Finset.sum_coe_sort,antidiagonal_entry_sum] using weighted_tail_summable ha d
  exact Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mp hs

theorem hankelOffset_mass {a : Laurent} (ha : WeightedSummable a) (d : ℕ) :
    totalMass (hankelOffset a d)=∑' n : ℕ,((n+1 : ℕ) : ℝ)*|a ((n+d : ℕ) : ℤ)| := by
  change (∑' p : ℕ×ℕ,entryNorm (hankelOffset a d) p)=_
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq (entryNorm (hankelOffset a d))]
  have hs := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr (hankelOffset_summable ha d)
  change (∑' p : Σ n : ℕ,Finset.antidiagonal n,entryNorm (hankelOffset a d) p.2.val)=_
  have hs' : Summable (fun p : Σ n : ℕ,Finset.antidiagonal n => entryNorm (hankelOffset a d) p.2.val) := hs
  rw [hs'.tsum_sigma' (fun n => (hasSum_fintype _).summable)]
  simp only [tsum_fintype,Finset.sum_coe_sort,antidiagonal_entry_sum]

theorem H_summable {a : Laurent} (ha : WeightedSummable a) : Summable (entryNorm (H a)) :=
  hankelOffset_summable ha 1
theorem Hshift_summable {a : Laurent} (ha : WeightedSummable a) : Summable (entryNorm (Hshift a)) :=
  hankelOffset_summable ha 2

end
end SpanningTreeIsoperimetry.ToeplitzHankelKernels
