module

public import SpanningTreeIsoperimetry.ToeplitzHankelKernels
public import SpanningTreeIsoperimetry.SummableKernelTrace

@[expose] public section

/-! The actual linear and quadratic trace constants for weighted Laurent
coefficients. Only summable differences and Hankel products are traced;
individual nonsummable Toeplitz kernels are never assigned finite traces. -/
namespace SpanningTreeIsoperimetry.ToeplitzHankelTraceConstants
open ToeplitzHankelKernels SummableKernelProduct SummableKernelTrace
open AbsolutelySummableDeterminant
open scoped BigOperators
noncomputable section

theorem M_sub_T_eq (a : Laurent) : M a-T a= -Hshift a := by
  ext i j
  change (T a i j-Hshift a i j)-T a i j= -Hshift a i j
  ring

theorem M_sub_T_summable {a : Laurent} (ha : WeightedSummable a) :
    Summable (entryNorm (M a-T a)) := by
  rw [M_sub_T_eq]
  have h := Hshift_summable ha
  change Summable (fun p : ℕ×ℕ => |Hshift a p.1 p.2|) at h
  change Summable (fun p : ℕ×ℕ => |-Hshift a p.1 p.2|)
  simpa only [abs_neg] using h

theorem trace_M_sub_T {a : Laurent} (_ha : WeightedSummable a) :
    trace (M a-T a)= -(∑' n : ℕ,a ((2*(n+1) : ℕ) : ℤ)) := by
  rw [M_sub_T_eq]
  unfold trace
  rw [← tsum_neg]
  apply tsum_congr
  intro n
  have hn : n+n+2=2*(n+1) := by omega
  simp only [Pi.neg_apply,Hshift,hankelOffset,hn]

def pairSquare (a : Laurent) (p : ℕ×ℕ) : ℝ := a ((p.1+p.2+1 : ℕ) : ℤ)^2

theorem weighted_square_summable {a : Laurent} (ha : WeightedSummable a) :
    Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)*a ((n+1 : ℕ) : ℤ)^2) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _
    ((weighted_tail_summable ha 1).mul_right (mass a))
  intro n
  have hb := abs_le_mass (summable_abs ha) ((n+1 : ℕ) : ℤ)
  have hs : a ((n+1 : ℕ) : ℤ)^2≤|a ((n+1 : ℕ) : ℤ)| *mass a := by
    calc
      _=|a ((n+1 : ℕ) : ℤ)| *|a ((n+1 : ℕ) : ℤ)| := by rw [← pow_two,sq_abs]
      _≤_ := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (n+1))

theorem antidiagonal_square_sum (a : Laurent) (n : ℕ) :
    (∑ p∈Finset.antidiagonal n,pairSquare a p)=((n+1 : ℕ) : ℝ)*a ((n+1 : ℕ) : ℤ)^2 := by
  have he : (∑ p∈Finset.antidiagonal n,pairSquare a p)=
      ∑ _p∈Finset.antidiagonal n,a ((n+1 : ℕ) : ℤ)^2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [pairSquare,Finset.mem_antidiagonal.mp hp]
  rw [he,Finset.sum_const,Finset.Nat.card_antidiagonal,nsmul_eq_mul]

theorem pairSquare_summable {a : Laurent} (ha : WeightedSummable a) : Summable (pairSquare a) := by
  have hs : Summable (fun p : Σ n : ℕ,Finset.antidiagonal n => pairSquare a p.2.val) := by
    apply (summable_sigma_of_nonneg
      (f := fun p : Σ n : ℕ,Finset.antidiagonal n => pairSquare a p.2.val)
      (fun p => sq_nonneg _)).mpr
    constructor
    · intro n
      exact (hasSum_fintype _).summable
    · simpa only [tsum_fintype,Finset.sum_coe_sort,antidiagonal_square_sum] using weighted_square_summable ha
  exact Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mp hs

theorem pairSquare_tsum {a : Laurent} (ha : WeightedSummable a) :
    (∑' p : ℕ×ℕ,pairSquare a p)=∑' n : ℕ,((n+1 : ℕ) : ℝ)*a ((n+1 : ℕ) : ℤ)^2 := by
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq (pairSquare a)]
  have hs := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr (pairSquare_summable ha)
  change (∑' p : Σ n : ℕ,Finset.antidiagonal n,pairSquare a p.2.val)=_
  have hs' : Summable (fun p : Σ n : ℕ,Finset.antidiagonal n => pairSquare a p.2.val) := hs
  rw [hs'.tsum_sigma' (fun n => (hasSum_fintype _).summable)]
  simp only [tsum_fintype,Finset.sum_coe_sort,antidiagonal_square_sum]

theorem H_product_summable {a : Laurent} (ha : WeightedSummable a) :
    Summable (entryNorm (product (H a) (H a))) := product_summable (H_summable ha) (H_summable ha)

/-- The actual infinite Hankel-square trace, with Fubini justified by the
proved absolute pair sum and the antidiagonal multiplicity n+1. -/
theorem trace_H_product {a : Laurent} (ha : WeightedSummable a) :
    trace (product (H a) (H a))=∑' n : ℕ,((n+1 : ℕ) : ℝ)*a ((n+1 : ℕ) : ℤ)^2 := by
  calc
    trace (product (H a) (H a))=∑' i : ℕ,∑' j : ℕ,pairSquare a (i,j) := by
      unfold trace product
      apply tsum_congr
      intro i
      apply tsum_congr
      intro j
      simp only [H,hankelOffset,pairSquare,Prod.fst,Prod.snd,Nat.add_comm,pow_two]
    _=(∑' p : ℕ×ℕ,pairSquare a p) := (pairSquare_summable ha).tsum_prod.symm
    _=_ := pairSquare_tsum ha

end
end SpanningTreeIsoperimetry.ToeplitzHankelTraceConstants
