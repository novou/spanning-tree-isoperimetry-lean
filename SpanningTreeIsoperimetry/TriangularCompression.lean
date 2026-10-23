module

public import SpanningTreeIsoperimetry.SummableKernelProduct
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

/-! Exact finite compression through a lower triangular factor on the left
and an upper triangular factor on the right. Infinite sums truncate exactly. -/
namespace SpanningTreeIsoperimetry.TriangularCompression
open SummableKernelProduct FiniteSectionPadding
open scoped BigOperators
noncomputable section

def Lower (L : Kernel) : Prop := ∀ i j : ℕ, i < j → L i j = 0
def Upper (U : Kernel) : Prop := ∀ i j : ℕ, j < i → U i j = 0

theorem lower_compression {L : Kernel} (hL : Lower L) (M : Kernel) (n : ℕ) :
    finiteSection (product L M) n=finiteSection L n*finiteSection M n := by
  ext i j
  simp only [finiteSection,product,Matrix.mul_apply]
  have he : (∑' k : ℕ,L i.val k*M k j.val)=∑ k∈Finset.range n,L i.val k*M k j.val := by
    apply tsum_eq_sum
    intro k hk
    have hk' : n≤k := by simpa only [Finset.mem_range,not_lt] using hk
    rw [hL i.val k (by have hi := i.isLt; omega),zero_mul]
  rw [he,← Fin.sum_univ_eq_sum_range]

theorem upper_compression {U : Kernel} (hU : Upper U) (M : Kernel) (n : ℕ) :
    finiteSection (product M U) n=finiteSection M n*finiteSection U n := by
  ext i j
  simp only [finiteSection,product,Matrix.mul_apply]
  have he : (∑' k : ℕ,M i.val k*U k j.val)=∑ k∈Finset.range n,M i.val k*U k j.val := by
    apply tsum_eq_sum
    intro k hk
    have hk' : n≤k := by simpa only [Finset.mem_range,not_lt] using hk
    rw [hU k j.val (by have hj := j.isLt; omega),mul_zero]
  rw [he,← Fin.sum_univ_eq_sum_range]

theorem sandwich_compression {L U : Kernel} (hL : Lower L) (hU : Upper U)
    (M : Kernel) (n : ℕ) :
    finiteSection (product (product L M) U) n=
      finiteSection L n*finiteSection M n*finiteSection U n := by
  rw [upper_compression hU,lower_compression hL]

theorem lower_det {L : Kernel} (hL : Lower L) {c : ℝ} (hc : ∀ i,L i i=c) (n : ℕ) :
    (finiteSection L n).det=c^n := by
  have ht : (finiteSection L n).IsLowerTriangular := fun i j hij => hL i.val j.val hij
  rw [Matrix.det_of_isLowerTriangular _ ht]
  simp only [finiteSection,hc,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem upper_det {U : Kernel} (hU : Upper U) {c : ℝ} (hc : ∀ i,U i i=c) (n : ℕ) :
    (finiteSection U n).det=c^n := by
  have ht : (finiteSection U n).IsUpperTriangular := fun i j hij => hU i.val j.val hij
  rw [Matrix.det_of_isUpperTriangular ht]
  simp only [finiteSection,hc,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem sandwich_det {L U : Kernel} (hL : Lower L) (hU : Upper U)
    {c d : ℝ} (hc : ∀ i,L i i=c) (hd : ∀ i,U i i=d) (M : Kernel) (n : ℕ) :
    (finiteSection (product (product L M) U) n).det=
      (c*d)^n*(finiteSection M n).det := by
  rw [sandwich_compression hL hU,Matrix.det_mul,Matrix.det_mul,lower_det hL hc,upper_det hU hd,mul_pow]
  ring

end
end SpanningTreeIsoperimetry.TriangularCompression
