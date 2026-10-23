module

public import SpanningTreeIsoperimetry.OneSidedLaurentKernels

@[expose] public section

/-! The exact Hankel convolution identity and the resulting intertwining
relation for one-sided Laurent coefficients. Every infinite product comes
from an absolutely convergent split of the full integer convolution. -/
namespace SpanningTreeIsoperimetry.HankelConvolution
open ToeplitzHankelKernels ToeplitzHankelConvolution LaurentConvolutionAlgebra
open OneSidedLaurentKernels SummableKernelProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The positive and negative intermediate indices give the two mixed
Toeplitz-Hankel products, with the actual index-one Hankel convention. -/
theorem hankel_convolution {a b : Laurent}
    (ha : Summable (fun n => |a n|)) (hb : Summable (fun n => |b n|)) :
    H (convolution a b)=product (T a) (H b)+product (H a) (T (flip b)) := by
  ext i j
  let y : ℤ := -(j : ℤ)-1
  let f : ℤ → ℝ := fun k => a ((i : ℤ)-k)*b (k-y)
  have hf : Summable f := full_entry_summable ha hb i y
  have hp : Summable (fun n : ℕ => f n) := hf.comp_injective Nat.cast_injective
  have hn : Summable (fun n : ℕ => f (-((n+1 : ℕ) : ℤ))) :=
    hf.comp_injective (by intro m n h; dsimp only at h; omega)
  have hsplit := tsum_of_nat_of_neg_add_one hp hn
  have hpos (k : ℕ) : f k=T a i k*H b k j := by
    dsimp only [f,y,T,H,hankelOffset]
    congr 1
    congr 1
    omega
  have hneg (k : ℕ) : f (-((k+1 : ℕ) : ℤ))=H a i k*T (flip b) k j := by
    dsimp only [f,y,T,H,hankelOffset,ToeplitzHankelKernels.flip]
    congr 1 <;> congr 1 <;> omega
  have hij : ((i+j+1 : ℕ) : ℤ)=(i : ℤ)-y := by dsimp [y]; omega
  change convolution a b ((i+j+1 : ℕ) : ℤ)=_
  rw [hij,convolution_shift]
  change (∑' k : ℤ,f k)=_
  rw [hsplit]
  change (∑' k : ℕ,f k)+(∑' k : ℕ,f (-(k+1 : ℤ)))=
    (∑' k : ℕ,T a i k*H b k j)+(∑' k : ℕ,H a i k*T (flip b) k j)
  congr 1
  · exact tsum_congr hpos
  · apply tsum_congr
    intro k
    simpa only [Nat.cast_add,Nat.cast_one] using hneg k

theorem hankel_convolution_weighted {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b) :
    H (convolution a b)=product (T a) (H b)+product (H a) (T (flip b)) :=
  hankel_convolution (summable_abs ha) (summable_abs hb)

/-- Writing `P=T(V)` and `Q=T(flip V)`, this is the concrete relation
`Q H(V)=H(V) P`. It requires only the one-sided support of `V`. -/
theorem positive_intertwining {a : Laurent} (ha : WeightedSummable a) (hs : NonnegativeSupport a) :
    product (T (flip a)) (H a)=product (H a) (T a) := by
  have h1 := hankel_convolution_weighted (weighted_flip ha) ha
  have h2 := hankel_convolution_weighted ha (weighted_flip ha)
  rw [H_zero (flip_nonnegative hs)] at h1 h2
  rw [LaurentConvolutionAlgebra.flip_flip] at h2
  have hzleft (A : Kernel) : product 0 A=0 := by
    ext i j
    simp only [product,Pi.zero_apply,zero_mul,tsum_zero]
  have hzright (A : Kernel) : product A 0=0 := by
    ext i j
    simp only [product,Pi.zero_apply,mul_zero,tsum_zero]
  rw [hzleft,add_zero] at h1
  rw [hzright,zero_add] at h2
  rw [convolution_comm (flip a) a] at h1
  exact h1.symm.trans h2

end
end SpanningTreeIsoperimetry.HankelConvolution
