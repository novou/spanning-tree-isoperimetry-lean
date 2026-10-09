import SpanningTreeIsoperimetry.LaurentConvolutionAlgebra
import SpanningTreeIsoperimetry.TriangularCompression

/-! One-sided support of actual Laurent coefficients gives triangular
Toeplitz kernels and exact multiplication without a Hankel defect. -/
namespace SpanningTreeIsoperimetry.OneSidedLaurentKernels
open ToeplitzHankelKernels ToeplitzHankelConvolution LaurentConvolutionAlgebra
open SummableKernelProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Negative coefficients vanish; the zero coefficient may be nonzero. -/
def NonnegativeSupport (a : Laurent) : Prop := ∀ n : ℤ,n<0 → a n=0
/-- Positive coefficients vanish; the zero coefficient may be nonzero. -/
def NonpositiveSupport (a : Laurent) : Prop := ∀ n : ℤ,0<n → a n=0

theorem flip_nonnegative {a : Laurent} (ha : NonnegativeSupport a) : NonpositiveSupport (flip a) := by
  intro n hn
  exact ha (-n) (by omega)

theorem flip_nonpositive {a : Laurent} (ha : NonpositiveSupport a) : NonnegativeSupport (flip a) := by
  intro n hn
  exact ha (-n) (by omega)

theorem convolution_nonnegative {a b : Laurent} (ha : NonnegativeSupport a) (hb : NonnegativeSupport b) :
    NonnegativeSupport (convolution a b) := by
  intro n hn
  have hz (k : ℤ) : a (n-k)*b k=0 := by
    by_cases hk : k<0
    · rw [hb k hk,mul_zero]
    · rw [ha (n-k) (by omega),zero_mul]
  simp only [convolution,hz,tsum_zero]

theorem convolution_nonpositive {a b : Laurent} (ha : NonpositiveSupport a) (hb : NonpositiveSupport b) :
    NonpositiveSupport (convolution a b) := by
  intro n hn
  have hz (k : ℤ) : a (n-k)*b k=0 := by
    by_cases hk : 0<k
    · rw [hb k hk,mul_zero]
    · rw [ha (n-k) (by omega),zero_mul]
  simp only [convolution,hz,tsum_zero]

theorem T_flip (a : Laurent) : T (flip a)=BoundedKernelProduct.transpose (T a) := by
  ext i j
  change a (-((i : ℤ)-j))=a ((j : ℤ)-i)
  congr 1
  ring

theorem T_lower {a : Laurent} (ha : NonnegativeSupport a) : TriangularCompression.Lower (T a) := by
  intro i j hij
  exact ha ((i : ℤ)-j) (by omega)

theorem T_upper {a : Laurent} (ha : NonpositiveSupport a) : TriangularCompression.Upper (T a) := by
  intro i j hji
  exact ha ((i : ℤ)-j) (by omega)

theorem hankelOffset_zero {a : Laurent} (ha : NonpositiveSupport a) {d : ℕ} (hd : 0<d) :
    hankelOffset a d=0 := by
  ext i j
  exact ha ((i+j+d : ℕ) : ℤ) (by omega)

theorem H_zero {a : Laurent} (ha : NonpositiveSupport a) : H a=0 :=
  hankelOffset_zero ha (by norm_num : 0<(1 : ℕ))

theorem Hshift_zero {a : Laurent} (ha : NonpositiveSupport a) : Hshift a=0 :=
  hankelOffset_zero ha (by norm_num : 0<(2 : ℕ))

theorem M_eq_T {a : Laurent} (ha : NonpositiveSupport a) : M a=T a := by
  rw [M,Hshift_zero ha,sub_zero]

theorem T_convolution_of_left_nonpositive {a b : Laurent}
    (ha : Summable (fun n => |a n|)) (hb : Summable (fun n => |b n|))
    (hs : NonpositiveSupport a) : T (convolution a b)=product (T a) (T b) := by
  rw [toeplitz_convolution ha hb,H_zero hs]
  ext i j
  simp only [Pi.add_apply,product,Pi.zero_apply,zero_mul,tsum_zero,add_zero]

theorem T_convolution_of_right_nonnegative {a b : Laurent}
    (ha : Summable (fun n => |a n|)) (hb : Summable (fun n => |b n|))
    (hs : NonnegativeSupport b) : T (convolution a b)=product (T a) (T b) := by
  rw [toeplitz_convolution ha hb,H_zero (flip_nonnegative hs)]
  ext i j
  simp only [Pi.add_apply,product,Pi.zero_apply,mul_zero,tsum_zero,add_zero]

theorem T_unit_apply (i j : ℕ) : T unitCoeff i j=if i=j then 1 else 0 := by
  simp only [T,unitCoeff,sub_eq_zero,Nat.cast_inj]

theorem Hshift_unit : Hshift unitCoeff=0 := by
  apply Hshift_zero
  intro n hn
  simp only [unitCoeff,if_neg (by omega : n≠0)]

theorem M_unit_apply (i j : ℕ) : M unitCoeff i j=if i=j then 1 else 0 := by
  rw [M,Hshift_unit,sub_zero,T_unit_apply]

/-- The Laurent convolution inverse gives the actual shifted-kernel
inverse whenever the right sequence is even. -/
theorem M_inverse {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b)
    (he : Function.Even b) (hinv : convolution a b=unitCoeff) (i j : ℕ) :
    product (M a) (M b) i j=if i=j then 1 else 0 := by
  rw [M_convolution_weighted ha hb he,hinv,M_unit_apply]

end
end SpanningTreeIsoperimetry.OneSidedLaurentKernels
