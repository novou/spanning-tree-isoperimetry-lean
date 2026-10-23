module

public import SpanningTreeIsoperimetry.HankelConvolution
public import SpanningTreeIsoperimetry.ToeplitzHankelMassBounds
public import SpanningTreeIsoperimetry.BoundedKernelAlgebra

@[expose] public section

/-! Exact algebra for the summable defect of a triangular conjugation.
No trace is assigned to the individual nonsummable Toeplitz factors. -/
namespace SpanningTreeIsoperimetry.ConjugationHankelAlgebra
open ToeplitzHankelKernels ToeplitzHankelConvolution LaurentWeightedConvolution
open LaurentConvolutionAlgebra OneSidedLaurentKernels ToeplitzHankelMassBounds HankelConvolution
open SummableKernelProduct BoundedKernelProduct BoundedKernelAlgebra AbsolutelySummableDeterminant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual bounded-kernel conjugation defect. -/
def defect (a c p : Laurent) : Kernel :=
  product (product (T a) (T (flip p))) (T c)-T (flip p)
def second (p c : Laurent) : Laurent := convolution p (flip c)

private theorem entry_summable {A B : Kernel} {a b : ℝ} (hA : RowBound A a) (hB : RowBound B b)
    (i j : ℕ) : Summable (fun k => A i k*B k j) := by
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs] using BoundedKernelAlgebra.entry_product_summable hA hB i j

private theorem product_add_left {A B C : Kernel} {a b c : ℝ}
    (hA : RowBound A a) (hB : RowBound B b) (hC : RowBound C c) :
    product (A+B) C=product A C+product B C := by
  ext i j
  simp only [product,Pi.add_apply,add_mul]
  exact (entry_summable hA hC i j).tsum_add (entry_summable hB hC i j)

private theorem product_sub_left {A B C : Kernel} {a b c : ℝ}
    (hA : RowBound A a) (hB : RowBound B b) (hC : RowBound C c) :
    product (A-B) C=product A C-product B C := by
  ext i j
  simp only [product,Pi.sub_apply,sub_mul]
  exact (entry_summable hA hC i j).tsum_sub (entry_summable hB hC i j)

private theorem product_neg_left (A B : Kernel) : product (-A) B= -product A B := by
  ext i j
  simp only [product,Pi.neg_apply,neg_mul,tsum_neg]

private theorem product_neg_right (A B : Kernel) : product A (-B)= -product A B := by
  ext i j
  simp only [product,Pi.neg_apply,mul_neg,tsum_neg]

private theorem product_zero (A : Kernel) : product A 0=0 := by
  ext i j
  simp only [product,Pi.zero_apply,mul_zero,tsum_zero]

private theorem zero_product (A : Kernel) : product 0 A=0 := by
  ext i j
  simp only [product,Pi.zero_apply,zero_mul,tsum_zero]

private theorem product_unit_right (A : Kernel) : product A (T unitCoeff)=A := by
  ext i j
  simp [product,T_unit_apply]

private theorem H_neg (a : Laurent) : H (-a)= -H a := rfl

theorem second_weighted {p c : Laurent} (hp : WeightedSummable p) (hc : WeightedSummable c) :
    WeightedSummable (second p c) := weighted_convolution hp (weighted_flip hc)

theorem second_hankel {p c : Laurent} (hp : WeightedSummable p) (hc : WeightedSummable c)
    (hcs : NonnegativeSupport c) : H (second p c)=product (H p) (T c) := by
  rw [second,hankel_convolution_weighted hp (weighted_flip hc),H_zero (flip_nonnegative hcs),
    LaurentConvolutionAlgebra.flip_flip,product_zero,zero_add]

theorem positive_commute {p c : Laurent} (hp : WeightedSummable p) (hc : WeightedSummable c)
    (hps : NonnegativeSupport p) (hcs : NonnegativeSupport c) :
    product (T p) (T c)=product (T c) (T p) := by
  rw [← T_convolution_of_right_nonnegative (summable_abs hp) (summable_abs hc) hcs,
    convolution_comm, T_convolution_of_right_nonnegative (summable_abs hc) (summable_abs hp) hps]

/-- The compact formula is an identity for the actual conjugation. -/
theorem defect_eq_hankels {a c p : Laurent} (ha : WeightedSummable a) (hc : WeightedSummable c)
    (hp : WeightedSummable p) (hcs : NonnegativeSupport c) (hps : NonnegativeSupport p)
    (hinv : convolution a c=unitCoeff) :
    defect a c p= -product (H a) (H (second p c)) := by
  have ra := rowBound_T_weighted ha
  have rc := rowBound_T_weighted hc
  have rq := rowBound_T_weighted (weighted_flip hp)
  have rha : RowBound (H a) (weightedMass a) := rowBound_hankelOffset_weighted ha 1
  have rhp : RowBound (H p) (weightedMass p) := rowBound_hankelOffset_weighted hp 1
  have hinvT : product (T a) (T c)=T unitCoeff := by
    rw [← T_convolution_of_right_nonnegative (summable_abs ha) (summable_abs hc) hcs,hinv]
  have hcancel : product (product (T (flip p)) (T a)) (T c)=T (flip p) := by
    rw [BoundedKernelAlgebra.product_assoc rq ra rc,hinvT,product_unit_right]
  have hcomm := toeplitz_commutator (summable_abs ha) (summable_abs (weighted_flip hp))
  rw [H_zero (flip_nonnegative hps),LaurentConvolutionAlgebra.flip_flip,zero_product,zero_sub] at hcomm
  have hsplit := product_sub_left (rowBound_product ra rq) (rowBound_product rq ra) rc
  rw [hcancel] at hsplit
  change product (product (T a) (T (flip p))-product (T (flip p)) (T a)) (T c)=defect a c p at hsplit
  rw [← hsplit,hcomm,product_neg_left,BoundedKernelAlgebra.product_assoc rha rhp rc,
    ← second_hankel hp hc hcs]

theorem defect_summable {a c p : Laurent} (ha : WeightedSummable a) (hc : WeightedSummable c)
    (hp : WeightedSummable p) (hcs : NonnegativeSupport c) (hps : NonnegativeSupport p)
    (hinv : convolution a c=unitCoeff) : Summable (entryNorm (defect a c p)) := by
  rw [defect_eq_hankels ha hc hp hcs hps hinv]
  have hs := product_summable (H_summable ha) (H_summable (second_weighted hp hc))
  have he : entryNorm (-product (H a) (H (second p c)))=entryNorm (product (H a) (H (second p c))) := by
    funext p
    exact abs_neg _
  rw [he]
  exact hs

/-- The same intertwining survives multiplication by any positive
Toeplitz factor commuting with the generator. -/
theorem second_intertwining {p c : Laurent} (hp : WeightedSummable p) (hc : WeightedSummable c)
    (hps : NonnegativeSupport p) (hcs : NonnegativeSupport c) :
    product (T (flip p)) (H (second p c))=product (H (second p c)) (T p) := by
  have rq := rowBound_T_weighted (weighted_flip hp)
  have rp := rowBound_T_weighted hp
  have rh : RowBound (H p) (weightedMass p) := rowBound_hankelOffset_weighted hp 1
  have rc := rowBound_T_weighted hc
  rw [second_hankel hp hc hcs,
    ← BoundedKernelAlgebra.product_assoc rq rh rc,positive_intertwining hp hps,
    BoundedKernelAlgebra.product_assoc rh rp rc,positive_commute hp hc hps hcs,
    ← BoundedKernelAlgebra.product_assoc rh rc rp]

theorem second_direction_hankel {p c : Laurent} (hp : WeightedSummable p) (hc : WeightedSummable c)
    (hps : NonnegativeSupport p) :
    H (convolution (second p c) (flip p))=product (H (second p c)) (T p) := by
  rw [hankel_convolution_weighted (second_weighted hp hc) (weighted_flip hp),
    H_zero (flip_nonnegative hps),LaurentConvolutionAlgebra.flip_flip,product_zero,zero_add]

/-- The HH Leibniz direction simplifies to the conjugate of the fixed
summable square H(p)^2. -/
theorem hankel_direction {a c p : Laurent} (ha : WeightedSummable a) (hc : WeightedSummable c)
    (hp : WeightedSummable p) (hcs : NonnegativeSupport c) (hps : NonnegativeSupport p) :
    -(product (H (convolution a p)) (H (second p c))+
      product (H a) (H (-convolution (second p c) (flip p))))=
      -product (product (T a) (product (H p) (H p))) (T c) := by
  have ra := rowBound_T_weighted ha
  have rp := rowBound_T_weighted hp
  have rq := rowBound_T_weighted (weighted_flip hp)
  have rc := rowBound_T_weighted hc
  have rha : RowBound (H a) (weightedMass a) := rowBound_hankelOffset_weighted ha 1
  have rhp : RowBound (H p) (weightedMass p) := rowBound_hankelOffset_weighted hp 1
  have rhb : RowBound (H (second p c)) (weightedMass (second p c)) :=
    rowBound_hankelOffset_weighted (second_weighted hp hc) 1
  have hcross : product (product (H a) (T (flip p))) (H (second p c))=
      product (H a) (product (H (second p c)) (T p)) := by
    rw [BoundedKernelAlgebra.product_assoc rha rq rhb,second_intertwining hp hc hps hcs]
  have hmain : product (product (T a) (H p)) (H (second p c))=
      product (product (T a) (product (H p) (H p))) (T c) := by
    rw [second_hankel hp hc hcs,
      ← BoundedKernelAlgebra.product_assoc (rowBound_product ra rhp) rhp rc,
      BoundedKernelAlgebra.product_assoc ra rhp rhp]
  rw [hankel_convolution_weighted ha hp,H_neg,second_direction_hankel hp hc hps,
    product_neg_right,product_add_left (rowBound_product ra rhp) (rowBound_product rha rq) rhb,
    hcross,hmain]
  abel

end
end SpanningTreeIsoperimetry.ConjugationHankelAlgebra
