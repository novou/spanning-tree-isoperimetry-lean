module

public import SpanningTreeIsoperimetry.NormalizedExponentialPath
public import SpanningTreeIsoperimetry.BoundedKernelLinear

@[expose] public section

/-! Algebraic forms of the actual normalized kernel derivative. These are
identities of kernels; no trace of an individual nonsummable factor is used. -/
namespace SpanningTreeIsoperimetry.NormalizedExponentialDerivativeAlgebra
open OneSidedToeplitz OneSidedLaurentCompatibility EvenExponentialPath EvenExponentialSignedPath
open NormalizedExponentialInverse NormalizedExponentialPath ToeplitzHankelKernels
open ToeplitzHankelConvolution LaurentConvolutionAlgebra LaurentWeightedConvolution
open OneSidedLaurentKernels ToeplitzHankelMassBounds WeightedPowerSeries
open SummableKernelProduct BoundedKernelProduct BoundedKernelAlgebra
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem convolution_neg_left (a b : Laurent) : convolution (-a) b= -convolution a b := by
  funext n
  simp only [convolution,Pi.neg_apply,neg_mul,tsum_neg]

private theorem T_neg (a : Laurent) : T (-a)= -T a := rfl
private theorem T_zero : T (0 : Laurent)=0 := rfl

theorem flip_generator (V : PowerSeries ℝ) : flip (evenGenerator V)=evenGenerator V := by
  funext n
  simp only [evenGenerator,ToeplitzHankelKernels.flip,Pi.add_apply,neg_neg]
  ring

theorem generator_even (V : PowerSeries ℝ) : Function.Even (evenGenerator V) :=
  (flip_eq_iff_even _).mp (flip_generator V)

theorem flip_positiveDirection (V : PowerSeries ℝ) (s : ℝ) :
    flip (positiveDirection V s)=positiveDirection V s := by
  rw [positiveDirection,flip_convolution,(flip_eq_iff_even _).mpr (even_even V s),flip_generator]

theorem direction_convolution_cancel {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    convolution (negativeDirection V s) (evenExponential V s)+
      convolution (evenExponential V (-s)) (positiveDirection V s)=0 := by
  have hm := even_weighted hV0 hV (-s)
  have hp := even_weighted hV0 hV s
  have hg := generator_weighted hV
  rw [negativeDirection,positiveDirection,positiveDirection,convolution_neg_left,
    convolution_assoc_weighted hm hg hp,convolution_comm (evenGenerator V) (evenExponential V s)]
  exact neg_add_cancel _

/-- Raw Leibniz form of the already proved summable derivative. -/
theorem direction_eq_raw {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    direction V s=product (T (negativeDirection V s)) (M (evenExponential V s))+
      product (T (evenExponential V (-s))) (M (positiveDirection V s)) := by
  have hm := even_weighted hV0 hV (-s)
  have hp := even_weighted hV0 hV s
  have hdm := negativeDirection_weighted hV0 hV s
  have hdp := positiveDirection_weighted hV0 hV s
  have h1 := toeplitz_convolution_weighted hdm hp
  have h2 := toeplitz_convolution_weighted hm hdp
  rw [(flip_eq_iff_even _).mpr (even_even V s)] at h1
  rw [flip_positiveDirection] at h2
  have hc := congrArg T (direction_convolution_cancel hV0 hV s)
  rw [T_add,T_zero,h1,h2] at hc
  have htt : product (T (negativeDirection V s)) (T (evenExponential V s))+
      product (T (evenExponential V (-s))) (T (positiveDirection V s))=
      -(product (H (negativeDirection V s)) (H (evenExponential V s))+
        product (H (evenExponential V (-s))) (H (positiveDirection V s))) := by
    have hz : (product (T (negativeDirection V s)) (T (evenExponential V s))+
        product (T (evenExponential V (-s))) (T (positiveDirection V s)))+
        (product (H (negativeDirection V s)) (H (evenExponential V s))+
        product (H (evenExponential V (-s))) (H (positiveDirection V s)))=0 := by
      convert hc using 1 <;> abel
    exact eq_neg_of_add_eq_zero_left hz
  symm
  calc
    _=(product (T (negativeDirection V s)) (T (evenExponential V s))+
        product (T (evenExponential V (-s))) (T (positiveDirection V s)))-
        (product (T (negativeDirection V s)) (Hshift (evenExponential V s))+
        product (T (evenExponential V (-s))) (Hshift (positiveDirection V s))) := by
      rw [M,M,Hshift,Hshift,
        BoundedKernelLinear.product_sub_right (rowBound_T_weighted hdm) (rowBound_T_weighted hp)
          (rowBound_hankelOffset_weighted hp 2),
        BoundedKernelLinear.product_sub_right (rowBound_T_weighted hm) (rowBound_T_weighted hdp)
          (rowBound_hankelOffset_weighted hdp 2)]
      abel
    _=direction V s := by
      rw [htt]
      unfold direction thDirection hhDirection
      abel

def P (V : PowerSeries ℝ) : Kernel := T (lift V)
def Q (V : PowerSeries ℝ) : Kernel := T (flip (lift V))
def B (V : PowerSeries ℝ) : Kernel := M (evenGenerator V)

theorem row_P {V : PowerSeries ℝ} (hV : SummableWeighted V) : RowBound (P V) (weightedMass (lift V)) :=
  rowBound_T_weighted (weighted_lift hV)
theorem row_Q {V : PowerSeries ℝ} (hV : SummableWeighted V) : RowBound (Q V) (weightedMass (flip (lift V))) :=
  rowBound_T_weighted (weighted_flip (weighted_lift hV))
theorem row_B {V : PowerSeries ℝ} (hV : SummableWeighted V) : RowBound (B V) (2*weightedMass (evenGenerator V)) :=
  rowBound_M_weighted (generator_weighted hV)

theorem T_negativeDirection {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    T (negativeDirection V s)= -(product (N V s) (P V)+product (Q V) (N V s)) := by
  have hm := even_weighted hV0 hV (-s)
  have hp := weighted_lift hV
  have hq := weighted_flip hp
  have h1 : T (convolution (evenExponential V (-s)) (lift V))=product (N V s) (P V) :=
    T_convolution_of_right_nonnegative (summable_abs hm) (summable_abs hp) (lift_nonnegative V)
  have h2 : T (convolution (evenExponential V (-s)) (flip (lift V)))=product (Q V) (N V s) := by
    rw [convolution_comm]
    exact T_convolution_of_left_nonpositive (summable_abs hq) (summable_abs hm)
      (flip_nonnegative (lift_nonnegative V))
  rw [negativeDirection,positiveDirection,T_neg,evenGenerator,
    convolution_add_right hm hp hq,T_add,h1,h2]

theorem M_positiveDirection {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    M (positiveDirection V s)=product (B V) (W V s) := by
  rw [positiveDirection,convolution_comm]
  exact (M_convolution_weighted (generator_weighted hV) (even_weighted hV0 hV s) (even_even V s)).symm

/-- The raw derivative arranged for multiplication by the actual inverse. -/
theorem direction_eq_factored {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    direction V s= -product (product (N V s) (P V)) (W V s)-
      product (product (Q V) (N V s)) (W V s)+product (product (N V s) (B V)) (W V s) := by
  rw [direction_eq_raw hV0 hV s,T_negativeDirection hV0 hV s,M_positiveDirection hV0 hV s]
  change product (-(product (N V s) (P V)+product (Q V) (N V s))) (W V s)+
    product (N V s) (product (B V) (W V s))=_
  rw [BoundedKernelLinear.product_neg_left,
    BoundedKernelLinear.product_add_left (rowBound_product (row_N hV0 hV s) (row_P hV))
      (rowBound_product (row_Q hV) (row_N hV0 hV s)) (row_W hV0 hV s),
    ← BoundedKernelAlgebra.product_assoc (row_N hV0 hV s) (row_B hV) (row_W hV0 hV s)]
  abel

end
end SpanningTreeIsoperimetry.NormalizedExponentialDerivativeAlgebra
