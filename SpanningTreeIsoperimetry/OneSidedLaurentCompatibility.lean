module

public import SpanningTreeIsoperimetry.OneSidedToeplitz
public import SpanningTreeIsoperimetry.OneSidedLaurentKernels

@[expose] public section

/-! The positive-frequency lift respects actual Laurent convolution and
transfers the proved weighted exponential remainder to Laurent coefficients. -/
namespace SpanningTreeIsoperimetry.OneSidedLaurentCompatibility
open OneSidedToeplitz OneSidedLaurentKernels ToeplitzHankelKernels
open ToeplitzHankelConvolution LaurentConvolutionAlgebra LaurentWeightedConvolution
open PositiveFrequencyExponential WeightedPowerSeries WeightedExponentialRemainder
open Filter Asymptotics
open scoped Topology
noncomputable section

theorem T_injective : Function.Injective T := by
  intro a b h
  funext n
  cases n with
  | ofNat n =>
    change a (n : ℤ)=b (n : ℤ)
    have he := congrFun (congrFun h n) 0
    simpa only [T,Nat.cast_zero,sub_zero] using he
  | negSucc n =>
    have he := congrFun (congrFun h 0) (n+1)
    have hn : (0 : ℤ)-((n+1 : ℕ) : ℤ)=Int.negSucc n := by omega
    simpa only [T,Nat.cast_zero,hn] using he

theorem lift_nonnegative (p : PowerSeries ℝ) : NonnegativeSupport (lift p) :=
  fun _ hn => lift_negative p hn

theorem lift_one : lift (1 : PowerSeries ℝ)=unitCoeff := by
  funext n
  cases n <;> simp [lift,unitCoeff]

theorem lift_add (p q : PowerSeries ℝ) : lift (p+q)=lift p+lift q := by
  funext n
  cases n <;> simp [lift]

theorem lift_sub (p q : PowerSeries ℝ) : lift (p-q)=lift p-lift q := by
  funext n
  cases n <;> simp [lift]

theorem lift_C_mul (t : ℝ) (p : PowerSeries ℝ) : lift (PowerSeries.C t*p)=t • lift p := by
  funext n
  cases n <;> simp [lift,PowerSeries.coeff_C_mul]

theorem lift_mul {p q : PowerSeries ℝ} (hp : SummableWeighted p) (hq : SummableWeighted q) :
    lift (p*q)=convolution (lift p) (lift q) := by
  apply T_injective
  rw [T_lift,T_convolution_of_right_nonnegative (summable_abs (weighted_lift hp))
    (summable_abs (weighted_lift hq)) (lift_nonnegative q),T_lift,T_lift,lower_mul]

def positiveExponential (V : PowerSeries ℝ) (t : ℝ) : Laurent := lift (exponential V t)

theorem positive_weighted {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (t : ℝ) : WeightedSummable (positiveExponential V t) :=
  weighted_lift (exponential_control hV0 hV t).1

theorem positive_support (V : PowerSeries ℝ) (t : ℝ) : NonnegativeSupport (positiveExponential V t) :=
  lift_nonnegative _

theorem positive_zero (V : PowerSeries ℝ) : positiveExponential V 0=unitCoeff := by
  rw [positiveExponential,exponential_zero,lift_one]

theorem positive_add {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s t : ℝ) :
    positiveExponential V (s+t)=convolution (positiveExponential V s) (positiveExponential V t) := by
  rw [positiveExponential,exponential_add hV0,
    lift_mul (exponential_control hV0 hV s).1 (exponential_control hV0 hV t).1]
  rfl

theorem positive_inverse {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (t : ℝ) :
    convolution (positiveExponential V t) (positiveExponential V (-t))=unitCoeff := by
  rw [← positive_add hV0 hV,add_neg_cancel,positive_zero]

theorem positive_remainder_isLittleO {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    (fun t : ℝ => weightedMass (positiveExponential V (s+t)-positiveExponential V s-
      t • convolution (positiveExponential V s) (lift V))) =o[𝓝 0] (fun t => t) := by
  have he (t : ℝ) : positiveExponential V (s+t)-positiveExponential V s-
      t • convolution (positiveExponential V s) (lift V)=
      lift (exponential V (s+t)-exponential V s-PowerSeries.C t*(exponential V s*V)) := by
    rw [lift_sub,lift_sub,lift_C_mul,lift_mul (exponential_control hV0 hV s).1 hV]
    rfl
  have hm (t : ℝ) : weightedMass (positiveExponential V (s+t)-positiveExponential V s-
      t • convolution (positiveExponential V s) (lift V))=
      WeightedPowerSeries.mass (exponential V (s+t)-exponential V s-PowerSeries.C t*(exponential V s*V)) := by
    rw [he,weightedMass_lift (shifted_remainder_summable hV0 hV s t)]
  simpa only [hm] using shifted_remainder_isLittleO hV0 hV s

def evenExponential (V : PowerSeries ℝ) (t : ℝ) : Laurent :=
  convolution (positiveExponential V t) (ToeplitzHankelKernels.flip (positiveExponential V t))

theorem even_weighted {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (t : ℝ) : WeightedSummable (evenExponential V t) :=
  weighted_convolution (positive_weighted hV0 hV t) (weighted_flip (positive_weighted hV0 hV t))

theorem even_even (V : PowerSeries ℝ) (t : ℝ) : Function.Even (evenExponential V t) :=
  convolution_flip_even _

theorem even_inverse {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (t : ℝ) :
    convolution (evenExponential V t) (evenExponential V (-t))=unitCoeff := by
  exact convolution_flip_inverse (positive_weighted hV0 hV t)
    (positive_weighted hV0 hV (-t)) (positive_inverse hV0 hV t)

end
end SpanningTreeIsoperimetry.OneSidedLaurentCompatibility
