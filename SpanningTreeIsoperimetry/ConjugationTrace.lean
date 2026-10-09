import SpanningTreeIsoperimetry.ConjugationHankelAlgebra
import SpanningTreeIsoperimetry.PositiveExponentialSignedPath
import SpanningTreeIsoperimetry.WeightedKernelProductPath
import SpanningTreeIsoperimetry.SummableTraceConjugation
import SpanningTreeIsoperimetry.SummableTracePath
import Mathlib.Analysis.Calculus.MeanValue

/-! The actual trace of a triangular conjugation defect. The derivative
is obtained in total entry mass from the checked HH Leibniz rule, and its
constant trace follows from the proved summable-middle cyclicity theorem. -/
namespace SpanningTreeIsoperimetry.ConjugationTrace
open ToeplitzHankelKernels ToeplitzHankelConvolution LaurentWeightedConvolution
open LaurentConvolutionAlgebra OneSidedLaurentKernels ToeplitzHankelMassBounds
open OneSidedToeplitz OneSidedLaurentCompatibility WeightedPowerSeries
open ConjugationHankelAlgebra SummableKernelProduct BoundedKernelProduct
open AbsolutelySummableDeterminant SummableKernelTrace SummableTracePath
open SummableDeterminantFirstOrder SummableDeterminantContinuity Filter Asymptotics
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem entryNorm_neg (A : Kernel) : entryNorm (-A)=entryNorm A := by
  funext p
  exact abs_neg _

private theorem totalMass_neg (A : Kernel) : totalMass (-A)=totalMass A := by
  unfold totalMass
  rw [entryNorm_neg]

def D (V : PowerSeries ℝ) (s : ℝ) : Kernel :=
  defect (positiveExponential V s) (positiveExponential V (-s)) (lift V)
def direction (V : PowerSeries ℝ) (s : ℝ) : Kernel :=
  -product (product (T (positiveExponential V s)) (product (H (lift V)) (H (lift V))))
    (T (positiveExponential V (-s)))

theorem D_compact {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (hV : SummableWeighted V) (s : ℝ) :
    D V s= -product (H (positiveExponential V s))
      (H (PositiveExponentialSignedPath.conjugationFactor V s)) :=
  defect_eq_hankels (positive_weighted hV0 hV s) (positive_weighted hV0 hV (-s))
    (weighted_lift hV) (positive_support V (-s)) (lift_nonnegative V) (positive_inverse hV0 hV s)

theorem D_summable {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (hV : SummableWeighted V) (s : ℝ) :
    Summable (entryNorm (D V s)) :=
  defect_summable (positive_weighted hV0 hV s) (positive_weighted hV0 hV (-s))
    (weighted_lift hV) (positive_support V (-s)) (lift_nonnegative V) (positive_inverse hV0 hV s)

theorem direction_summable {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (hV : SummableWeighted V) (s : ℝ) :
    Summable (entryNorm (direction V s)) := by
  have hs := right_summable
    (left_summable (columnBound_T_weighted (positive_weighted hV0 hV s))
      (product_summable (H_summable (weighted_lift hV)) (H_summable (weighted_lift hV))))
    (rowBound_T_weighted (positive_weighted hV0 hV (-s)))
  rw [direction,entryNorm_neg]
  exact hs

theorem direction_eq_leibniz {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    direction V s= -(product (H (PositiveExponentialSignedPath.positiveDirection V s))
      (H (PositiveExponentialSignedPath.conjugationFactor V s))+
      product (H (positiveExponential V s)) (H (PositiveExponentialSignedPath.factorDirection V s))) := by
  exact (hankel_direction (positive_weighted hV0 hV s) (positive_weighted hV0 hV (-s))
    (weighted_lift hV) (positive_support V (-s)) (lift_nonnegative V)).symm

theorem D_remainder {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    (fun t : ℝ => totalMass (D V (s+t)-D V s-t • direction V s)) =o[𝓝 0] fun t => t := by
  have h := WeightedKernelProductPath.hankel_hankel_remainder_isLittleO 1 1
    (a := fun t => positiveExponential V (s+t))
    (b := fun t => PositiveExponentialSignedPath.conjugationFactor V (s+t))
    (a1 := PositiveExponentialSignedPath.positiveDirection V s)
    (b1 := PositiveExponentialSignedPath.factorDirection V s)
    (fun t => positive_weighted hV0 hV (s+t))
    (fun t => PositiveExponentialSignedPath.factor_weighted hV0 hV (s+t))
    (PositiveExponentialSignedPath.positiveDirection_weighted hV0 hV s)
    (PositiveExponentialSignedPath.factorDirection_weighted hV0 hV s)
    (by simpa only [add_zero] using PositiveExponentialSignedPath.positive_remainder hV0 hV s)
    (by simpa only [add_zero] using PositiveExponentialSignedPath.factor_remainder hV0 hV s)
  apply h.congr_left
  intro t
  rw [D_compact hV0 hV (s+t),D_compact hV0 hV s,direction_eq_leibniz hV0 hV s]
  simp only [add_zero]
  have he (A B E : Kernel) : -A-(-B)-t • (-E)= -(A-B-t • E) := by
    ext i j
    simp only [Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he,totalMass_neg]
  rfl

theorem direction_trace {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    trace (direction V s)= -trace (product (H (lift V)) (H (lift V))) := by
  have hinv : product (T (positiveExponential V (-s))) (T (positiveExponential V s))=T unitCoeff := by
    rw [← T_convolution_of_right_nonnegative (summable_abs (positive_weighted hV0 hV (-s)))
      (summable_abs (positive_weighted hV0 hV s)) (positive_support V s)]
    have h := positive_inverse hV0 hV (-s)
    simpa only [neg_neg] using congrArg T h
  unfold direction
  simp only [trace,Pi.neg_apply,tsum_neg]
  congr 1
  exact SummableTraceConjugation.trace_conjugation
    (rowBound_T_weighted (positive_weighted hV0 hV s))
    (rowBound_T_weighted (positive_weighted hV0 hV (-s)))
    (product_summable (H_summable (weighted_lift hV)) (H_summable (weighted_lift hV))) hinv

theorem hasDerivAt_trace {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    HasDerivAt (fun t : ℝ => trace (D V t))
      (-trace (product (H (lift V)) (H (lift V)))) s := by
  have hr := trace_isLittleO_of_mass
    (fun t => difference_summable (difference_summable (D_summable hV0 hV (s+t))
      (D_summable hV0 hV s)) (scale_summable t (direction_summable hV0 hV s)))
    (D_remainder hV0 hV s)
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  apply hr.congr_left
  intro t
  rw [trace_sub (difference_summable (D_summable hV0 hV (s+t)) (D_summable hV0 hV s))
    (scale_summable t (direction_summable hV0 hV s)),
    trace_sub (D_summable hV0 hV (s+t)) (D_summable hV0 hV s)]
  change trace (D V (s+t))-trace (D V s)-trace (scale t (direction V s))=_
  rw [scale_trace,direction_trace hV0 hV s]
  rfl

theorem D_zero {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (hV : SummableWeighted V) : D V 0=0 := by
  rw [D_compact hV0 hV 0,positive_zero]
  have hh : H unitCoeff=0 := by
    apply H_zero
    intro n hn
    simp [unitCoeff,ne_of_gt hn]
  rw [hh]
  ext i j
  simp only [Pi.neg_apply,product,Pi.zero_apply,zero_mul,tsum_zero,neg_zero]

/-- The conjugation defect has exactly linear trace, with the sign fixed
by the actual Hankel commutator. -/
theorem trace_D {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    trace (D V s)= -s*trace (product (H (lift V)) (H (lift V))) := by
  let q : ℝ := trace (product (H (lift V)) (H (lift V)))
  have hd (t : ℝ) : HasDerivAt (fun x : ℝ => trace (D V x)+x*q) 0 t := by
    have htrace : HasDerivAt (fun x : ℝ => trace (D V x)) (-q) t := hasDerivAt_trace hV0 hV t
    have hmul : HasDerivAt (fun x : ℝ => x*q) q t := hasDerivAt_mul_const q
    have hsum : HasDerivAt (fun x : ℝ => trace (D V x)+x*q) (-q+q) t := htrace.add hmul
    simpa only [neg_add_cancel] using hsum
  have he := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) s 0
  change trace (D V s)+s*q=trace (D V 0)+0*q at he
  rw [D_zero hV0 hV] at he
  simp only [trace,Pi.zero_apply,tsum_zero,zero_mul,zero_add] at he
  change trace (D V s)+s*q=0 at he
  change trace (D V s)= -s*q
  linarith

end
end SpanningTreeIsoperimetry.ConjugationTrace
