import SpanningTreeIsoperimetry.OneSidedLaurentCompatibility
import SpanningTreeIsoperimetry.WeightedConvolutionPath

/-! Signed positive-frequency exponential paths and the actual reflected
factor used in the conjugation difference. This is coefficient calculus only;
it does not duplicate the separate kernel conjugation identity. -/
namespace SpanningTreeIsoperimetry.PositiveExponentialSignedPath
open OneSidedToeplitz OneSidedLaurentCompatibility ToeplitzHankelKernels
open ToeplitzHankelConvolution LaurentConvolutionAlgebra LaurentWeightedConvolution
open WeightedPowerSeries WeightedConvolutionPath Filter Asymptotics
open scoped Topology
noncomputable section

def positiveDirection (V : PowerSeries ℝ) (s : ℝ) : Laurent :=
  convolution (positiveExponential V s) (lift V)
def negativeDirection (V : PowerSeries ℝ) (s : ℝ) : Laurent := -positiveDirection V (-s)
def conjugationFactor (V : PowerSeries ℝ) (s : ℝ) : Laurent :=
  convolution (lift V) (flip (positiveExponential V (-s)))
def factorDirection (V : PowerSeries ℝ) (s : ℝ) : Laurent :=
  -convolution (conjugationFactor V s) (flip (lift V))

theorem positiveDirection_weighted {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) : WeightedSummable (positiveDirection V s) :=
  weighted_convolution (positive_weighted hV0 hV s) (weighted_lift hV)

theorem negativeDirection_weighted {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) : WeightedSummable (negativeDirection V s) :=
  weighted_neg (positiveDirection_weighted hV0 hV (-s))

theorem factor_weighted {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) : WeightedSummable (conjugationFactor V s) :=
  weighted_convolution (weighted_lift hV) (weighted_flip (positive_weighted hV0 hV (-s)))

theorem factorDirection_weighted {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) : WeightedSummable (factorDirection V s) :=
  weighted_neg (weighted_convolution (factor_weighted hV0 hV s) (weighted_flip (weighted_lift hV)))

theorem positive_remainder {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    (fun t : ℝ => weightedMass (positiveExponential V (s+t)-positiveExponential V s-
      t • positiveDirection V s)) =o[𝓝 0] fun t => t :=
  positive_remainder_isLittleO hV0 hV s

theorem negative_remainder {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    (fun t : ℝ => weightedMass (positiveExponential V (-(s+t))-positiveExponential V (-s)-
      t • negativeDirection V s)) =o[𝓝 0] fun t => t := by
  have hn : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using continuous_neg.tendsto (0 : ℝ)
  have h := (positive_remainder hV0 hV (-s)).comp_tendsto hn
  have h' := h.of_neg_right
  simpa only [Function.comp_def,negativeDirection,neg_add,neg_smul,smul_neg] using h'

private theorem convolution_neg_right (a b : Laurent) : convolution a (-b)= -convolution a b := by
  funext n
  simp only [convolution,Pi.neg_apply,mul_neg,tsum_neg]

theorem factorDirection_eq {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    convolution (lift V) (flip (negativeDirection V s))=factorDirection V s := by
  have he : flip (negativeDirection V s)= -flip (positiveDirection V (-s)) := rfl
  rw [he,convolution_neg_right,positiveDirection,flip_convolution,
    ← convolution_assoc_weighted (weighted_lift hV)
      (weighted_flip (positive_weighted hV0 hV (-s))) (weighted_flip (weighted_lift hV))]
  rfl

/-- Derivative of p*flip(E(-(s+t))) is -b(s)*flip(p), in the actual weighted
Laurent mass. All constant-path and reflection premises are discharged. -/
theorem factor_remainder {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    (fun t : ℝ => weightedMass (conjugationFactor V (s+t)-conjugationFactor V s-
      t • factorDirection V s)) =o[𝓝 0] fun t => t := by
  have hzero : WeightedSummable (0 : Laurent) := by
    change Summable (fun n : ℤ => (1+(n.natAbs : ℝ))*|(0 : ℝ)|)
    simpa only [abs_zero,mul_zero] using (summable_zero : Summable (fun _ : ℤ => (0 : ℝ)))
  have hmzero : weightedMass (0 : Laurent)=0 := by simp [weightedMass,weightedTerm]
  have hrzero : (fun t : ℝ => weightedMass (lift V-lift V-t • (0 : Laurent))) =o[𝓝 0] fun t => t := by
    simpa only [sub_self,smul_zero,sub_zero,hmzero] using
      (isLittleO_zero (fun t : ℝ => t) (𝓝 0) : (fun _ : ℝ => (0 : ℝ)) =o[𝓝 0] fun t => t)
  have hrneg : (fun t : ℝ => weightedMass
      (positiveExponential V (-(s+t))-positiveExponential V (-(s+0))-t • negativeDirection V s))
      =o[𝓝 0] fun t => t := by
    simpa only [add_zero] using negative_remainder hV0 hV s
  have h := convolution_remainder_isLittleO
    (fun _ : ℝ => weighted_lift hV)
    (fun t : ℝ => weighted_flip (positive_weighted hV0 hV (-(s+t))))
    hzero (weighted_flip (negativeDirection_weighted hV0 hV s))
    hrzero (flip_remainder_isLittleO hrneg)
  simpa only [conjugationFactor,add_zero,convolution_zero_left,zero_add,factorDirection_eq hV0 hV s] using h

end
end SpanningTreeIsoperimetry.PositiveExponentialSignedPath
