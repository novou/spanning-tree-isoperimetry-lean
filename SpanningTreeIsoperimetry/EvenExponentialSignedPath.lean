import SpanningTreeIsoperimetry.EvenExponentialPath

/-! Positive and negative parameter directions of the actual even Laurent
exponential, including the sign in the negative reparametrization. -/
namespace SpanningTreeIsoperimetry.EvenExponentialSignedPath
open OneSidedLaurentCompatibility EvenExponentialPath ToeplitzHankelKernels
open ToeplitzHankelConvolution LaurentWeightedConvolution WeightedPowerSeries
open Filter Asymptotics
open scoped Topology
noncomputable section

def positiveDirection (V : PowerSeries ℝ) (s : ℝ) : Laurent :=
  convolution (evenExponential V s) (evenGenerator V)
def negativeDirection (V : PowerSeries ℝ) (s : ℝ) : Laurent := -positiveDirection V (-s)

theorem positiveDirection_weighted {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) : WeightedSummable (positiveDirection V s) :=
  weighted_convolution (even_weighted hV0 hV s) (generator_weighted hV)

theorem negativeDirection_weighted {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) : WeightedSummable (negativeDirection V s) :=
  weighted_neg (positiveDirection_weighted hV0 hV (-s))

theorem positive_remainder {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    (fun t : ℝ => weightedMass (evenExponential V (s+t)-evenExponential V s-
      t • positiveDirection V s)) =o[𝓝 0] fun t => t :=
  even_remainder_isLittleO hV0 hV s

theorem negative_remainder {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    (fun t : ℝ => weightedMass (evenExponential V (-(s+t))-evenExponential V (-s)-
      t • negativeDirection V s)) =o[𝓝 0] fun t => t := by
  have hn : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using continuous_neg.tendsto (0 : ℝ)
  have h := (positive_remainder hV0 hV (-s)).comp_tendsto hn
  have h' := h.of_neg_right
  simpa only [Function.comp_def,negativeDirection,neg_add,neg_smul,smul_neg] using h'

end
end SpanningTreeIsoperimetry.EvenExponentialSignedPath
