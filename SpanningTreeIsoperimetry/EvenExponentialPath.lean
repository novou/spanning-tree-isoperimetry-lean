import SpanningTreeIsoperimetry.OneSidedLaurentCompatibility
import SpanningTreeIsoperimetry.WeightedConvolutionPath

/-! The actual even Laurent exponential inherits a weighted derivative from
its proved positive factor and reflected factor. The convolution derivative
is identified with multiplication by the actual even generator. -/
namespace SpanningTreeIsoperimetry.EvenExponentialPath
open OneSidedToeplitz OneSidedLaurentCompatibility ToeplitzHankelKernels
open ToeplitzHankelConvolution LaurentConvolutionAlgebra LaurentWeightedConvolution
open WeightedPowerSeries WeightedConvolutionPath Filter Asymptotics
open scoped Topology
noncomputable section

def evenGenerator (V : PowerSeries ℝ) : Laurent := lift V+flip (lift V)

theorem generator_weighted {V : PowerSeries ℝ} (hV : SummableWeighted V) :
    WeightedSummable (evenGenerator V) :=
  weighted_add (weighted_lift hV) (weighted_flip (weighted_lift hV))

theorem even_direction_eq {a v : Laurent} (ha : WeightedSummable a) (hv : WeightedSummable v) :
    convolution (convolution a v) (flip a)+convolution a (flip (convolution a v))=
      convolution (convolution a (flip a)) (v+flip v) := by
  have hfa := weighted_flip ha
  have hfv := weighted_flip hv
  have hfirst : convolution (convolution a v) (flip a)=convolution (convolution a (flip a)) v := by
    rw [convolution_assoc_weighted ha hv hfa,convolution_comm v (flip a),
      ← convolution_assoc_weighted ha hfa hv]
  rw [hfirst,flip_convolution,← convolution_assoc_weighted ha hfa hfv,
    convolution_add_right (weighted_convolution ha hfa) hv hfv]

/-- Weighted differentiability at every real parameter of the actual even
exponential coefficients, with the actual convolution derivative. -/
theorem even_remainder_isLittleO {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    (fun t : ℝ => weightedMass (evenExponential V (s+t)-evenExponential V s-
      t • convolution (evenExponential V s) (evenGenerator V))) =o[𝓝 0] fun t => t := by
  let a : ℝ → Laurent := fun t => positiveExponential V (s+t)
  let a1 : Laurent := convolution (positiveExponential V s) (lift V)
  have ha (t : ℝ) : WeightedSummable (a t) := positive_weighted hV0 hV (s+t)
  have ha1 : WeightedSummable a1 := weighted_convolution (positive_weighted hV0 hV s) (weighted_lift hV)
  have hr : (fun t => weightedMass (a t-a 0-t • a1)) =o[𝓝 0] fun t => t := by
    simpa only [a,a1,add_zero] using positive_remainder_isLittleO hV0 hV s
  have hf := flip_remainder_isLittleO hr
  have h := convolution_remainder_isLittleO ha (fun t => weighted_flip (ha t))
    ha1 (weighted_flip ha1) hr hf
  change (fun t => weightedMass (convolution (a t) (flip (a t))-
    convolution (a 0) (flip (a 0))-t •
      (convolution a1 (flip (a 0))+convolution (a 0) (flip a1)))) =o[𝓝 0] fun t => t at h
  simp only [a,a1,add_zero] at h
  have he := even_direction_eq (positive_weighted hV0 hV s) (weighted_lift hV)
  rw [he] at h
  exact h

theorem even_zero (V : PowerSeries ℝ) : evenExponential V 0=unitCoeff := by
  rw [evenExponential,positive_zero,flip_unit,convolution_unit_right]

theorem even_remainder_zero {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) :
    (fun t : ℝ => weightedMass (evenExponential V t-unitCoeff-t • evenGenerator V))
      =o[𝓝 0] fun t => t := by
  simpa only [zero_add,even_zero,convolution_unit_left] using even_remainder_isLittleO hV0 hV 0

end
end SpanningTreeIsoperimetry.EvenExponentialPath
