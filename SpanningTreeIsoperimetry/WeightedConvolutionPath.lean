import SpanningTreeIsoperimetry.WeightedBilinearPath

/-! The actual weighted Laurent convolution obeys the ordinary Leibniz
remainder rule, proved from concrete summability and mass estimates. -/
namespace SpanningTreeIsoperimetry.WeightedConvolutionPath
open ToeplitzHankelKernels ToeplitzHankelConvolution LaurentWeightedConvolution
open WeightedLaurentPath WeightedBilinearPath Filter Asymptotics
open scoped Topology
noncomputable section

def laurentMass : MassData Laurent where
  regular := WeightedSummable
  mass := weightedMass
  nonneg := weightedMass_nonneg
  add_regular := weighted_add
  smul_regular := weighted_smul
  add_le := weightedMass_add_le
  smul_mass := fun t a => weightedMass_smul a t

def convolutionData : BilinearData laurentMass where
  map := convolution
  regular := weighted_convolution
  bound := weightedMass_convolution_le
  add_left := convolution_add_left
  add_right := convolution_add_right
  smul_left := fun t a b => convolution_smul_left a b t
  smul_right := fun t a b => convolution_smul_right a b t

theorem convolution_remainder_isLittleO {a b : ℝ → Laurent} {a1 b1 : Laurent}
    (ha : ∀ t,WeightedSummable (a t)) (hb : ∀ t,WeightedSummable (b t))
    (ha1 : WeightedSummable a1) (hb1 : WeightedSummable b1)
    (hra : (fun t => weightedMass (a t-a 0-t • a1)) =o[𝓝 0] fun t => t)
    (hrb : (fun t => weightedMass (b t-b 0-t • b1)) =o[𝓝 0] fun t => t) :
    (fun t => weightedMass (convolution (a t) (b t)-convolution (a 0) (b 0)-
      t • (convolution a1 (b 0)+convolution (a 0) b1))) =o[𝓝 0] fun t => t :=
  remainder_isLittleO convolutionData ha hb ha1 hb1 hra hrb

/-- Reflection of actual Laurent coefficients preserves the same weighted
remainder estimate, as needed by positive/negative spectral factors. -/
theorem flip_remainder_isLittleO {a : ℝ → Laurent} {a1 : Laurent}
    (hra : (fun t => weightedMass (a t-a 0-t • a1)) =o[𝓝 0] fun t => t) :
    (fun t => weightedMass (flip (a t)-flip (a 0)-t • flip a1)) =o[𝓝 0] fun t => t := by
  apply hra.congr_left
  intro t
  have he : flip (a t)-flip (a 0)-t • flip a1=flip (a t-a 0-t • a1) := by
    funext n
    rfl
  rw [he,weightedMass_flip]

end
end SpanningTreeIsoperimetry.WeightedConvolutionPath
