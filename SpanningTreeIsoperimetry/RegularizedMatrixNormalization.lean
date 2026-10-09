import SpanningTreeIsoperimetry.RegularizedLaurentIdentification
import SpanningTreeIsoperimetry.OneSidedLaurentCompatibility
import SpanningTreeIsoperimetry.RegularizedStripNormalization

/-! Exact scalar normalization connecting the actual Green boundary matrix
with the zero-mean symbol used in the determinant deformation. -/
namespace SpanningTreeIsoperimetry.RegularizedMatrixNormalization
open RegularizedLaurentIdentification RegularizedStripSymbol RegularizedBoundaryKernel
open RegularizedStripNormalization RegularizedCornerDeterminant
open ToeplitzHankelKernels ToeplitzHankelConvolution LaurentConvolutionAlgebra
open EvenPeriodicFourier FiniteSectionPadding
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem coefficients_even (z t : ℝ) : Function.Even (coefficients z t) :=
  convolution_flip_even _

theorem coefficients_eq_evenExponential (z t : ℝ) : coefficients z t=
    OneSidedLaurentCompatibility.evenExponential (RegularizedCircleFactorization.logSeries z) t := rfl

theorem deformedSymbol_one (z θ : ℝ) :
    deformedSymbol z 1 θ=Real.exp (-coefficientZ z 0)*RegularizedStripSymbol.symbol z θ := by
  unfold deformedSymbol RegularizedStripSymbol.symbol
  rw [one_mul,sub_eq_add_neg,Real.exp_add]
  ring

theorem cosine_coefficient_one (z : ℝ) (n : ℕ) :
    cosineCoeff (deformedSymbol z 1) n=Real.exp (-coefficientZ z 0)*symbolCoefficient z n := by
  unfold cosineCoeff symbolCoefficient
  simp_rw [deformedSymbol_one]
  rw [show (fun θ : ℝ => (Real.exp (-coefficientZ z 0)*RegularizedStripSymbol.symbol z θ)*Real.cos ((n : ℝ)*θ))=
      fun θ => Real.exp (-coefficientZ z 0)*(RegularizedStripSymbol.symbol z θ*Real.cos ((n : ℝ)*θ)) by
        funext θ; ring]
  rw [intervalIntegral.integral_const_mul]
  ring

theorem coefficient_one_nat {z : ℝ} (hz : 4<z) (n : ℕ) :
    coefficients z 1 (n : ℤ)=Real.exp (-coefficientZ z 0)*symbolCoefficient z n := by
  rw [← cosineCoeff_deformedSymbol hz 1 n,cosine_coefficient_one]

theorem coefficient_one_difference {z : ℝ} (hz : 4<z) (i j : ℕ) :
    coefficients z 1 ((i : ℤ)-j)=Real.exp (-coefficientZ z 0)*symbolCoefficient z (Nat.dist i j) := by
  by_cases hji : j ≤ i
  · rw [← Int.ofNat_sub hji,Nat.dist_eq_sub_of_le_right hji]
    exact coefficient_one_nat hz _
  · have hij : i ≤ j := by omega
    have he : (i : ℤ)-j= -((j : ℤ)-i) := by ring
    rw [he,coefficients_even z 1,← Int.ofNat_sub hij,Nat.dist_eq_sub_of_le hij]
    exact coefficient_one_nat hz _

def normalizedMatrix (z : ℝ) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  finiteSection (M (coefficients z 1)) k

theorem normalizedMatrix_eq {z : ℝ} (hz : 4<z) (k : ℕ) :
    normalizedMatrix z k=Real.exp (-coefficientZ z 0) • boundaryMatrix z k := by
  rw [boundaryMatrix_eq_toeplitzHankel hz]
  ext i j
  change coefficients z 1 ((i.val : ℤ)-j.val)-coefficients z 1 ((i.val+j.val+2 : ℕ) : ℤ)=
    Real.exp (-coefficientZ z 0)*(symbolCoefficient z (Nat.dist i.val j.val)-
      symbolCoefficient z (i.val+j.val+2))
  rw [coefficient_one_difference hz,coefficient_one_nat hz]
  ring

theorem normalized_det {z : ℝ} (hz : 4<z) (k : ℕ) :
    (normalizedMatrix z k).det=Real.exp (-((k : ℝ)*coefficientZ z 0))*(boundaryMatrix z k).det := by
  rw [normalizedMatrix_eq hz,Matrix.det_smul,Fintype.card_fin,← Real.exp_nat_mul]
  congr 1
  congr 1
  ring

theorem normalized_det_pos {z : ℝ} (hz : 4<z) (k : ℕ) : 0<(normalizedMatrix z k).det := by
  rw [normalized_det hz]
  exact mul_pos (Real.exp_pos _) (strip_det_pos hz.le k)

theorem normalized_logdet {z : ℝ} (hz : 4<z) (k : ℕ) :
    Real.log (normalizedMatrix z k).det=Real.log (boundaryMatrix z k).det-(k : ℝ)*coefficientZ z 0 := by
  rw [normalized_det hz,Real.log_mul (Real.exp_ne_zero _) (strip_det_pos hz.le k).ne',Real.log_exp]
  ring

/-- The actual energy relation, before identifying the bulk coefficient
through the independent matrix asymptotic. -/
theorem strip_energy_normalized {z : ℝ} (hz : 4<z) (k : ℕ) :
    StripSpectralRegularization.spectralEnergy (Ferrers.horizontalStrip k) z=
      -Real.log (normalizedMatrix z k).det-(bulkEntropy z+coefficientZ z 0)*(k : ℝ) := by
  rw [strip_energy_logdet hz.le,normalized_logdet hz]
  ring

end
end SpanningTreeIsoperimetry.RegularizedMatrixNormalization
