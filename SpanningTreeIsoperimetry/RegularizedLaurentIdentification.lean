module

public import SpanningTreeIsoperimetry.LaurentCircle
public import SpanningTreeIsoperimetry.RegularizedCircleFactorization
public import SpanningTreeIsoperimetry.OneSidedToeplitz

@[expose] public section

/-! The Laurent convolution of the two formal exponential factors is
identified with the actual cosine coefficients of the deformed strip
symbol. This is the analytic link used by the Toeplitz--Hankel algebra. -/
namespace SpanningTreeIsoperimetry.RegularizedLaurentIdentification
open ToeplitzHankelKernels ToeplitzHankelConvolution LaurentWeightedConvolution
open PositiveFrequencyExponential WeightedPowerSeries WeightedExponentialRemainder
open RegularizedStripSymbol RegularizedCircleFactorization EvenPeriodicFourier
open scoped BigOperators ComplexConjugate
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance : Fact (0<(2*Real.pi : ℝ)) := ⟨by positivity⟩

theorem value_lift {p : PowerSeries ℝ} (hp : SummableWeighted p) (x : PowerSeriesCircle.CircleDomain) :
    LaurentCircle.value (OneSidedToeplitz.lift p) x=PowerSeriesCircle.value p x := by
  have hs := (LaurentCircle.mode_norm_summable (OneSidedToeplitz.weighted_lift hp) x).of_norm
  have hh := tsum_nat_add_neg_add_one hs
  have hn (n : ℕ) : LaurentCircle.mode (OneSidedToeplitz.lift p) (-((n+1 : ℕ) : ℤ)) x=0 := by
    simp only [LaurentCircle.mode,OneSidedToeplitz.lift_negative p (by omega : -((n+1 : ℕ) : ℤ)<0),
      Complex.ofReal_zero,zero_mul]
  have hp' (n : ℕ) : LaurentCircle.mode (OneSidedToeplitz.lift p) (n : ℤ) x=
      PowerSeriesCircle.mode p n x := rfl
  have hh' : (∑' n : ℕ,(LaurentCircle.mode (OneSidedToeplitz.lift p) (n : ℤ) x+
      LaurentCircle.mode (OneSidedToeplitz.lift p) (-((n+1 : ℕ) : ℤ)) x))=
      LaurentCircle.value (OneSidedToeplitz.lift p) x := by
    simpa only [Nat.cast_add,Nat.cast_one,LaurentCircle.value] using hh
  simpa only [hn,hp',add_zero,PowerSeriesCircle.value] using hh'.symm

def coefficients (z t : ℝ) : Laurent :=
  convolution (OneSidedToeplitz.lift (exponential (logSeries z) t))
    (flip (OneSidedToeplitz.lift (exponential (logSeries z) t)))

def deformedSymbol (z t θ : ℝ) : ℝ := Real.exp (t*(-gammaZ z θ-coefficientZ z 0))

theorem coefficients_weighted {z : ℝ} (hz : 4<z) (t : ℝ) : WeightedSummable (coefficients z t) := by
  have hp := OneSidedToeplitz.weighted_lift
    (exponential_control (logSeries_constant z) (logSeries_weighted hz) t).1
  exact weighted_convolution hp (weighted_flip hp)

theorem value_coefficients {z : ℝ} (hz : 4<z) (t θ : ℝ) :
    LaurentCircle.value (coefficients z t) (θ : PowerSeriesCircle.CircleDomain)=
      (deformedSymbol z t θ : ℂ) := by
  have hp := (exponential_control (logSeries_constant z) (logSeries_weighted hz) t).1
  rw [coefficients,LaurentCircle.value_convolution (OneSidedToeplitz.weighted_lift hp)
    (weighted_flip (OneSidedToeplitz.weighted_lift hp)),LaurentCircle.value_flip,value_lift hp]
  exact exponential_factorization hz t θ

/-- Actual cosine coefficients, without an assumed symbol identity. -/
theorem cosineCoeff_deformedSymbol {z : ℝ} (hz : 4<z) (t : ℝ) (n : ℕ) :
    cosineCoeff (deformedSymbol z t) n=coefficients z t (n : ℤ) := by
  have hc : Continuous (deformedSymbol z t) :=
    Real.continuous_exp.comp (((contDiff_gammaZ hz).continuous.neg.sub continuous_const).const_mul t)
  have hp : Function.Periodic (deformedSymbol z t) (2*Real.pi) := by
    intro θ
    simp only [deformedSymbol,gammaZ_periodic z θ]
  have he : Function.Even (deformedSymbol z t) := by
    intro θ
    simp only [deformedSymbol,gammaZ_even z θ]
  have hv : LaurentCircle.value (coefficients z t)=circleMap (deformedSymbol z t) hc hp := by
    funext x
    induction x using QuotientAddGroup.induction_on with
    | H θ => exact value_coefficients hz t θ
  have hf := LaurentCircle.fourierCoeff_value (coefficients_weighted hz t) (n : ℤ)
  rw [hv,fourier_coefficient _ hc hp he] at hf
  simpa only [Int.natAbs_natCast,Complex.ofReal_inj] using hf

end
end SpanningTreeIsoperimetry.RegularizedLaurentIdentification
