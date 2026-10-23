module

public import SpanningTreeIsoperimetry.LaurentWeightedConvolution
public import SpanningTreeIsoperimetry.PowerSeriesCircleFourier

@[expose] public section

/-! Actual Fourier evaluation of weighted real Laurent coefficients,
including convolution and coefficient extraction. -/
namespace SpanningTreeIsoperimetry.LaurentCircle
open ToeplitzHankelKernels ToeplitzHankelConvolution LaurentWeightedConvolution
open PowerSeriesCircle MeasureTheory AddCircle
open scoped BigOperators ComplexConjugate
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance : Fact (0<(2*Real.pi : ℝ)) := ⟨by positivity⟩

def mode (a : Laurent) (n : ℤ) (x : CircleDomain) : ℂ := (a n : ℂ)*fourier n x
def value (a : Laurent) (x : CircleDomain) : ℂ := ∑' n : ℤ,mode a n x

theorem norm_mode (a : Laurent) (n : ℤ) (x : CircleDomain) : ‖mode a n x‖=|a n| := by
  rw [mode,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have h : ‖fourier n x‖=1 := Circle.norm_coe _
  rw [h,mul_one]

theorem mode_norm_summable {a : Laurent} (ha : WeightedSummable a) (x : CircleDomain) :
    Summable (fun n => ‖mode a n x‖) := by simpa only [norm_mode] using summable_abs ha

theorem continuous_value {a : Laurent} (ha : WeightedSummable a) : Continuous (value a) := by
  apply continuous_tsum (fun n => continuous_const.mul (fourier n).continuous) (summable_abs ha)
  intro n x
  exact (norm_mode a n x).le

theorem mode_convolution (a b : Laurent) (n : ℤ) (x : CircleDomain) :
    mode (convolution a b) n x=∑' k : ℤ,mode a (n-k) x*mode b k x := by
  rw [mode,convolution,Complex.ofReal_tsum,← tsum_mul_right]
  apply tsum_congr
  intro k
  have hf : fourier n x=fourier (n-k) x*fourier k x := by
    simpa only [sub_add_cancel] using (fourier_add (m := n-k) (n := k) (x := x))
  rw [Complex.ofReal_mul,hf]
  unfold mode
  ring

theorem value_convolution {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b)
    (x : CircleDomain) : value (convolution a b) x=value a x*value b x := by
  let F : ℤ×ℤ → ℂ := fun p => mode a p.1 x*mode b p.2 x
  have hF : Summable F := summable_mul_of_summable_norm
    (f := fun n : ℤ => mode a n x) (g := fun n : ℤ => mode b n x)
    (mode_norm_summable ha x) (mode_norm_summable hb x)
  have hshear : Summable (fun p : ℤ×ℤ => F (convolutionShear p)) :=
    hF.comp_injective convolutionShear.injective
  unfold value
  simp_rw [mode_convolution]
  calc
    _=∑' p : ℤ×ℤ,F (convolutionShear p) := hshear.tsum_prod.symm
    _=∑' p : ℤ×ℤ,F p := convolutionShear.tsum_eq F
    _=_ := (tsum_mul_tsum_of_summable_norm (mode_norm_summable ha x) (mode_norm_summable hb x)).symm

theorem value_flip (a : Laurent) (x : CircleDomain) : value (flip a) x=conj (value a x) := by
  have hm (n : ℤ) : mode (flip a) n x=conj (mode a (-n) x) := by
    simp [mode,ToeplitzHankelKernels.flip,fourier_neg]
  unfold value
  simp_rw [hm]
  rw [← Complex.conj_tsum]
  exact congrArg (fun z : ℂ => conj z) ((Equiv.neg ℤ).tsum_eq (fun n => mode a n x))

/-- The actual Fourier coefficient of the evaluated Laurent series is the
specified coefficient, by absolutely convergent termwise integration. -/
theorem fourierCoeff_value {a : Laurent} (ha : WeightedSummable a) (m : ℤ) :
    fourierCoeff (value a) m=(a m : ℂ) := by
  let F : ℤ → CircleDomain → ℂ := fun n x => fourier (-m) x*mode a n x
  have hc (n : ℤ) : Continuous (F n) :=
    (fourier (-m)).continuous.mul (continuous_const.mul (fourier n).continuous)
  have hi (n : ℤ) : Integrable (F n) haarAddCircle :=
    (hc n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hn (n : ℤ) (x : CircleDomain) : ‖F n x‖=|a n| := by
    dsimp only [F]
    rw [norm_mul,norm_mode]
    have hf : ‖fourier (-m) x‖=1 := Circle.norm_coe _
    rw [hf,one_mul]
  have hni (n : ℤ) : (∫ x,‖F n x‖ ∂haarAddCircle)=|a n| := by simp only [hn]; simp
  have hs : Summable (fun n => ∫ x,‖F n x‖ ∂haarAddCircle) := by
    simpa only [hni] using summable_abs ha
  have he := integral_tsum_of_summable_integral_norm hi hs
  have hcseries : fourierCoeff (value a) m=∑' n : ℤ,fourierCoeff (mode a n) m := by
    unfold fourierCoeff value
    simp only [smul_eq_mul]
    simp_rw [← tsum_mul_left]
    exact he.symm
  rw [hcseries]
  have ht (n : ℤ) : fourierCoeff (mode a n) m=if n=m then (a m : ℂ) else 0 := by
    change fourierCoeff (fun x : CircleDomain => (a n : ℂ)*fourier n x) m=_
    rw [fourierCoeff.const_mul,fourierCoeff_fourier]
    by_cases hn : n=m
    · subst n
      simp
    · simp [hn,Ne.symm hn]
  simp_rw [ht]
  simp

end
end SpanningTreeIsoperimetry.LaurentCircle
