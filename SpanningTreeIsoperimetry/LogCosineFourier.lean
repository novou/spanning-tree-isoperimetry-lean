import SpanningTreeIsoperimetry.RegularizedLaurentIdentification
import SpanningTreeIsoperimetry.OneSidedLaurentCompatibility
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! The exact log-cosine Fourier identity on the open unit disk. The
Taylor series is the checked complex logarithm series; coefficient
extraction uses the checked absolutely summable Laurent Fourier expansion. -/
namespace SpanningTreeIsoperimetry.LogCosineFourier
open ToeplitzHankelKernels LaurentWeightedConvolution OneSidedToeplitz
open WeightedPowerSeries PowerSeriesCircle EvenPeriodicFourier
open scoped ComplexConjugate
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance : Fact (0<(2*Real.pi : ℝ)) := ⟨by positivity⟩

def series (q : ℝ) : PowerSeries ℝ := PowerSeries.mk (fun n => -q^n/(n : ℝ))
def coefficients (q : ℝ) : Laurent := lift (series q)+flip (lift (series q))
def argument (q θ : ℝ) : ℝ := 1-2*q*Real.cos θ+q^2
def logCosine (q θ : ℝ) : ℝ := Real.log (argument q θ)

@[simp] theorem coefficient_series (q : ℝ) (n : ℕ) : PowerSeries.coeff n (series q)= -q^n/(n : ℝ) :=
  PowerSeries.coeff_mk _ _

theorem series_weighted {q : ℝ} (hq0 : 0≤q) (hq : q<1) : SummableWeighted (series q) := by
  have hgeo : Summable (fun n : ℕ => q^n) := summable_geometric_of_abs_lt_one (by simpa [abs_of_nonneg hq0] using hq)
  apply Summable.of_nonneg_of_le (term_nonneg _) _ (hgeo.mul_left 2)
  intro n
  by_cases hn : n=0
  · subst n
    simp [term]
  have hn1 : (1 : ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hn0 : (0 : ℝ)<n := by positivity
  have hw : (1+(n : ℝ))/(n : ℝ)≤2 := (div_le_iff₀ hn0).mpr (by linarith)
  calc
    term (series q) n=((1+(n : ℝ))/(n : ℝ))*q^n := by
      simp only [term,coefficient_series,neg_div,abs_neg,abs_of_nonneg (div_nonneg (pow_nonneg hq0 _) hn0.le)]
      ring
    _≤2*q^n := mul_le_mul_of_nonneg_right hw (pow_nonneg hq0 _)

theorem coefficients_weighted {q : ℝ} (hq0 : 0≤q) (hq : q<1) : WeightedSummable (coefficients q) :=
  weighted_add (weighted_lift (series_weighted hq0 hq)) (weighted_flip (weighted_lift (series_weighted hq0 hq)))

private theorem fourier_nat_pow (n : ℕ) (x : CircleDomain) :
    fourier (n : ℤ) x=(fourier 1 x)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,fourier_add,ih,pow_succ]

/-- Circle evaluation of the real formal log series equals the actual
principal complex logarithm throughout the open unit disk. -/
theorem value_series {q : ℝ} (hq0 : 0≤q) (hq : q<1) (x : CircleDomain) :
    PowerSeriesCircle.value (series q) x=Complex.log (1-(q : ℂ)*fourier 1 x) := by
  let z : ℂ := (q : ℂ)*fourier 1 x
  have hz : ‖z‖<1 := by
    dsimp only [z]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hq0,
      show ‖fourier (1 : ℤ) x‖=1 from Circle.norm_coe _,mul_one]
    exact hq
  have hm (n : ℕ) : PowerSeriesCircle.mode (series q) n x= -(z^n/(n : ℂ)) := by
    rw [PowerSeriesCircle.mode,coefficient_series,fourier_nat_pow]
    dsimp only [z]
    push_cast
    rw [mul_pow]
    ring
  have hs := (Complex.hasSum_taylorSeries_neg_log hz).neg
  simp only [neg_neg] at hs
  unfold PowerSeriesCircle.value
  simp_rw [hm]
  exact hs.tsum_eq

private theorem value_add {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b)
    (x : CircleDomain) : LaurentCircle.value (a+b) x=LaurentCircle.value a x+LaurentCircle.value b x := by
  unfold LaurentCircle.value
  have he (n : ℤ) : LaurentCircle.mode (a+b) n x=LaurentCircle.mode a n x+LaurentCircle.mode b n x := by
    simp only [LaurentCircle.mode,Pi.add_apply,Complex.ofReal_add,add_mul]
  simp_rw [he]
  exact ((LaurentCircle.mode_norm_summable ha x).of_norm).tsum_add
    ((LaurentCircle.mode_norm_summable hb x).of_norm)

theorem argument_pos {q : ℝ} (hq0 : 0≤q) (hq : q<1) (θ : ℝ) : 0<argument q θ := by
  have h := mul_nonneg hq0 (sub_nonneg.mpr (Real.cos_le_one θ))
  have hs : 0<(1-q)^2 := sq_pos_of_pos (sub_pos.mpr hq)
  unfold argument
  nlinarith

private theorem normSq_identity (q θ : ℝ) :
    Complex.normSq (1-(q : ℂ)*fourier (1 : ℤ) (θ : CircleDomain))=argument q θ := by
  rw [fourier_frequency]
  norm_num only [Int.cast_one,one_mul]
  rw [Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos,← Complex.ofReal_sin,Complex.normSq_apply,
    Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.add_re,Complex.add_im,Complex.I_re,Complex.I_im]
  have h := congrArg (fun z : ℝ => q^2*z) (Real.sin_sq_add_cos_sq θ)
  unfold argument
  nlinarith [h]

theorem value_coefficients {q : ℝ} (hq0 : 0≤q) (hq : q<1) (θ : ℝ) :
    LaurentCircle.value (coefficients q) (θ : CircleDomain)=(logCosine q θ : ℂ) := by
  have hp := weighted_lift (series_weighted hq0 hq)
  rw [coefficients,value_add hp (weighted_flip hp),LaurentCircle.value_flip,
    RegularizedLaurentIdentification.value_lift (series_weighted hq0 hq),value_series hq0 hq]
  have hr : logCosine q θ=2*(Complex.log (1-(q : ℂ)*fourier 1 (θ : CircleDomain))).re := by
    rw [logCosine,← normSq_identity,Complex.normSq_eq_norm_sq,Real.log_pow,Complex.log_re]
    norm_num
  apply Complex.ext
  · simp only [Complex.add_re,Complex.conj_re,Complex.ofReal_re]
    linarith
  · simp only [Complex.add_im,Complex.conj_im,Complex.ofReal_im]
    ring

theorem cosineCoeff_logCosine {q : ℝ} (hq0 : 0≤q) (hq : q<1) (n : ℕ) :
    cosineCoeff (logCosine q) n=coefficients q (n : ℤ) := by
  have hc : Continuous (logCosine q) := by
    apply Continuous.log _ (fun θ => (argument_pos hq0 hq θ).ne')
    unfold argument
    fun_prop
  have hp : Function.Periodic (logCosine q) (2*Real.pi) := by
    intro θ
    simp only [logCosine,argument,Real.cos_add_two_pi]
  have he : Function.Even (logCosine q) := by
    intro θ
    simp only [logCosine,argument,Real.cos_neg]
  have hv : LaurentCircle.value (coefficients q)=circleMap (logCosine q) hc hp := by
    funext x
    induction x using QuotientAddGroup.induction_on with
    | H θ => exact value_coefficients hq0 hq θ
  have hf := LaurentCircle.fourierCoeff_value (coefficients_weighted hq0 hq) (n : ℤ)
  rw [hv,fourier_coefficient _ hc hp he] at hf
  simpa only [Int.natAbs_natCast,Complex.ofReal_inj] using hf

/-- The constant Fourier mode vanishes, including q=0. -/
theorem mean_zero {q : ℝ} (hq0 : 0≤q) (hq : q<1) :
    (1/Real.pi)*(∫ θ in (0 : ℝ)..Real.pi,Real.log (1-2*q*Real.cos θ+q^2))=0 := by
  have h := cosineCoeff_logCosine hq0 hq 0
  simpa only [cosineCoeff,logCosine,argument,coefficients,Pi.add_apply,
    ToeplitzHankelKernels.flip,Nat.cast_zero,neg_zero,lift,lift_nat,coefficient_series,
    pow_zero,div_zero,add_zero,zero_mul,Real.cos_zero,mul_one] using h

/-- The exact normalized cosine coefficient printed in Appendix A. -/
theorem cosine_coefficient {q : ℝ} (hq0 : 0≤q) (hq : q<1) {j : ℕ} (hj : 0<j) :
    (1/Real.pi)*(∫ θ in (0 : ℝ)..Real.pi,
      Real.log (1-2*q*Real.cos θ+q^2)*Real.cos ((j : ℝ)*θ))= -q^j/(j : ℝ) := by
  have h := cosineCoeff_logCosine hq0 hq j
  have hn : -((j : ℕ) : ℤ)<0 := by omega
  simpa only [cosineCoeff,logCosine,argument,coefficients,Pi.add_apply,
    ToeplitzHankelKernels.flip,lift_nat,lift_negative (series q) hn,coefficient_series,add_zero] using h

end
end SpanningTreeIsoperimetry.LogCosineFourier
