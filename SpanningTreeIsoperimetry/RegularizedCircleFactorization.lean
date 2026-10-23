module

public import SpanningTreeIsoperimetry.PowerSeriesCircleExponential
public import SpanningTreeIsoperimetry.RegularizedFourierWeighted
public import SpanningTreeIsoperimetry.RegularizedFourierQuadraticLimit
public import SpanningTreeIsoperimetry.EvenFourierReconstruction

@[expose] public section

set_option backward.privateInPublic true

/-! Actual positive-frequency factors of the regularized strip symbol.
The zero mode is separated explicitly; all remaining coefficients are the
printed cosine coefficients of minus gamma. -/
namespace SpanningTreeIsoperimetry.RegularizedCircleFactorization
open PowerSeriesCircle WeightedPowerSeries PositiveFrequencyExponential
open RegularizedStripSymbol RegularizedFourierWeighted EvenPeriodicFourier EvenFourierReconstruction
open scoped BigOperators ComplexConjugate
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance : Fact (0<(2*Real.pi : ℝ)) := ⟨by positivity⟩

def logSeries (z : ℝ) : PowerSeries ℝ := PowerSeries.mk (positivePart z)

@[simp] theorem logSeries_coefficient (z : ℝ) (n : ℕ) :
    PowerSeries.coeff n (logSeries z)=positivePart z n := PowerSeries.coeff_mk _ _

@[simp] theorem logSeries_constant (z : ℝ) : (logSeries z).constantCoeff=0 := by
  simp [logSeries,PowerSeries.constantCoeff_mk]

theorem logSeries_weighted {z : ℝ} (hz : 4<z) : SummableWeighted (logSeries z) := by
  change Summable (fun n : ℕ => (1+(n : ℝ))*|PowerSeries.coeff n (logSeries z)|)
  simpa only [logSeries_coefficient] using positivePart_weighted_summable hz

private theorem mode_zero (z : ℝ) (x : CircleDomain) : mode (logSeries z) 0 x=0 := by
  simp [mode]

private theorem mode_succ (z : ℝ) (n : ℕ) (x : CircleDomain) :
    mode (logSeries z) (n+1) x=(coefficientZ z (n+1) : ℂ)*fourier ((n+1 : ℕ) : ℤ) x := by
  simp only [mode,logSeries_coefficient,positivePart_succ]

theorem value_eq_shifted {z : ℝ} (hz : 4<z) (x : CircleDomain) :
    value (logSeries z) x=∑' n : ℕ,(coefficientZ z (n+1) : ℂ)*fourier ((n+1 : ℕ) : ℤ) x := by
  have h := (mode_summable (logSeries_weighted hz) x).sum_add_tsum_nat_add 1
  simpa only [Finset.sum_range_one,mode_zero,zero_add,mode_succ,value] using h.symm

/-- Full even Fourier reconstruction identifies the two one-sided log
factors with the actual zero-mean logarithmic symbol. -/
theorem log_factorization {z : ℝ} (hz : 4<z) (θ : ℝ) :
    value (logSeries z) (θ : CircleDomain)+conj (value (logSeries z) (θ : CircleDomain))=
      ((-gammaZ z θ-coefficientZ z 0 : ℝ) : ℂ) := by
  let f : ℝ → ℝ := fun θ => -gammaZ z θ
  have hc : Continuous f := (contDiff_gammaZ hz).continuous.neg
  have hp : Function.Periodic f (2*Real.pi) :=
    fun θ => congrArg Neg.neg (gammaZ_periodic z θ)
  have he : Function.Even f := fun x => congrArg Neg.neg (gammaZ_even z x)
  have hs : Summable (cosineCoeff f) := by
    change Summable (coefficientZ z)
    exact (summable_nat_add_iff 1).mp
      (RegularizedFourierQuadraticLimit.coefficient_abs_summable hz.le).of_abs
  have hf := has_pointwise_sum_fourier_series_of_summable (fourier_summable f hc hp he hs)
    (θ : CircleDomain)
  let F : ℤ → ℂ := fun n => (coefficientZ z n.natAbs : ℂ)*fourier n (θ : CircleDomain)
  have hF : HasSum F ((-gammaZ z θ : ℝ) : ℂ) := by
    convert hf using 1
    · funext n
      simp only [smul_eq_mul,fourier_coefficient f hc hp he]
      rfl
    · rfl
  have hpos : Summable (fun n : ℕ => F (n : ℤ)) :=
    hF.summable.comp_injective Nat.cast_injective
  have hneg : Summable (fun n : ℕ => F (-((n+1 : ℕ) : ℤ))) :=
    hF.summable.comp_injective (fun a b h => by omega)
  have hposval : (∑' n : ℕ,F (n : ℤ))=(coefficientZ z 0 : ℂ)+value (logSeries z) (θ : CircleDomain) := by
    have hh := hpos.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one] at hh
    rw [← hh,value_eq_shifted hz]
    simp only [F,Int.natAbs_natCast,Nat.cast_zero,Int.natAbs_zero,fourier_zero,mul_one]
  have hnegval : (∑' n : ℕ,F (-((n+1 : ℕ) : ℤ)))=conj (value (logSeries z) (θ : CircleDomain)) := by
    rw [value_eq_shifted hz,Complex.conj_tsum]
    apply tsum_congr
    intro n
    simp only [F,Int.natAbs_neg,Int.natAbs_natCast,fourier_neg,map_mul,Complex.conj_ofReal]
  have ht := tsum_nat_add_neg_add_one hF.summable
  have ht' : (∑' n : ℕ,(F (n : ℤ)+F (-((n+1 : ℕ) : ℤ))))=∑' n : ℤ,F n := by
    simpa only [Nat.cast_add,Nat.cast_one] using ht
  rw [hpos.tsum_add hneg,hposval,hnegval,hF.tsum_eq] at ht'
  push_cast at ht' ⊢
  linear_combination ht'

/-- The actual exponential factors multiply to the zero-mean real strip
symbol for every real deformation parameter. -/
theorem exponential_factorization {z : ℝ} (hz : 4<z) (t θ : ℝ) :
    value (exponential (logSeries z) t) (θ : CircleDomain)*
      conj (value (exponential (logSeries z) t) (θ : CircleDomain))=
      ((Real.exp (t*(-gammaZ z θ-coefficientZ z 0)) : ℝ) : ℂ) := by
  rw [value_exponential (logSeries_constant z) (logSeries_weighted hz),← Complex.exp_conj,
    map_mul,Complex.conj_ofReal,← Complex.exp_add,← mul_add,log_factorization hz]
  rw [← Complex.ofReal_mul,Complex.ofReal_exp]

end
end SpanningTreeIsoperimetry.RegularizedCircleFactorization
