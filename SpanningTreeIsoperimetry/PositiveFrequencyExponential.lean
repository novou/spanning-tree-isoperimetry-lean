import Mathlib.Basic.Real.Basic
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Order

/-! Positive-frequency exponential coefficients as actual formal
convolution coefficients. Zero constant term makes every coefficient a
finite polynomial in the real deformation parameter. -/
namespace SpanningTreeIsoperimetry.PositiveFrequencyExponential
open PowerSeries
open scoped BigOperators
noncomputable section

def exponential (V : PowerSeries ℝ) (t : ℝ) : PowerSeries ℝ :=
  (PowerSeries.rescale t (PowerSeries.exp ℝ)).subst V

def coefficient (V : PowerSeries ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  PowerSeries.coeff n (exponential V t)

theorem power_coefficient_zero {V : PowerSeries ℝ} (hV : V.constantCoeff=0)
    {n m : ℕ} (hnm : n<m) : PowerSeries.coeff n (V^m)=0 := by
  apply PowerSeries.coeff_of_lt_order n
  exact lt_of_lt_of_le (by exact_mod_cast hnm)
    (PowerSeries.le_order_pow_of_constantCoeff_eq_zero m hV)

/-- Only the first n+1 outer coefficients can contribute. -/
theorem coefficient_substitution {V q : PowerSeries ℝ} (hV : V.constantCoeff=0) (n : ℕ) :
    PowerSeries.coeff n (q.subst V)=
      ∑ m∈Finset.range (n+1),PowerSeries.coeff m q*PowerSeries.coeff n (V^m) := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hV)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro m hm
  simp only [Finset.mem_coe,Finset.mem_range]
  by_contra hmn
  have hz := power_coefficient_zero hV (show n<m by omega)
  change PowerSeries.coeff m q*PowerSeries.coeff n (V^m)≠0 at hm
  exact hm (by rw [hz,mul_zero])

theorem coefficient_finite {V : PowerSeries ℝ} (hV : V.constantCoeff=0) (t : ℝ) (n : ℕ) :
    coefficient V t n=∑ m∈Finset.range (n+1),
      (t^m/(m.factorial : ℝ))*PowerSeries.coeff n (V^m) := by
  rw [coefficient,exponential,coefficient_substitution hV]
  apply Finset.sum_congr rfl
  intro m _
  simp only [PowerSeries.coeff_rescale,PowerSeries.coeff_exp,map_div₀,map_one,map_natCast]
  ring

theorem exponential_zero (V : PowerSeries ℝ) : exponential V 0=1 := by
  unfold exponential
  rw [PowerSeries.rescale_zero_apply,PowerSeries.constantCoeff_exp,PowerSeries.subst_C]
  simp

theorem exponential_add {V : PowerSeries ℝ} (hV : V.constantCoeff=0) (s t : ℝ) :
    exponential V (s+t)=exponential V s*exponential V t := by
  unfold exponential
  rw [← PowerSeries.exp_mul_exp_eq_exp_add]
  exact PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hV) _ _

theorem exponential_inverse {V : PowerSeries ℝ} (hV : V.constantCoeff=0) (t : ℝ) :
    exponential V t*exponential V (-t)=1 := by
  rw [← exponential_add hV,add_neg_cancel,exponential_zero]

theorem coefficient_add {V : PowerSeries ℝ} (hV : V.constantCoeff=0) (s t : ℝ) (n : ℕ) :
    coefficient V (s+t) n=∑ p∈Finset.antidiagonal n,coefficient V s p.1*coefficient V t p.2 := by
  rw [coefficient,exponential_add hV,PowerSeries.coeff_mul]
  rfl

theorem coefficient_inverse {V : PowerSeries ℝ} (hV : V.constantCoeff=0) (t : ℝ) (n : ℕ) :
    (∑ p∈Finset.antidiagonal n,coefficient V t p.1*coefficient V (-t) p.2)=
      if n=0 then 1 else 0 := by
  rw [← coefficient_add hV,add_neg_cancel,coefficient,exponential_zero]
  simp

end
end SpanningTreeIsoperimetry.PositiveFrequencyExponential
