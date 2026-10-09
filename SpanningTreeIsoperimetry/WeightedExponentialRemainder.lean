import SpanningTreeIsoperimetry.WeightedPowerSeries
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.IntervalCases

/-! True weighted coefficient control of the positive-frequency
exponential and its remainder. All bounds concern actual coefficient sums. -/
namespace SpanningTreeIsoperimetry.WeightedExponentialRemainder
open PowerSeries PositiveFrequencyExponential WeightedPowerSeries Filter Asymptotics
open scoped BigOperators Topology
noncomputable section

def outer (t : ℝ) : PowerSeries ℝ := PowerSeries.rescale t (PowerSeries.exp ℝ)
def outerRemainder (t : ℝ) : PowerSeries ℝ := outer t-1-PowerSeries.C t*PowerSeries.X

theorem outer_coefficient (t : ℝ) (m : ℕ) : PowerSeries.coeff m (outer t)=t^m/(m.factorial : ℝ) := by
  simp only [outer,PowerSeries.coeff_rescale,PowerSeries.coeff_exp,map_div₀,map_one,map_natCast]
  ring


theorem outer_constant (t : ℝ) : PowerSeries.constantCoeff (outer t)=1 := by
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply,pow_zero,Nat.factorial_zero,
    Nat.cast_one,div_one] using outer_coefficient t 0

private theorem exponential_hasSum (x : ℝ) : HasSum (fun m : ℕ => x^m/(m.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

theorem outer_majorant (t M : ℝ) (m : ℕ) :
    |PowerSeries.coeff m (outer t)| * M^m=(|t| * M)^m/(m.factorial : ℝ) := by
  rw [outer_coefficient,abs_div,abs_pow,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) m.factorial),mul_pow]
  ring

theorem outerRemainder_coefficient (t : ℝ) (m : ℕ) :
    |PowerSeries.coeff m (outerRemainder t)|=
      if 2≤m then |t|^m/(m.factorial : ℝ) else 0 := by
  by_cases hm : 2≤m
  · have hm0 : m≠0 := by omega
    have hm1 : m≠1 := by omega
    simp only [outerRemainder,map_sub,PowerSeries.coeff_C_mul,PowerSeries.coeff_X,
      PowerSeries.coeff_one,outer_coefficient,hm0,hm1,ite_false,mul_zero,sub_zero,if_pos hm,
      abs_div,abs_pow,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) m.factorial)]
  · have hm2 : m≤1 := by omega
    interval_cases m <;> norm_num [outerRemainder,outer_coefficient,outer_constant]

theorem outerRemainder_majorant (t M : ℝ) (m : ℕ) :
    |PowerSeries.coeff m (outerRemainder t)| * M^m=
      if 2≤m then (|t| * M)^m/(m.factorial : ℝ) else 0 := by
  rw [outerRemainder_coefficient]
  split_ifs <;> simp only [mul_pow,zero_mul] <;> ring

private theorem tail_hasSum (x : ℝ) :
    HasSum (fun m : ℕ => if 2≤m then x^m/(m.factorial : ℝ) else 0) (Real.exp x-1-x) := by
  have hs := exponential_hasSum x
  have hsi : Summable (fun m : ℕ => if 2≤m then x^m/(m.factorial : ℝ) else 0) := by
    convert! hs.summable.indicator {m : ℕ | 2≤m} using 1
    funext m
    simp only [Set.indicator_apply,Set.mem_setOf_eq]
  have hfull := hs.summable.sum_add_tsum_nat_add 2
  have htail := hsi.sum_add_tsum_nat_add 2
  norm_num [Finset.sum_range_succ,hs.tsum_eq] at hfull htail
  apply hsi.hasSum_iff.mpr
  linarith

/-- Weighted absolute summability is proved, together with its exponential
majorant, for every real deformation parameter. -/
theorem exponential_control {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (t : ℝ) :
    SummableWeighted (exponential V t) ∧ mass (exponential V t)≤Real.exp (|t| * mass V) := by
  have hs : Summable (fun m => |PowerSeries.coeff m (outer t)| * (mass V)^m) := by
    simpa only [outer_majorant] using (exponential_hasSum (|t| * mass V)).summable
  have h := subst_control (q := outer t) hV0 hV hs
  change SummableWeighted (exponential V t) ∧ mass (exponential V t)≤_ at h
  have he : (∑' m,|PowerSeries.coeff m (outer t)| * (mass V)^m)=Real.exp (|t| * mass V) := by
    simpa only [outer_majorant] using (exponential_hasSum (|t| * mass V)).tsum_eq
  exact ⟨h.1,h.2.trans_eq he⟩

def remainder (V : PowerSeries ℝ) (t : ℝ) : PowerSeries ℝ := exponential V t-1-PowerSeries.C t*V

theorem remainder_eq_subst {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (t : ℝ) :
    remainder V t=(outerRemainder t).subst V := by
  have h := PowerSeries.HasSubst.of_constantCoeff_zero' hV0
  have h1 : (1 : PowerSeries ℝ).subst V=1 := by
    rw [show (1 : PowerSeries ℝ)=PowerSeries.C (1 : ℝ) by simp,PowerSeries.subst_C]
    simp
  have hc : (PowerSeries.C t : PowerSeries ℝ).subst V=PowerSeries.C t := by
    rw [PowerSeries.subst_C]
    rfl
  simp only [remainder,outerRemainder,exponential,outer,PowerSeries.subst_sub h,
    PowerSeries.subst_mul h,PowerSeries.subst_X h,h1,hc]

/-- The full weighted remainder, not merely each individual coefficient,
is controlled by the scalar exponential remainder. -/
theorem remainder_control {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (t : ℝ) :
    SummableWeighted (remainder V t) ∧
      mass (remainder V t)≤Real.exp (|t| * mass V)-1-|t| * mass V := by
  have hs : Summable (fun m => |PowerSeries.coeff m (outerRemainder t)| * (mass V)^m) := by
    simpa only [outerRemainder_majorant] using (tail_hasSum (|t| * mass V)).summable
  have h := subst_control (q := outerRemainder t) hV0 hV hs
  rw [← remainder_eq_subst hV0] at h
  have he : (∑' m,|PowerSeries.coeff m (outerRemainder t)| * (mass V)^m)=
      Real.exp (|t| * mass V)-1-|t| * mass V := by
    simpa only [outerRemainder_majorant] using (tail_hasSum (|t| * mass V)).tsum_eq
  exact ⟨h.1,h.2.trans_eq he⟩

/-- The semigroup identity transports the weighted remainder to any base
parameter, preparing the actual weighted differentiability estimate. -/
theorem shifted_remainder_identity {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (s t : ℝ) :
    exponential V (s+t)-exponential V s-PowerSeries.C t*(exponential V s*V)=
      exponential V s*remainder V t := by
  rw [exponential_add hV0,remainder]
  ring

theorem shifted_remainder_summable {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s t : ℝ) :
    SummableWeighted (exponential V (s+t)-exponential V s-PowerSeries.C t*(exponential V s*V)) := by
  rw [shifted_remainder_identity hV0]
  exact mul_summable (exponential_control hV0 hV s).1 (remainder_control hV0 hV t).1

theorem shifted_remainder_mass_le {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s t : ℝ) :
    mass (exponential V (s+t)-exponential V s-PowerSeries.C t*(exponential V s*V))≤
      Real.exp (|s| * mass V)*(Real.exp (|t| * mass V)-1-|t| * mass V) := by
  rw [shifted_remainder_identity hV0]
  have hs := exponential_control hV0 hV s
  have ht := remainder_control hV0 hV t
  exact (mass_mul_le hs.1 ht.1).trans (mul_le_mul hs.2 ht.2 (mass_nonneg _) (Real.exp_pos _).le)


/-- Differentiability in the actual weighted coefficient mass, obtained
from the global remainder estimate rather than coefficientwise limits. -/
theorem shifted_remainder_isLittleO {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    (fun t : ℝ => mass (exponential V (s+t)-exponential V s-
      PowerSeries.C t*(exponential V s*V))) =o[𝓝 0] (fun t => t) := by
  let M := mass V
  have hM : 0≤M := mass_nonneg V
  have hlim : Tendsto (fun t : ℝ => |t| * M) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.continuousAt.tendsto.mul_const M :
      Tendsto (fun t : ℝ => |t| * M) (𝓝 0) (𝓝 (|0| * M)))
  have he : (fun t : ℝ => Real.exp (|t| * M)-1-|t| * M) =o[𝓝 0] (fun t => |t| * M) := by
    have h := (Real.exp_sub_sum_range_succ_isLittleO_pow 1).comp_tendsto hlim
    simpa [Function.comp_def,Finset.sum_range_succ,sub_add_eq_sub_sub] using h
  have hi : (fun t : ℝ => |t| * M) =O[𝓝 0] (fun t => t) := by
    apply IsBigO.of_bound M
    exact Eventually.of_forall (fun t => by
      simp only [Real.norm_eq_abs,abs_mul,abs_abs,abs_of_nonneg hM]
      exact le_of_eq (mul_comm _ _))
  have hb : (fun t : ℝ => mass (exponential V (s+t)-exponential V s-
      PowerSeries.C t*(exponential V s*V))) =O[𝓝 0]
        (fun t : ℝ => Real.exp (|t| * M)-1-|t| * M) := by
    apply IsBigO.of_bound (Real.exp (|s| * M))
    apply Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs,abs_of_nonneg (mass_nonneg _),Real.norm_eq_abs]
    exact (shifted_remainder_mass_le hV0 hV s t).trans
      (mul_le_mul_of_nonneg_left (le_abs_self _) (Real.exp_pos _).le)
  exact hb.trans_isLittleO (he.trans_isBigO hi)

end
end SpanningTreeIsoperimetry.WeightedExponentialRemainder
