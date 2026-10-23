module

public import SquareMaximality.ClosedWalk.EntropySeries
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! The elementary cosine Poisson integral from a uniformly dominated
geometric series and the checked central-binomial generating function. -/
namespace SpanningTreeIsoperimetry.PoissonCosineIntegral
open MeasureTheory SquareMaximality.ClosedWalk
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def cosineMoment (n : ℕ) : ℝ := ∫ x in (0 : ℝ)..Real.pi,Real.cos x^n

theorem cosineMoment_recurrence (n : ℕ) :
    cosineMoment (n+2)=((n : ℝ)+1)/((n : ℝ)+2)*cosineMoment n := by
  unfold cosineMoment
  rw [integral_cos_pow]
  simp only [Real.sin_pi,Real.sin_zero,mul_zero,sub_zero,zero_div,zero_add]

theorem cosineMoment_even (n : ℕ) : cosineMoment (2*n)=Real.pi*normalizedCentralBinom n := by
  induction n with
  | zero => simp [cosineMoment,normalizedCentralBinom]
  | succ n ih =>
    rw [show 2*(n+1)=2*n+2 by omega,cosineMoment_recurrence,ih,normalizedCentralBinom_succ]
    push_cast
    field_simp
    <;> ring

theorem cosineMoment_odd (n : ℕ) : cosineMoment (2*n+1)=0 := by
  induction n with
  | zero => simp [cosineMoment]
  | succ n ih =>
    rw [show 2*(n+1)+1=(2*n+1)+2 by omega,cosineMoment_recurrence,ih,mul_zero]

theorem integral_geometric_term (a : ℝ) (n : ℕ) :
    (∫ x in (0 : ℝ)..Real.pi,(a*Real.cos x)^n)=a^n*cosineMoment n := by
  simp_rw [mul_pow]
  rw [intervalIntegral.integral_const_mul]
  rfl

/-- Uniform domination by |a|^n justifies integration of the geometric
series; no exchange of divergent integrals is used. -/
theorem geometric_integral_hasSum {a : ℝ} (ha : |a|<1) :
    HasSum (fun n : ℕ => ∫ x in (0 : ℝ)..Real.pi,(a*Real.cos x)^n)
      (∫ x in (0 : ℝ)..Real.pi,1/(1-a*Real.cos x)) := by
  have hlim (x : ℝ) : HasSum (fun n : ℕ => (a*Real.cos x)^n) (1/(1-a*Real.cos x)) := by
    have hx : |a*Real.cos x|<1 := by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg a) (Real.abs_cos_le_one x)).trans_lt ha
    simpa only [one_div] using hasSum_geometric_of_abs_lt_one hx
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _ => |a|^n)
  · intro n
    exact (show Continuous (fun x : ℝ => (a*Real.cos x)^n) by fun_prop).aestronglyMeasurable
  · intro n
    apply Filter.Eventually.of_forall
    intro x _
    rw [Real.norm_eq_abs,abs_pow,abs_mul]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_of_le_one_right (abs_nonneg a) (Real.abs_cos_le_one x)) n
  · exact Filter.Eventually.of_forall (fun _ _ => summable_geometric_of_abs_lt_one (by simpa using ha))
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall (fun x _ => hlim x)

theorem cosine_integral_reciprocal {a : ℝ} (ha : |a|<1) :
    (∫ x in (0 : ℝ)..Real.pi,1/(1-a*Real.cos x))=Real.pi/Real.sqrt (1-a^2) := by
  have ha2 : a^2<1 := by
    have h := mul_self_lt_mul_self (abs_nonneg a) ha
    simpa only [← pow_two,sq_abs,one_pow] using h
  have harg : |4*(a^2/4)|<1 := by
    rw [show 4*(a^2/4)=a^2 by ring,abs_of_nonneg (sq_nonneg a)]
    exact ha2
  have hc := (hasSum_centralBinom_mul_pow harg).mul_left Real.pi
  have hc' : HasSum (fun n : ℕ => Real.pi*((Nat.centralBinom n : ℝ)*(a^2/4)^n))
      (Real.pi/Real.sqrt (1-a^2)) := by
    simpa only [show 4*(a^2/4)=a^2 by ring,mul_one_div] using hc
  have heven : HasSum (fun n : ℕ => ∫ x in (0 : ℝ)..Real.pi,(a*Real.cos x)^(2*n))
      (Real.pi/Real.sqrt (1-a^2)) := by
    apply hc'.congr_fun
    intro n
    rw [integral_geometric_term,cosineMoment_even,normalizedCentralBinom,div_pow,
      show a^(2*n)=(a^2)^n by rw [pow_mul]]
    ring
  have hodd : HasSum (fun n : ℕ => ∫ x in (0 : ℝ)..Real.pi,(a*Real.cos x)^(2*n+1)) 0 := by
    simpa only [integral_geometric_term,cosineMoment_odd,mul_zero] using
      (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  have hsum := HasSum.even_add_odd (f := fun n : ℕ =>
    ∫ x in (0 : ℝ)..Real.pi,(a*Real.cos x)^n) heven hodd
  simp only [add_zero] at hsum
  exact (geometric_integral_hasSum ha).unique hsum

end
end SpanningTreeIsoperimetry.PoissonCosineIntegral
