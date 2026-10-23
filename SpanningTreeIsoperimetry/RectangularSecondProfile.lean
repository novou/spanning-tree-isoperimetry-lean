module

public import SpanningTreeIsoperimetry.CoupledRectangleError
public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

@[expose] public section

set_option backward.privateInPublic true

/-! The genuine convergent second rectangular profile. Its modular symmetry
and curvature bounds are separate proof obligations, not inputs to a claimed
rectangle comparison. -/
namespace SpanningTreeIsoperimetry.RectangularSecondProfile

open RectangularRemainder CoupledRectangleError
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def boseCubic (u : ℝ) : ℝ :=
  ∑' n : ℕ, ((n : ℝ)+1)^3/(Real.exp (2*Real.pi*u*(n+1))-1)

def K2 (u : ℝ) : ℝ := Real.pi^3*u*(1+u)^2/1440*(1+240*boseCubic u)

private theorem bose_mode_geometric {u : ℝ} (hu : 0<u) (n : ℕ) :
    ((n : ℝ)+1)^3/(Real.exp (2*Real.pi*u*(n+1))-1)=
      ((n : ℝ)+1)^3*Real.exp (-2*Real.pi*u)^(n+1)/
        (1-Real.exp (-2*Real.pi*u)^(n+1)) := by
  have hx : 0<2*Real.pi*u*((n : ℝ)+1) := by positivity
  have he : Real.exp (2*Real.pi*u*(n+1))≠0 := (Real.exp_pos _).ne'
  have hd : Real.exp (2*Real.pi*u*(n+1))-1≠0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)).ne'
  have hpow : Real.exp (-2*Real.pi*u)^(n+1)=Real.exp (-(2*Real.pi*u*(n+1))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hpow,Real.exp_neg]
  field_simp <;> ring

theorem boseCubic_summable {u : ℝ} (hu : 0<u) :
    Summable (fun n : ℕ => ((n : ℝ)+1)^3/(Real.exp (2*Real.pi*u*(n+1))-1)) := by
  let q := Real.exp (-2*Real.pi*u)
  have hq0 : 0<q := Real.exp_pos _
  have hq1 : q<1 := by rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have hm := geometricMoment_summable 3 (show |q|<1 by rwa [abs_of_pos hq0])
  have hshift : Summable (fun n : ℕ => ((n : ℝ)+1)^3*q^(n+1)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      (summable_nat_add_iff 1).mpr hm
  apply Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hshift.div_const (1-q))
  · exact div_nonneg (by positivity)
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))).le
  · rw [bose_mode_geometric hu n]
    have hp : q^(n+1)≤q := by
      simpa using pow_le_pow_of_le_one hq0.le hq1.le (show 1≤n+1 by omega)
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)

/-- The genuine Bose correction is the Lambert/divisor series underlying E4. -/
theorem boseCubic_eq_divisor_series {u : ℝ} (hu : 0<u) :
    boseCubic u=∑' n : ℕ+, (ArithmeticFunction.sigma 3 n : ℝ)*
      Real.exp (-2*Real.pi*u)^(n : ℕ) := by
  let q := Real.exp (-2*Real.pi*u)
  have hq0 : 0<q := Real.exp_pos _
  have hq1 : q<1 := by rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have hqn : ‖q‖<1 := by simpa only [Real.norm_eq_abs,abs_of_pos hq0] using hq1
  change boseCubic u=∑' n : ℕ+, (ArithmeticFunction.sigma 3 n : ℝ)*q^(n : ℕ)
  rw [← tsum_pow_div_one_sub_eq_tsum_sigma hqn 3]
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (n : ℝ)^3*q^n/(1-q^n))]
  unfold boseCubic
  apply tsum_congr
  intro n
  simpa only [Nat.cast_add,Nat.cast_one] using bose_mode_geometric hu n

theorem boseCubic_nonneg {u : ℝ} (hu : 0<u) : 0≤boseCubic u := by
  apply tsum_nonneg
  intro n
  exact div_nonneg (by positivity)
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))).le

theorem K2_pos {u : ℝ} (hu : 0<u) : 0<K2 u := by
  have hb := boseCubic_nonneg hu
  unfold K2
  positivity

end
end SpanningTreeIsoperimetry.RectangularSecondProfile
