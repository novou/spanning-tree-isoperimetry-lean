import SpanningTreeIsoperimetry.RectangularRemainder
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! Checked arithmetic and convergent geometric moments used by the higher
rectangle correction. The full coupled-error estimate is not yet asserted. -/
namespace SpanningTreeIsoperimetry.CoupledRectangleError

open RectangularRemainder SquareMaximality.Rectangle
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def geometricMoment (k : ℕ) (q : ℝ) : ℝ := ∑' n : ℕ, (n : ℝ)^k*q^n

/-- Positive-index geometric sum; the zero mode is excluded. -/
def moment0 (q : ℝ) : ℝ := q/(1-q)
def moment1 (q : ℝ) : ℝ := q/(1-q)^2
def moment2 (q : ℝ) : ℝ := q*(1+q)/(1-q)^3

def moment3 (q : ℝ) : ℝ := q*(1+4*q+q^2)/(1-q)^4

def moment4 (q : ℝ) : ℝ := q*(1+11*q+11*q^2+q^3)/(1-q)^5

def moment5 (q : ℝ) : ℝ := q*(1+26*q+66*q^2+26*q^3+q^4)/(1-q)^6

def moment6 (q : ℝ) : ℝ := q*(1+57*q+302*q^2+302*q^3+57*q^4+q^5)/(1-q)^7

theorem geometricMoment_summable (k : ℕ) {q : ℝ} (hq : |q|<1) :
    Summable (fun n : ℕ => (n : ℝ)^k*q^n) :=
  summable_pow_mul_geometric_of_norm_lt_one k (by simpa only [Real.norm_eq_abs] using hq)

theorem moment0_hasSum {q : ℝ} (hq : |q|<1) :
    HasSum (fun n : ℕ => q^(n+1)) (moment0 q) := by
  have h := (hasSum_geometric_of_abs_lt_one hq).mul_right q
  convert h using 1 <;> simp only [pow_succ,moment0] <;> ring

theorem geometricMoment_one {q : ℝ} (hq : |q|<1) : geometricMoment 1 q=moment1 q := by
  simpa only [geometricMoment,moment1,pow_one] using
    (hasSum_coe_mul_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs] using hq)).tsum_eq

theorem geometricMoment_two {q : ℝ} (hq : |q|<1) : geometricMoment 2 q=moment2 q := by
  have hn : 1-q≠0 := by have h := (abs_lt.mp hq).2; linarith
  rw [geometricMoment,tsum_pow_mul_geometric_of_norm_lt_one 2 (by simpa only [Real.norm_eq_abs] using hq)]
  norm_num [Finset.sum_range_succ,Nat.stirlingSecond,Nat.factorial,moment2]
  field_simp [hn] <;> ring

theorem geometricMoment_three {q : ℝ} (hq : |q|<1) : geometricMoment 3 q=moment3 q := by
  have hn : 1-q≠0 := by have h := (abs_lt.mp hq).2; linarith
  rw [geometricMoment,tsum_pow_mul_geometric_of_norm_lt_one 3 (by simpa only [Real.norm_eq_abs] using hq)]
  norm_num [Finset.sum_range_succ,Nat.stirlingSecond,Nat.factorial,moment3]
  field_simp [hn] <;> ring

theorem geometricMoment_four {q : ℝ} (hq : |q|<1) : geometricMoment 4 q=moment4 q := by
  have hn : 1-q≠0 := by have h := (abs_lt.mp hq).2; linarith
  rw [geometricMoment,tsum_pow_mul_geometric_of_norm_lt_one 4 (by simpa only [Real.norm_eq_abs] using hq)]
  norm_num [Finset.sum_range_succ,Nat.stirlingSecond,Nat.factorial,moment4]
  field_simp [hn] <;> ring

theorem geometricMoment_five {q : ℝ} (hq : |q|<1) : geometricMoment 5 q=moment5 q := by
  have hn : 1-q≠0 := by have h := (abs_lt.mp hq).2; linarith
  rw [geometricMoment,tsum_pow_mul_geometric_of_norm_lt_one 5 (by simpa only [Real.norm_eq_abs] using hq)]
  norm_num [Finset.sum_range_succ,Nat.stirlingSecond,Nat.factorial,moment5]
  field_simp [hn] <;> ring

theorem geometricMoment_six {q : ℝ} (hq : |q|<1) : geometricMoment 6 q=moment6 q := by
  have hn : 1-q≠0 := by have h := (abs_lt.mp hq).2; linarith
  rw [geometricMoment,tsum_pow_mul_geometric_of_norm_lt_one 6 (by simpa only [Real.norm_eq_abs] using hq)]
  norm_num [Finset.sum_range_succ,Nat.stirlingSecond,Nat.factorial,moment6]
  field_simp [hn] <;> ring

theorem exp_four_alpha_gt_thirtythree : (33 : ℝ)<Real.exp (4*Concrete.alpha) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
  have hl : (4/3 : ℝ)<Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have he : Real.exp (4*Concrete.alpha)=(1+Real.sqrt 2)^4 := by
    simpa [Concrete.exp_alpha] using Real.exp_nat_mul Concrete.alpha 4
  rw [he]
  have heq : (1+Real.sqrt 2)^4=17+12*Real.sqrt 2 := by
    have hs3 : Real.sqrt 2^3=2*Real.sqrt 2 := by rw [pow_succ,hs]
    have hs4 : Real.sqrt 2^4=4 := by
      calc
        Real.sqrt 2^4=(Real.sqrt 2^2)^2 := by ring
        _=4 := by rw [hs]; norm_num
    nlinarith
  rw [heq]
  linarith

theorem exp_two_pi_gt_fivehundredthirty : (530 : ℝ)<Real.exp (2*Real.pi) := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤157/25) 25
  norm_num [Finset.sum_range_succ,Nat.factorial] at hs
  have hsmall : (530 : ℝ)<Real.exp (157/25) := by linarith
  exact hsmall.trans (Real.exp_lt_exp.mpr (by linarith [Real.pi_gt_d2]))

/-- Exact rational check of the uniform residual coefficient from Appendix A. -/
theorem uniform_residual_coefficient_lt :
    ((22/7 : ℝ)^3/6)*moment3 (1/33)/(1-1/33)+500/499^2<5/24 := by
  norm_num [moment3]

private def retainedSixth (d₁ d₂ : ℝ) : ℝ :=
  d₁/(d₁-1)^2+2^6*d₂/(d₂-1)^2+
    3^6*550000/(550000-1)^2+4^6*22000000/(22000000-1)^2

private def tailSixth : ℝ :=
  (moment6 (1/33)-((1/33)+2^6*(1/33)^2+3^6*(1/33)^3+4^6*(1/33)^4))/(1-1/33)^2

def fourthOrderCoefficient (d₁ d₂ tail : ℝ) : ℝ :=
  3*(22/7)^5/6048+(22/7)^5*moment5 (1/500)/(48*(1-1/500))+
    (22/7)^6/72*(retainedSixth d₁ d₂+tailSixth)+tail

theorem fourthOrderCoefficient_four_lt : fourthOrderCoefficient 396 37600 (1/1000)<1/4 := by
  norm_num [fourthOrderCoefficient,retainedSixth,tailSixth,moment5,moment6]

theorem fourthOrderCoefficient_three_lt : fourthOrderCoefficient 321 12000 (1/500)<1/3 := by
  norm_num [fourthOrderCoefficient,retainedSixth,tailSixth,moment5,moment6]

theorem curvature_coefficient_one_lt :
    (22/7 : ℝ)^3/1440*(10-4200/530+
      300*(160*moment5 (1/530)-100*moment4 (1/530)+10*moment3 (1/530)))<1 := by
  norm_num [moment3,moment4,moment5]

theorem curvature_coefficient_three_lt :
    (22/7 : ℝ)^3/1440*(22+300*(1920*moment5 ((1/530)^3)+22*moment3 ((1/530)^3)))<1/2 := by
  norm_num [moment3,moment5]

/-- A factored double-series majorant avoids a divisor-sum bound. -/
theorem curvature_double_coefficient_one_lt :
    (22/7 : ℝ)^3/1440*(10+240*530*(
      160*moment5 (1/530)*moment2 (1/530)-100*moment4 (1/530)*moment1 (1/530)+
        10*moment3 (1/530)*moment0 (1/530)))<1 := by
  norm_num [moment0,moment1,moment2,moment3,moment4,moment5]

theorem curvature_double_coefficient_three_lt :
    (22/7 : ℝ)^3/1440*(22+240*530^3*(
      1920*moment5 ((1/530)^3)*moment2 ((1/530)^3)+
        22*moment3 ((1/530)^3)*moment0 ((1/530)^3)))<1/2 := by
  norm_num [moment0,moment2,moment3,moment5]

/-- Positive polynomial multiplying each exponential in the second derivative. -/
def secondModePolynomial (b u : ℝ) : ℝ :=
  (4*b^2-16*b+10)+(8*b^2-20*b+6)*(u-1)+(5*b^2-6*b)*(u-1)^2+b^2*(u-1)^3

def fourthModePolynomial (b u : ℝ) : ℝ :=
  4*b*(b^3-8*b^2+15*b-6)+4*b^2*(2*b^2-10*b+9)*(u-1)+
    b^3*(5*b-12)*(u-1)^2+b^4*(u-1)^3

theorem secondModePolynomial_pos {b u : ℝ} (hb : 6≤b) (hu : 1≤u) : 0<secondModePolynomial b u := by
  have h0 : 0<4*b^2-16*b+10 := by nlinarith [sq_nonneg (b-6)]
  have h1 : 0<8*b^2-20*b+6 := by nlinarith [sq_nonneg (b-6)]
  have h2 : 0<5*b^2-6*b := by nlinarith [sq_nonneg (b-6)]
  have hu' : 0≤u-1 := by linarith
  unfold secondModePolynomial
  positivity

theorem fourthModePolynomial_pos {b u : ℝ} (hb : 6≤b) (hu : 1≤u) : 0<fourthModePolynomial b u := by
  have hb0 : 0<b := by linarith
  have hb' : 0≤b-6 := by linarith
  have h0 : 0<b^3-8*b^2+15*b-6 := by
    rw [show b^3-8*b^2+15*b-6=(b-6)^3+10*(b-6)^2+27*(b-6)+12 by ring]
    positivity
  have h1 : 0<2*b^2-10*b+9 := by nlinarith [sq_nonneg (b-6)]
  have h2 : 0<5*b-12 := by linarith
  have hu' : 0≤u-1 := by linarith
  unfold fourthModePolynomial
  positivity

end
end SpanningTreeIsoperimetry.CoupledRectangleError
