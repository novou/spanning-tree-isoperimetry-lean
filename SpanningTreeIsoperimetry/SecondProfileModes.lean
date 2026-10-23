module

public import SpanningTreeIsoperimetry.RectangularSecondProfile
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! Actual exponential mode derivatives for the genuine second profile. -/
namespace SpanningTreeIsoperimetry.SecondProfileModes

open Polynomial CoupledRectangleError RectangularSecondProfile
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def profilePolynomial (u : ℝ) : ℝ := u*(1+u)^2
def profilePolynomialDeriv (u : ℝ) : ℝ := 1+4*u+3*u^2
def profilePolynomialSecond (u : ℝ) : ℝ := 4+6*u

def modeCoefficient (b : ℝ) : ℕ → ℝ[X]
  | 0 => X*(1+X)^2
  | n+1 => (modeCoefficient b n).derivative-C b*modeCoefficient b n

def frequency (n : ℕ) : ℝ := 2*Real.pi*((n : ℝ)+1)
def weight (n : ℕ) : ℝ := (ArithmeticFunction.sigma 3 (n+1) : ℝ)
def weightedMode (n k : ℕ) (u : ℝ) : ℝ :=
  weight n*(modeCoefficient (frequency n) k).eval u*Real.exp (-frequency n*u)

theorem frequency_ge_six (n : ℕ) : 6≤frequency n := by
  dsimp [frequency]
  nlinarith [Real.pi_gt_d2,mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n)]

theorem exp_frequency_eq (n : ℕ) (u : ℝ) :
    Real.exp (-frequency n*u)=Real.exp (-2*Real.pi*u)^(n+1) := by
  rw [← Real.exp_nat_mul]
  congr 1
  unfold frequency
  push_cast
  ring

theorem weight_nonneg (n : ℕ) : 0≤weight n := Nat.cast_nonneg _

theorem weight_le_fourth (n : ℕ) : weight n≤((n : ℝ)+1)^4 := by
  have h := ArithmeticFunction.sigma_le_pow_succ 3 (n+1)
  unfold weight
  exact_mod_cast h

theorem weight_one : weight 1=9 := by
  norm_num [weight,ArithmeticFunction.sigma_apply,Nat.prime_two.divisors]

theorem coefficient_zero (b u : ℝ) : (modeCoefficient b 0).eval u=profilePolynomial u := by
  simp [modeCoefficient,profilePolynomial]

theorem coefficient_one (b u : ℝ) :
    (modeCoefficient b 1).eval u=profilePolynomialDeriv u-b*profilePolynomial u := by
  norm_num [modeCoefficient,profilePolynomial,profilePolynomialDeriv,Polynomial.derivative_mul,
    Polynomial.derivative_add,Polynomial.derivative_pow]
  ring

theorem coefficient_two (b u : ℝ) :
    (modeCoefficient b 2).eval u=secondModePolynomial b u := by
  norm_num [modeCoefficient,secondModePolynomial,Polynomial.derivative_mul,
    Polynomial.derivative_add,Polynomial.derivative_sub,Polynomial.derivative_pow]
  ring

theorem secondModePolynomial_identity (b u : ℝ) :
    secondModePolynomial b u=profilePolynomialSecond u-2*b*profilePolynomialDeriv u+
      b^2*profilePolynomial u := by
  unfold secondModePolynomial profilePolynomialSecond profilePolynomialDeriv profilePolynomial
  ring

theorem coefficient_four (b u : ℝ) :
    (modeCoefficient b 4).eval u=fourthModePolynomial b u := by
  norm_num [modeCoefficient,fourthModePolynomial,Polynomial.derivative_mul,
    Polynomial.derivative_add,Polynomial.derivative_sub,Polynomial.derivative_pow]
  ring

theorem hasDerivAt_weightedMode (n k : ℕ) (u : ℝ) :
    HasDerivAt (weightedMode n k) (weightedMode n (k+1) u) u := by
  have hp := ((modeCoefficient (frequency n) k).hasDerivAt u).const_mul (weight n)
  have he := ((hasDerivAt_id u).const_mul (-frequency n)).exp
  have h := hp.fun_mul he
  unfold weightedMode
  convert h using 1 <;> (try rfl) <;>
    simp only [modeCoefficient,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,id_eq,mul_one] <;> ring

theorem continuous_weightedMode (n k : ℕ) : Continuous (weightedMode n k) := by
  rw [continuous_iff_continuousAt]
  exact fun u => (hasDerivAt_weightedMode n k u).continuousAt

theorem weightedMode_two_nonneg (n : ℕ) {u : ℝ} (hu : 1≤u) : 0≤weightedMode n 2 u := by
  rw [weightedMode,coefficient_two]
  have hp := secondModePolynomial_pos (frequency_ge_six n) hu
  have hw := weight_nonneg n
  positivity

theorem weightedMode_four_nonneg (n : ℕ) {u : ℝ} (hu : 1≤u) : 0≤weightedMode n 4 u := by
  rw [weightedMode,coefficient_four]
  have hp := fourthModePolynomial_pos (frequency_ge_six n) hu
  have hw := weight_nonneg n
  positivity

/-- Every actual second-derivative exponential mode is convex on u>=1. -/
theorem weightedMode_two_convex (n : ℕ) : ConvexOn ℝ (Set.Ici 1) (weightedMode n 2) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := weightedMode n 3) (f'' := weightedMode n 4)
    (convex_Ici 1)
  · exact (continuous_weightedMode n 2).continuousOn
  · exact fun u _ => (hasDerivAt_weightedMode n 2 u).hasDerivWithinAt
  · exact fun u _ => (hasDerivAt_weightedMode n 3 u).hasDerivWithinAt
  · intro u hu
    have hu' : 1<u := by simpa only [interior_Ici,Set.mem_Ioi] using hu
    exact weightedMode_four_nonneg n hu'.le

/-- The sharper endpoint bound uses only the exact sigma3(2)=9 value beyond
the standard sigma3(n)<=n^4 estimate. -/
theorem curvature_single_coefficient_one_lt :
    (22/7 : ℝ)^3/1440*(10+240*(160*moment6 (1/530)-100*moment5 (1/530)+
      10*moment4 (1/530)-3150*(1/530)^2))<1 := by
  norm_num [moment4,moment5,moment6]

theorem curvature_single_coefficient_three_lt :
    (22/7 : ℝ)^3/1440*(22+240*(1920*moment6 ((1/530)^3)+22*moment4 ((1/530)^3)))<1/2 := by
  norm_num [moment4,moment6]

end
end SpanningTreeIsoperimetry.SecondProfileModes
