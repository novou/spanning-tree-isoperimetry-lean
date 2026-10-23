module

public import SpanningTreeIsoperimetry.RectangleResidualBounds
public import SpanningTreeIsoperimetry.TrapezoidalKernelError

@[expose] public section

set_option backward.privateInPublic true

/-! Uniform quadratic control of the actual rectangle profile error. -/
namespace SpanningTreeIsoperimetry.UniformRectangleError

open SquareMaximality SquareMaximality.Rectangle
open RectangularRemainder RectangleResidualBounds TrapezoidalKernelError CoupledRectangleError
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def retainedCoefficient : ℝ :=
  ((22/7)^3/6)*((1+4*(1/32)+(1/32)^2)/(32*(1-1/32)^3))

def tailCoefficient : ℝ := 500/499^2

private theorem pi_le_twenty_two_sevenths : Real.pi≤(22 : ℝ)/7 := by linarith [Real.pi_lt_d4]

private theorem q_lt_thirtysecond : Concrete.q<(1 : ℝ)/32 := by
  have hq := Concrete.q_pos
  have hq1 := Concrete.q_lt_one
  have hfrac := Concrete.q_fraction
  have hden : 0<(1-Concrete.q)^2 := sq_pos_of_pos (by linarith)
  have hEq := (div_eq_iff hden.ne').mp hfrac
  nlinarith

private theorem linear_q_le {u : ℝ} (hu : 1≤u) : Real.exp (-2*Real.pi*u)≤(1 : ℝ)/500 := by
  have he : (500 : ℝ)≤Real.exp (2*Real.pi*u) := by
    have hp := exp_two_pi_gt_fivehundredthirty
    have hm : Real.exp (2*Real.pi)≤Real.exp (2*Real.pi*u) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    linarith
  rw [show -2*Real.pi*u= -(2*Real.pi*u) by ring,Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<500) he

private theorem retained_coefficient_bound {r : ℕ} (hr : 0<r) :
    (Real.pi^3/(6*(r : ℝ)^2))*
      ((1+4*Concrete.q+Concrete.q^2)/(32*(1-Concrete.q)^3))≤retainedCoefficient/(r : ℝ)^2 := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hq0 := Concrete.q_pos
  have hq1 := Concrete.q_lt_one
  have hq := q_lt_thirtysecond.le
  have hb : (1+4*Concrete.q+Concrete.q^2)/(32*(1-Concrete.q)^3)≤
      (1+4*(1/32 : ℝ)+(1/32)^2)/(32*(1-1/32)^3) := by gcongr
  have hp := pi_le_twenty_two_sevenths
  calc
    _≤((22/7 : ℝ)^3/(6*(r : ℝ)^2))*
        ((1+4*(1/32)+(1/32)^2)/(32*(1-1/32)^3)) := by gcongr
    _=retainedCoefficient/(r : ℝ)^2 := by
      unfold retainedCoefficient
      field_simp <;> ring

/-- Actual finite residual versus its convergent linear profile. -/
theorem residual_uniform {r s : ℕ} (hr : 0<r) (hrs : r≤s) :
    |RectangularComparison.realResidual r s-linearResidual ((s : ℝ)/r)|≤
      (retainedCoefficient+tailCoefficient)/(r : ℝ)^2 := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hsR : (r : ℝ)≤s := by exact_mod_cast hrs
  have hu : 1≤(s : ℝ)/r := (one_le_div hrR).mpr hsR
  have hu0 : 0<(s : ℝ)/r := by linarith
  let q := Real.exp (-2*Real.pi*((s : ℝ)/r))
  have hq0 : 0<q := Real.exp_pos _
  have hq : q≤1/500 := linear_q_le hu
  have ht := logTail_quadratic_bound hq0 (show q≤1/4 by linarith) hr
  have ht' : |logTail q r|≤tailCoefficient/(r : ℝ)^2 := by
    have hrat : q/(1-q)^2≤tailCoefficient := by
      unfold tailCoefficient
      calc
        q/(1-q)^2≤(1/500 : ℝ)/(1-1/500)^2 := by gcongr
        _=500/499^2 := by norm_num
    calc
      _≤q/((1-q)^2*(r : ℝ)^2) := ht
      _=(q/(1-q)^2)/(r : ℝ)^2 := by field_simp <;> ring
      _≤_ := div_le_div_of_nonneg_right hrat (sq_nonneg _)
  have hret := (retained_residual_bound hr hrs).trans (retained_coefficient_bound hr)
  rw [linearResidual_decomposition hu0 hr,sub_add_eq_sub_sub]
  have htriangle := abs_sub_le
    (RectangularComparison.realResidual r s-
      ∑ j∈Finset.Ico 1 r, Real.log (1-Real.exp (-2*Real.pi*((s : ℝ)/r)*j))) (0 : ℝ) (logTail q r)
  simp only [sub_zero,zero_sub,abs_neg] at htriangle
  exact htriangle.trans (by simpa only [add_div] using add_le_add hret ht')

private theorem endpoint_uniform {r : ℕ} (hr : 0<r) :
    |(1/2 : ℝ)*Real.log (1-Real.exp (-4*r*Concrete.alpha))|≤(1/64)/(r : ℝ)^2 := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hq0 := Concrete.q_pos
  have hq1 := Concrete.q_lt_one
  have hpow1 : Concrete.q^r<1 := pow_lt_one₀ hq0.le hq1 (by omega)
  have hpow : Concrete.q^r≤Concrete.q := pow_le_of_le_one hq0.le hq1.le (by omega)
  have he : Real.exp (-4*r*Concrete.alpha)=Concrete.q^r := by
    rw [Concrete.q,← Real.exp_nat_mul]
    congr 1
    ring
  rw [he,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
  have hlog : Real.log (1-Concrete.q^r)≤0 :=
    Real.log_nonpos (sub_pos.mpr hpow1).le (by have := pow_nonneg hq0.le r; linarith)
  rw [abs_of_nonpos hlog]
  have hdecay := quadratic_geometric_decay hq0.le (show Concrete.q≤1/4 by linarith [q_lt_thirtysecond])
    (show 1≤r by omega)
  have hp : Concrete.q^r≤Concrete.q/(r : ℝ)^2 :=
    (le_div_iff₀ (sq_pos_of_pos hrR)).mpr (by simpa only [mul_comm] using hdecay)
  have hratio : Concrete.q/(1-Concrete.q)≤1/32 := by
    calc
      _=(Concrete.q/(1-Concrete.q)^2)*(1-Concrete.q) := by
        field_simp [(sub_pos.mpr hq1).ne'] <;> ring
      _=(1/32)*(1-Concrete.q) := by rw [Concrete.q_fraction]
      _≤1/32 := by linarith
  have hh : -Real.log (1-Concrete.q^r)≤(1/32)/(r : ℝ)^2 := by
    calc
      _≤Concrete.q^r/(1-Concrete.q^r) := Concrete.Inputs.neg_log_one_sub_le (pow_nonneg hq0.le _) hpow1
      _≤Concrete.q^r/(1-Concrete.q) := div_le_div_of_nonneg_left (pow_nonneg hq0.le _) (by linarith) (by linarith)
      _≤(Concrete.q/(r : ℝ)^2)/(1-Concrete.q) := div_le_div_of_nonneg_right hp (by linarith)
      _=(Concrete.q/(1-Concrete.q))/(r : ℝ)^2 := by field_simp <;> ring
      _≤_ := div_le_div_of_nonneg_right hratio (sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ)≤1/2)
  convert hm using 1 <;> field_simp <;> ring

private theorem epsilon_uniform {r s : ℕ} (hr : 0<r) (hsr : s≤3*r) :
    |-(s : ℝ)*(Concrete.epsilon squareLatticeEntropy r-Real.pi/(12*r))|≤
      ((22/7 : ℝ)^3/120)/(r : ℝ)^2 := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hsrR : (s : ℝ)≤3*r := by exact_mod_cast hsr
  rw [abs_mul,abs_neg,abs_of_nonneg (Nat.cast_nonneg s)]
  calc
    _≤(s : ℝ)*(Real.pi^3/(360*(r : ℝ)^3)) :=
      mul_le_mul_of_nonneg_left (epsilon_first_error hr) (Nat.cast_nonneg s)
    _≤(3*(r : ℝ))*(((22/7 : ℝ)^3)/(360*(r : ℝ)^3)) := by gcongr; exact pi_le_twenty_two_sevenths
    _=((22/7 : ℝ)^3/120)/(r : ℝ)^2 := by field_simp <;> ring

/-- Uniform actual rectangle remainder for ordered aspect at most three. -/
theorem error_uniform {r s : ℕ} (hr : 0<r) (hrs : r≤s) (hsr : s≤3*r) :
    |error r s|≤1/(2*(r : ℝ)^2) := by
  have hs : 0<s := hr.trans_le hrs
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hε := epsilon_uniform hr hsr
  have hres := residual_uniform hr hrs
  have hend := endpoint_uniform hr
  have hc : ((22/7 : ℝ)^3/120)+retainedCoefficient+tailCoefficient+1/64≤1/2 := by
    norm_num [retainedCoefficient,tailCoefficient]
  rw [error_exact hr hs]
  have h1 := abs_add_le
    (-(s : ℝ)*(Concrete.epsilon squareLatticeEntropy r-Real.pi/(12*r)))
    (RectangularComparison.realResidual r s-linearResidual ((s : ℝ)/r))
  have h2 := abs_sub_le
    (-(s : ℝ)*(Concrete.epsilon squareLatticeEntropy r-Real.pi/(12*r))+
      (RectangularComparison.realResidual r s-linearResidual ((s : ℝ)/r))) (0 : ℝ)
    ((1/2)*Real.log (1-Real.exp (-4*r*Concrete.alpha)))
  simp only [sub_zero,zero_sub,abs_neg] at h2
  have hcoeff := div_le_div_of_nonneg_right hc (sq_nonneg (r : ℝ))
  have he : (1/2 : ℝ)/(r : ℝ)^2=1/(2*(r : ℝ)^2) := by field_simp <;> ring
  rw [he] at hcoeff
  simp only [add_div] at hcoeff hres
  linarith

end
end SpanningTreeIsoperimetry.UniformRectangleError
