import SpanningTreeIsoperimetry.RectangleTaylorRemainder
import SpanningTreeIsoperimetry.RectangleTailRemainder

/-! The actual fourth-order rectangle expansion with complete local errors. -/
namespace SpanningTreeIsoperimetry.FourthOrderRectangleError

open SquareMaximality SquareMaximality.Rectangle
open RectangularRemainder RectangularSecondProfile RectangleResidualBounds
open SharpRectangleExpansion RectangleTaylorRemainder RectangleTailRemainder RectangleModeSums
open TrapezoidalKernelError CoupledRectangleError
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def epsilonConstant : ℝ := 3*(22/7)^5/6048

def retainedConstant (D1 D2 : ℝ) : ℝ :=
  ((22/7)^5)*moment5 (1/500)/(48*(1-1/500))+(22/7)^6/72*(lowSixth D1 D2+highSixth)

private theorem coefficient_identity (D1 D2 t : ℝ) :
    epsilonConstant+retainedConstant D1 D2+t=fourthOrderCoefficient D1 D2 t := by
  let A : ℝ := 3*(22/7)^5/6048
  let B : ℝ := ((22/7)^5)*moment5 (1/500)/(48*(1-1/500))
  let C : ℝ := (22/7)^6/72*(lowSixth D1 D2+highSixth)
  change A+(B+C)+t=A+B+C+t
  ring

private theorem epsilon_next_scaled {r s : ℕ} (hr : 0<r) (hsr : s≤3*r) :
    |-(s : ℝ)*(Concrete.epsilon squareLatticeEntropy r-Real.pi/(12*r)-Real.pi^3/(1440*(r : ℝ)^3))|≤
      epsilonConstant/(r : ℝ)^4 := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hsR : (s : ℝ)≤3*r := by exact_mod_cast hsr
  have hp : Real.pi≤(22 : ℝ)/7 := by linarith [Real.pi_lt_d4]
  rw [abs_mul,abs_neg,abs_of_nonneg (Nat.cast_nonneg s)]
  calc
    _≤(s : ℝ)*(Real.pi^5/(6048*(r : ℝ)^5)) :=
      mul_le_mul_of_nonneg_left (epsilon_next_error hr) (Nat.cast_nonneg s)
    _≤(3*(r : ℝ))*((22/7)^5/(6048*(r : ℝ)^5)) := by gcongr
    _=epsilonConstant/(r : ℝ)^4 := by unfold epsilonConstant; field_simp [hrR.ne'] <;> ring

private theorem sharpError_le_components {r s : ℕ} (hr : 0<r) (hrs : r≤s) :
    |sharpError r s|≤
      |-(s : ℝ)*(Concrete.epsilon squareLatticeEntropy r-Real.pi/(12*r)-Real.pi^3/(1440*(r : ℝ)^3))|+
      |retainedCorrection r s|+tailError r s := by
  have hs : 0<s := hr.trans_le hrs
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hsR : (0 : ℝ)<s := by exact_mod_cast hs
  have hB := omittedBose_nonneg (div_pos hsR hrR) hr
  let a : ℝ := -(s : ℝ)*(Concrete.epsilon squareLatticeEntropy r-Real.pi/(12*r)-Real.pi^3/(1440*(r : ℝ)^3))
  let b := retainedCorrection r s
  let c := logTail (Real.exp (-2*Real.pi*((s : ℝ)/r))) r
  let d := (Real.pi^3*s/(6*(r : ℝ)^3))*omittedBose ((s : ℝ)/r) r
  let e := (1/2 : ℝ)*Real.log (1-Real.exp (-4*r*Concrete.alpha))
  have hd : 0≤d := by dsimp [d]; positivity
  rw [sharpError_exact hr hs]
  change |a+b-c+d-e|≤|a|+|b|+(|c|+d+|e|)
  have h1 := abs_add_le a b
  have h2 := abs_sub_le (a+b) (0 : ℝ) c
  have h3 := abs_add_le (a+b-c) d
  have h4 := abs_sub_le (a+b-c+d) (0 : ℝ) e
  simp only [sub_zero,zero_sub,abs_neg] at h2 h4
  rw [abs_of_nonneg hd] at h3
  linarith

private theorem sharpError_lt_of_bounds {r s : ℕ} (hr : 0<r) (hrs : r≤s) (hsr : s≤3*r)
    {D1 D2 t : ℝ} (hret : |retainedCorrection r s|≤retainedConstant D1 D2/(r : ℝ)^4)
    (htail : tailError r s<t/(r : ℝ)^4) :
    |sharpError r s|<fourthOrderCoefficient D1 D2 t/(r : ℝ)^4 := by
  have hε := epsilon_next_scaled hr hsr
  have hsum := add_lt_add_of_le_of_lt (add_le_add hε hret) htail
  calc
    _<epsilonConstant/(r : ℝ)^4+retainedConstant D1 D2/(r : ℝ)^4+t/(r : ℝ)^4 :=
      (sharpError_le_components hr hrs).trans_lt hsum
    _=(epsilonConstant+retainedConstant D1 D2+t)/(r : ℝ)^4 := by ring
    _=_ := by rw [coefficient_identity]

/-- The actual next rectangle term, with a strict fourth-order error. -/
theorem sharpError_four {r s : ℕ} (hr : 4≤r) (hrs : r≤s) (hsr : s≤3*r) :
    |sharpError r s|<1/(4*(r : ℝ)^4) := by
  have hr0 : 0<r := by omega
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr0
  have hret : |retainedCorrection r s|≤retainedConstant 396 37600/(r : ℝ)^4 :=
    retainedCorrection_four hr hrs
  have h := sharpError_lt_of_bounds hr0 hrs hsr hret (tailError_four_lt hr hrs)
  calc
    _<fourthOrderCoefficient 396 37600 (1/1000)/(r : ℝ)^4 := h
    _<(1/4 : ℝ)/(r : ℝ)^4 := div_lt_div_of_pos_right fourthOrderCoefficient_four_lt (pow_pos hrR 4)
    _=1/(4*(r : ℝ)^4) := by field_simp [hrR.ne'] <;> ring

/-- The width-three endpoint needed by the full coupled-error lemma. -/
theorem sharpError_three {r s : ℕ} (hr : 3≤r) (hrs : r≤s) (hsr : s≤3*r) :
    |sharpError r s|<1/(3*(r : ℝ)^4) := by
  have hr0 : 0<r := by omega
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr0
  have hret : |retainedCorrection r s|≤retainedConstant 321 12000/(r : ℝ)^4 :=
    retainedCorrection_three hr hrs
  have h := sharpError_lt_of_bounds hr0 hrs hsr hret (tailError_three_lt hr hrs)
  calc
    _<fourthOrderCoefficient 321 12000 (1/500)/(r : ℝ)^4 := h
    _<(1/3 : ℝ)/(r : ℝ)^4 := div_lt_div_of_pos_right fourthOrderCoefficient_three_lt (pow_pos hrR 4)
    _=1/(3*(r : ℝ)^4) := by field_simp [hrR.ne'] <;> ring

end
end SpanningTreeIsoperimetry.FourthOrderRectangleError
