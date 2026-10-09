import SpanningTreeIsoperimetry.RectangleEnergyBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Exact inverse quadratic forms and strict polynomial bounds for the
two-cell strip and square quadrant minors. -/
namespace SpanningTreeIsoperimetry.ShortDefectPolynomials
open Matrix
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def a (t : ℝ) : ℝ := 2-16*t/3
def b (t : ℝ) : ℝ := 7/2-32*t/3
def c (t : ℝ) : ℝ := -4+64*t/5
def d (t : ℝ) : ℝ := 40-4352*t/35
def p (t : ℝ) : ℝ := a t*(4*b t-c t)-(b t)^2
def e (t : ℝ) : ℝ := 2*b t-c t
def D (t : ℝ) : ℝ := b t*d t-2*(c t)^2
def t0 : ℝ := 1/Real.pi

def twoMatrix (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a t,b t; b t,4*b t-c t]
def fourMatrix (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![a t,b t,b t,c t;
     b t,4*b t-c t,c t,2*c t;
     b t,c t,4*b t-c t,2*c t;
     c t,2*c t,2*c t,d t]
def twoVector (x : ℝ) : Fin 2 → ℝ := ![1,2-2*x]
def fourVector (x : ℝ) : Fin 4 → ℝ := ![1,2+2*x,2-2*x,4-4*x^2]

theorem twoMatrix_det (t : ℝ) : (twoMatrix t).det=p t := by
  simp [twoMatrix,Matrix.det_fin_two,p,pow_two]

theorem fourMatrix_eq (t : ℝ) : fourMatrix t=SmallGreenPolynomials.squareMatrix t := by
  rw [SmallGreenPolynomials.squareMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fourMatrix,SmallGreenPolynomials.squareLiteral,a,b,c,d] <;> ring

private def lower : ℝ := 100000000000000000000/314159265358979323847
private def upper : ℝ := 100000000000000000000/314159265358979323846

private theorem reciprocal_bounds : lower≤t0 ∧ t0≤upper := by
  constructor
  · have h := div_lt_div_of_pos_left (by norm_num : (0 : ℝ)<1) Real.pi_pos Real.pi_lt_d20
    norm_num [lower,t0] at h ⊢
    exact h.le
  · have h := div_lt_div_of_pos_left (by norm_num : (0 : ℝ)<1)
      (by norm_num : (0 : ℝ)<3.14159265358979323846) Real.pi_gt_d20
    norm_num [upper,t0] at h ⊢
    exact h.le

set_option maxHeartbeats 2000000 in
theorem coefficient_bounds :
    0<b t0 ∧ 0<e t0 ∧ 0<D t0 ∧ 4/43<p t0 ∧
    0<4*a t0-c t0-(73/6)*p t0 ∧ 0<4*a t0-12*p t0 ∧
    0<2*D t0+4*(e t0)^2-40*b t0*D t0 ∧
    0<4*D t0-16*(e t0)^2+36*e t0*D t0 := by
  obtain ⟨hl,hu⟩ := reciprocal_bounds
  have h0 : 0≤lower := by norm_num [lower]
  have ht : 0≤t0 := by unfold t0; positivity
  have hl2 : lower^2≤t0^2 := by gcongr
  have hu2 : t0^2≤upper^2 := by gcongr
  have hl3 : lower^3≤t0^3 := by gcongr
  have hu3 : t0^3≤upper^3 := by gcongr
  norm_num [lower,upper] at hl hu hl2 hu2 hl3 hu3
  simp only [t0,one_div,inv_pow] at hl hu hl2 hu2 hl3 hu3
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    dsimp only [p,D,e,a,b,c,d,t0] <;> simp only [one_div] <;>
      nlinarith only [hl,hu,hl2,hu2,hl3,hu3]

theorem p_pos : 0<p t0 := lt_trans (by norm_num : (0 : ℝ)<4/43) coefficient_bounds.2.2.2.1

theorem fourMatrix_det_pos : 0<(fourMatrix t0).det := by
  rw [fourMatrix_eq,SmallGreenPolynomials.squareMatrix_det]
  exact RectangleEnergyBounds.squareDet_pos

theorem inverse_mulVec_of_solution {n : Type*} [Fintype n] [DecidableEq n]
    {Q : Matrix n n ℝ} (hQ : Q.det≠0) {v w : n → ℝ} (hw : Q*ᵥw=v) : Q⁻¹*ᵥv=w := by
  rw [← hw,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hQ),Matrix.one_mulVec]

def twoSolution (t x : ℝ) : Fin 2 → ℝ :=
  ![((4*b t-c t)-b t*(2-2*x))/p t, (-b t+a t*(2-2*x))/p t]

theorem twoSolution_eq (x : ℝ) : twoMatrix t0*ᵥtwoSolution t0 x=twoVector x := by
  have hp := p_pos.ne'
  ext i
  fin_cases i <;>
    simp [twoMatrix,twoSolution,twoVector,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;>
    field_simp [hp] <;> unfold p <;> ring

theorem two_inverse_form (x : ℝ) :
    twoVector x ⬝ᵥ ((twoMatrix t0)⁻¹*ᵥtwoVector x)=
      (4*a t0-c t0-2*x+4*a t0*x^2)/p t0 := by
  have hdet : (twoMatrix t0).det≠0 := by rw [twoMatrix_det]; exact p_pos.ne'
  rw [inverse_mulVec_of_solution hdet (twoSolution_eq x)]
  simp [twoVector,twoSolution,dotProduct,Fin.sum_univ_succ]
  have hb : b t0=2*a t0-1/2 := by unfold a b; ring
  field_simp [p_pos.ne']
  rw [hb]
  ring

def fourSolution (t x : ℝ) : Fin 4 → ℝ :=
  ![0,(d t-4*c t+4*c t*x^2)/(2*D t)+x/e t,
      (d t-4*c t+4*c t*x^2)/(2*D t)-x/e t,
      2*(e t-2*b t*x^2)/D t]

theorem fourSolution_eq (x : ℝ) : fourMatrix t0*ᵥfourSolution t0 x=fourVector x := by
  have he := coefficient_bounds.2.1.ne'
  have hD := coefficient_bounds.2.2.1.ne'
  ext i
  fin_cases i <;>
    simp [fourMatrix,fourSolution,fourVector,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;>
    field_simp [he,hD] <;> unfold e D <;> ring

theorem four_inverse_form (x : ℝ) :
    fourVector x ⬝ᵥ ((fourMatrix t0)⁻¹*ᵥfourVector x)=
      2/b t0+4*x^2/e t0+4*(e t0-2*b t0*x^2)^2/(b t0*D t0) := by
  rw [inverse_mulVec_of_solution fourMatrix_det_pos.ne' (fourSolution_eq x)]
  simp [fourVector,fourSolution,dotProduct,Fin.sum_univ_succ]
  field_simp [coefficient_bounds.1.ne',coefficient_bounds.2.1.ne',coefficient_bounds.2.2.1.ne']
  unfold e D
  ring

theorem two_polynomial_lower {x : ℝ} (hx : 0≤x) :
    (73/6 : ℝ)-(43/2)*x+12*x^2 < (4*a t0-c t0-2*x+4*a t0*x^2)/p t0 := by
  have hp := p_pos
  have hp4 := coefficient_bounds.2.2.2.1
  have hc := coefficient_bounds.2.2.2.2.1
  have hq := coefficient_bounds.2.2.2.2.2.1
  apply (lt_div_iff₀ hp).mpr
  have hl : 0≤((43/2)*p t0-2)*x := mul_nonneg (by nlinarith) hx
  have hh : 0≤(4*a t0-12*p t0)*x^2 := mul_nonneg hq.le (sq_nonneg x)
  nlinarith only [hc,hl,hh]

theorem four_polynomial_lower (x : ℝ) :
    (40 : ℝ)-36*x^2 < 2/b t0+4*x^2/e t0+4*(e t0-2*b t0*x^2)^2/(b t0*D t0) := by
  have hb := coefficient_bounds.1
  have he := coefficient_bounds.2.1
  have hD := coefficient_bounds.2.2.1
  have hc := coefficient_bounds.2.2.2.2.2.2.1
  have hq := coefficient_bounds.2.2.2.2.2.2.2
  have hconstant : 0<(2*D t0+4*(e t0)^2-40*b t0*D t0)/(b t0*D t0) :=
    div_pos hc (mul_pos hb hD)
  have hquadratic : 0≤((4*D t0-16*(e t0)^2+36*e t0*D t0)/(e t0*D t0))*x^2 :=
    mul_nonneg (div_pos hq (mul_pos he hD)).le (sq_nonneg x)
  have hquartic : 0≤(16*b t0/D t0)*x^4 := by positivity
  have hid : (2/b t0+4*x^2/e t0+4*(e t0-2*b t0*x^2)^2/(b t0*D t0))-(40-36*x^2)=
      (2*D t0+4*(e t0)^2-40*b t0*D t0)/(b t0*D t0)+
      ((4*D t0-16*(e t0)^2+36*e t0*D t0)/(e t0*D t0))*x^2+(16*b t0/D t0)*x^4 := by
    field_simp [hb.ne',he.ne',hD.ne']
    ring
  linarith

theorem two_quadratic_lower {x : ℝ} (hx : 0≤x) :
    (73/6 : ℝ)-(43/2)*x+12*x^2 < twoVector x ⬝ᵥ ((twoMatrix t0)⁻¹*ᵥtwoVector x) := by
  rw [two_inverse_form]
  exact two_polynomial_lower hx

theorem square_quadratic_lower (x : ℝ) :
    (40 : ℝ)-36*x^2 < fourVector x ⬝ᵥ ((SmallGreenPolynomials.squareMatrix t0)⁻¹*ᵥfourVector x) := by
  rw [← fourMatrix_eq,four_inverse_form]
  exact four_polynomial_lower x

end
end SpanningTreeIsoperimetry.ShortDefectPolynomials
