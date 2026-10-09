import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Elementary real ODE uniqueness for the normalized determinant path.
No holomorphic determinant theorem is used. -/
namespace SpanningTreeIsoperimetry.ScalarDeterminantODE
noncomputable section

theorem affine_of_constant_derivative (f : ℝ → ℝ) (b : ℝ)
    (hf : ∀ t,HasDerivAt f b t) (t : ℝ) : f t=f 0+b*t := by
  let g : ℝ → ℝ := fun x => f x-b*x
  have hd (x : ℝ) : HasDerivAt g 0 x := by
    have h := (hf x).sub ((hasDerivAt_id x).const_mul b)
    change HasDerivAt g _ x at h
    convert h using 1 <;> (try simp only [id_eq]) <;> ring
  have h := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt)
    (fun x => (hd x).deriv) t 0
  dsimp only [g] at h
  linarith

def exponent (a b t : ℝ) : ℝ := a*t+(b/2)*t^2

theorem exponent_derivative (a b t : ℝ) : HasDerivAt (exponent a b) (a+b*t) t := by
  have h := ((hasDerivAt_id t).const_mul a).add (((hasDerivAt_id t).pow 2).const_mul (b/2))
  change HasDerivAt (exponent a b) _ t at h
  convert h using 1 <;> (try simp only [id_eq]) <;> ring


theorem quadratic_of_affine_derivative (f : ℝ → ℝ) (a b : ℝ)
    (hf : ∀ t,HasDerivAt f (a+b*t) t) (t : ℝ) :
    f t=f 0+exponent a b t := by
  let g : ℝ → ℝ := fun x => f x-exponent a b x
  have hd (x : ℝ) : HasDerivAt g 0 x := by
    have h := (hf x).sub (exponent_derivative a b x)
    change HasDerivAt g _ x at h
    simpa using h
  have h := affine_of_constant_derivative g 0 hd t
  dsimp only [g] at h
  have hz : exponent a b 0=0 := by simp [exponent]
  rw [hz] at h
  linarith

theorem quadratic_exponential (f : ℝ → ℝ) (a b : ℝ) (hf0 : f 0=1)
    (hf : ∀ t,HasDerivAt f ((a+b*t)*f t) t) (t : ℝ) :
    f t=Real.exp (exponent a b t) := by
  let g : ℝ → ℝ := fun x => f x*Real.exp (-exponent a b x)
  have hd (x : ℝ) : HasDerivAt g 0 x := by
    have h := (hf x).mul ((exponent_derivative a b x).neg.exp)
    change HasDerivAt g _ x at h
    convert h using 1 <;> (try simp only [id_eq]) <;> ring
  have hconst := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt)
    (fun x => (hd x).deriv) t 0
  have hc : f t*Real.exp (-exponent a b t)=1 := by
    simpa only [g,exponent,mul_zero,zero_pow (by norm_num : (2 : ℕ)≠0),add_zero,
      neg_zero,Real.exp_zero,hf0,mul_one] using hconst
  have he := congrArg (fun y : ℝ => y*Real.exp (exponent a b t)) hc
  have hi : Real.exp (-exponent a b t)*Real.exp (exponent a b t)=1 := by
    rw [← Real.exp_add]
    simp
  rw [mul_assoc,hi,mul_one,one_mul] at he
  exact he

end
end SpanningTreeIsoperimetry.ScalarDeterminantODE
