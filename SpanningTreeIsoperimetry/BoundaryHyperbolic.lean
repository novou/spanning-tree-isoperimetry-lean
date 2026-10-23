module

public import SpanningTreeIsoperimetry.SmallCases
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section

/-! Hyperbolic evaluation of the actual path continuants, and the one-boundary
resolvent loss before finite-y separation. -/
namespace SpanningTreeIsoperimetry.BoundaryHyperbolic
open SmallCases Filter
open scoped Topology
noncomputable section

theorem sinh_neighbors (t x : ℝ) :
    Real.sinh (t*(x+1))+Real.sinh (t*(x-1))=2*Real.cosh t*Real.sinh (t*x) := by
  rw [mul_add,mul_sub,mul_one,Real.sinh_add,Real.sinh_sub]
  ring

theorem continuant_cosh_mul_sinh (t : ℝ) (n : ℕ) :
    continuant (2*Real.cosh t) n*Real.sinh t=Real.sinh (((n : ℝ)+1)*t) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp only [continuant_one,Nat.cast_one,one_add_one_eq_two,Real.sinh_two_mul]; ring
  | more n ih ih1 =>
    rw [continuant_recurrence,sub_mul,mul_assoc,ih,ih1]
    have h := sinh_neighbors t ((n : ℝ)+2)
    have ha : t*((n : ℝ)+2+1)=((n : ℝ)+3)*t := by ring
    have hb : t*((n : ℝ)+2-1)=((n : ℝ)+1)*t := by ring
    have hc : t*((n : ℝ)+2)=((n : ℝ)+2)*t := by ring
    rw [ha,hb,hc] at h
    push_cast
    convert (eq_sub_of_add_eq h).symm using 1 <;> congr 1 <;> ring

theorem continuant_cosh (t : ℝ) (ht : 0<t) (n : ℕ) :
    continuant (2*Real.cosh t) n=Real.sinh (((n : ℝ)+1)*t)/Real.sinh t := by
  exact (eq_div_iff (Real.sinh_pos_iff.mpr ht).ne').mpr (continuant_cosh_mul_sinh t n)

theorem endpoint_ratio (t : ℝ) (ht : 0<t) (n : ℕ) :
    continuant (2*Real.cosh t) n/continuant (2*Real.cosh t) (n+1)=
      Real.sinh (((n : ℝ)+1)*t)/Real.sinh (((n : ℝ)+2)*t) := by
  rw [continuant_cosh t ht,continuant_cosh t ht]
  push_cast
  have he : ((n : ℝ)+1)+1=(n : ℝ)+2 := by ring
  rw [he,div_div_div_cancel_right₀ (Real.sinh_pos_iff.mpr ht).ne']

theorem exp_neg_div_sinh (x : ℝ) (hx : 0<x) :
    Real.exp (-x)/Real.sinh x=2/(Real.exp (2*x)-1) := by
  have hp := Real.exp_pos x
  have he : Real.exp (2*x)=Real.exp x^2 := by rw [two_mul,Real.exp_add,pow_two]
  rw [he,Real.sinh_eq,Real.exp_neg]
  have hex : 1<Real.exp x := by simpa using Real.exp_lt_exp.mpr hx
  have hpow : Real.exp x^2-1≠0 := by nlinarith
  have hs : Real.exp x-(Real.exp x)⁻¹≠0 := by
    apply sub_ne_zero.mpr
    intro heq
    have he := congrArg (fun y : ℝ => y*Real.exp x) heq
    rw [inv_mul_cancel₀ hp.ne'] at he
    nlinarith
  field_simp
  <;> ring

/-- Exact loss from a half-line endpoint resolvent upon adding its far
Dirichlet boundary. This is the scalar factor in the Green-loss integral. -/
theorem endpoint_loss (r t : ℝ) (hr : 0<r) (ht : 0<t) :
    Real.exp (-t)-Real.sinh ((r-1)*t)/Real.sinh (r*t)=
      2*Real.sinh t/(Real.exp (2*r*t)-1) := by
  have hs : Real.sinh (r*t)≠0 := (Real.sinh_pos_iff.mpr (mul_pos hr ht)).ne'
  calc
    _=(Real.cosh (r*t)-Real.sinh (r*t))*Real.sinh t/Real.sinh (r*t) := by
      rw [show (r-1)*t=r*t-t by ring,Real.sinh_sub,← Real.cosh_sub_sinh t]
      field_simp
      <;> ring
    _=(Real.exp (-(r*t))/Real.sinh (r*t))*Real.sinh t := by rw [Real.cosh_sub_sinh]; ring
    _=2*Real.sinh t/(Real.exp (2*r*t)-1) := by
      rw [exp_neg_div_sinh (r*t) (mul_pos hr ht)]
      have he : 2*(r*t)=2*r*t := by ring
      rw [he]
      ring

/-- The path continuant resolvent converges to the actual half-line scalar
factor exp(-t), with an explicit positive error. -/
theorem endpoint_ratio_tendsto (t : ℝ) (ht : 0<t) :
    Tendsto (fun n : ℕ => continuant (2*Real.cosh t) n/continuant (2*Real.cosh t) (n+1))
      atTop (𝓝 (Real.exp (-t))) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)+2) atTop atTop :=
    Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds
  have harg : Tendsto (fun n : ℕ => 2*((n : ℝ)+2)*t) atTop atTop := by
    have h := hn.const_mul_atTop (show 0<2*t by positivity)
    convert h using 1
    funext n
    ring
  have hd : Tendsto (fun n : ℕ => Real.exp (2*((n : ℝ)+2)*t)-1) atTop atTop := by
    simpa only [sub_eq_add_neg,Function.comp_def] using (Real.tendsto_exp_atTop.comp harg).atTop_add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 (-1)))
  have hz := (tendsto_const_nhds.div_atTop hd :
    Tendsto (fun n : ℕ => (2*Real.sinh t)/(Real.exp (2*((n : ℝ)+2)*t)-1)) atTop (𝓝 0))
  have h := hz.const_sub (Real.exp (-t))
  simp only [sub_zero] at h
  apply h.congr
  intro n
  rw [endpoint_ratio t ht]
  have hh := endpoint_loss ((n : ℝ)+2) t (by positivity) ht
  have he : (n : ℝ)+2-1=(n : ℝ)+1 := by ring
  rw [he] at hh
  linarith

end
end SpanningTreeIsoperimetry.BoundaryHyperbolic
