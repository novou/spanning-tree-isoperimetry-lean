module

public import SpanningTreeIsoperimetry.StripFourierCoefficients
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

@[expose] public section

set_option backward.privateInPublic true

/-! Elementary primitives for the actual first strip-symbol coefficients.
The recurrence integrates x^(2m)/sqrt(2-x²) on [-1,1]. -/
namespace SpanningTreeIsoperimetry.StripFourierMoments
open Set
noncomputable section

def root (x : ℝ) : ℝ := Real.sqrt (2-x^2)

def primitive : ℕ → ℝ → ℝ
  | 0, x => Real.arctan (x/root x)
  | n+1, x => ((2*(n : ℝ)+1)/((n : ℝ)+1))*primitive n x-
      x^(2*n+1)*root x/(2*((n : ℝ)+1))

theorem root_pos {x : ℝ} (hx : x∈Icc (-1) 1) : 0<root x := by
  unfold root
  apply Real.sqrt_pos.mpr
  nlinarith [hx.1,hx.2]

theorem root_sq {x : ℝ} (hx : x∈Icc (-1) 1) : root x^2=2-x^2 := by
  apply Real.sq_sqrt
  nlinarith [hx.1,hx.2]

theorem hasDerivAt_root {x : ℝ} (hx : x∈Icc (-1) 1) :
    HasDerivAt root (-x/root x) x := by
  have hd := ((hasDerivAt_const x (2 : ℝ)).sub ((hasDerivAt_id x).fun_pow 2)).sqrt
    (show 2-x^2≠0 by nlinarith [hx.1,hx.2])
  unfold root
  convert hd using 1 <;> dsimp <;> ring

theorem hasDerivAt_primitive_zero {x : ℝ} (hx : x∈Icc (-1) 1) :
    HasDerivAt (primitive 0) (1/root x) x := by
  have hw := (root_pos hx).ne'
  have hs := root_sq hx
  have hd := (Real.hasDerivAt_arctan (x/root x)).comp x
    ((hasDerivAt_id x).fun_div (hasDerivAt_root hx) hw)
  change HasDerivAt (fun y => Real.arctan (y/root y)) _ x at hd
  change HasDerivAt (fun y => Real.arctan (y/root y)) _ x
  convert hd using 1
  dsimp only [id_eq]
  field_simp
  nlinarith [hs]

private theorem recurrence_derivative (n : ℕ) (x w : ℝ) (hw : w≠0) (hs : w^2=2-x^2) :
    ((2*(n : ℝ)+1)/((n : ℝ)+1))*(x^(2*n)/w)-
      (((2*(n : ℝ)+1)*x^(2*n)*w+x^(2*n+1)*(-x/w))/(2*((n : ℝ)+1)))=
        x^(2*(n+1))/w := by
  have hn : (n : ℝ)+1≠0 := by positivity
  rw [show 2*(n+1)=2*n+2 by omega,pow_add,pow_succ]
  field_simp
  have hm := congrArg (fun y : ℝ => x^(2*n)*(2*(n : ℝ)+1)*y) hs
  simp only [pow_add,pow_succ]
  nlinarith [hm]

theorem hasDerivAt_primitive (n : ℕ) {x : ℝ} (hx : x∈Icc (-1) 1) :
    HasDerivAt (primitive n) (x^(2*n)/root x) x := by
  induction n with
  | zero => simpa only [Nat.mul_zero,pow_zero] using hasDerivAt_primitive_zero hx
  | succ n ih =>
    have hd := (ih.const_mul ((2*(n : ℝ)+1)/((n : ℝ)+1))).sub
      ((((hasDerivAt_id x).fun_pow (2*n+1)).mul (hasDerivAt_root hx)).div_const (2*((n : ℝ)+1)))
    have hn : 2*n+1-1=2*n := by omega
    simp only [hn,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,mul_one] at hd
    convert hd using 1
    · funext y
      rfl
    · exact (recurrence_derivative n x (root x) (root_pos hx).ne' (root_sq hx)).symm

theorem primitive_zero (n : ℕ) : primitive n 0=0 := by
  induction n with
  | zero => simp [primitive]
  | succ n ih => simp [primitive,ih]

theorem primitive_one_zero : primitive 0 1=Real.pi/4 := by
  norm_num [primitive,root,Real.arctan_one]

theorem primitive_one_one : primitive 1 1=Real.pi/4-1/2 := by
  norm_num [primitive,root,Real.arctan_one]

theorem primitive_one_two : primitive 2 1=3*Real.pi/8-1 := by
  norm_num [primitive,root,Real.arctan_one]
  ring

theorem primitive_one_three : primitive 3 1=5*Real.pi/8-11/6 := by
  norm_num [primitive,root,Real.arctan_one]
  ring

theorem primitive_one_four : primitive 4 1=35*Real.pi/32-10/3 := by
  norm_num [primitive,root,Real.arctan_one]
  ring

theorem primitive_one_five : primitive 5 1=63*Real.pi/32-61/10 := by
  norm_num [primitive,root,Real.arctan_one]
  ring

end
end SpanningTreeIsoperimetry.StripFourierMoments
