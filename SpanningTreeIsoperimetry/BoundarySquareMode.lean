module

public import SpanningTreeIsoperimetry.FiniteSingletonSquares
public import SpanningTreeIsoperimetry.AngularKernelTaylor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-! A quantitative first-mode lower bound for the second boundary of a square. -/
namespace SpanningTreeIsoperimetry.BoundarySquareMode
open Set RectangularRemainder BoundaryKernelMajorant BoundarySingletonIntegral
  BoundaryKernelBounds AngularKernelTaylor
open scoped BigOperators
noncomputable section

theorem sinh_gamma_ge {θ : ℝ} (hθ : θ∈Icc (0 : ℝ) 1) : θ≤Real.sinh (gamma θ) := by
  let v := Real.sin (θ/2)
  have hv : 0≤v := Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],by linarith [hθ.2,Real.pi_gt_three]⟩
  have hv1 : v≤1 := Real.sin_le_one _
  have hvs : v^2≤1 := by nlinarith
  have hvs4 : v^4≤v^2 := by nlinarith [mul_nonneg (sq_nonneg v) (sub_nonneg.mpr hvs)]
  have hsqrt := Real.sq_sqrt (show 0≤1+v^2 by positivity)
  have hroot : 1+v^2/3≤Real.sqrt (1+v^2) := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    nlinarith only [hsqrt,hvs4]
  have hsin : θ/2-θ^3/48≤v := by
    have h := Real.sin_ge_sub_cube (show 0≤θ/2 by linarith [hθ.1])
    dsimp only [v]
    nlinarith only [h]
  have hθ3 : θ^3≤θ := by
    have hh : θ^2≤1 := by nlinarith [hθ.1,hθ.2]
    have hh' := mul_le_mul_of_nonneg_left hh hθ.1
    nlinarith only [hh']
  have hvθ : (23/48 : ℝ)*θ≤v := by linarith
  have hc := pow_le_pow_left₀ (show 0≤(23/48 : ℝ)*θ from mul_nonneg (by norm_num) hθ.1) hvθ 3
  have hm := mul_le_mul_of_nonneg_left hroot (show 0≤2*v by positivity)
  have he : Real.sinh (gamma θ)=2*v*Real.sqrt (1+v^2) := by
    rw [gamma,Real.sinh_two_mul,Real.sinh_arsinh,Real.cosh_arsinh]
  rw [he]
  nlinarith only [hsin,hc,hm,pow_nonneg hθ.1 3]

theorem sin_sq_lower {θ : ℝ} (hθ : θ∈Icc (0 : ℝ) 1) :
    θ^2*(1-θ^2/3)≤Real.sin θ^2 := by
  have hb := Real.sin_ge_sub_cube hθ.1
  have hθ3 : θ^3≤θ := by
    have hh : θ^2≤1 := by nlinarith [hθ.1,hθ.2]
    nlinarith [mul_le_mul_of_nonneg_left hh hθ.1]
  have h0 : 0≤θ-θ^3/6 := by linarith [hθ.1]
  have hs := pow_le_pow_left₀ h0 hb 2
  nlinarith [sq_nonneg (θ^3)]

theorem exp_negative_correction {x : ℝ} (hx : 0 < x) (hx1 : x≤5/8) :
    Real.exp (-(2*x/5))<1-x/3 := by
  have he := Real.sum_le_exp_of_nonneg (x := 2*x/5) (by positivity) 3
  norm_num [Finset.sum_range_succ,Nat.factorial] at he
  have hx2 : x^2≤25/64 := by
    have h := pow_le_pow_left₀ hx.le hx1 2
    norm_num at h ⊢
    exact h
  have hpoly : 0 < 5-4*x-2*x^2 := by nlinarith
  have hp := mul_pos hx hpoly
  have hb : 0 < 1-x/3 := by linarith
  have hh := mul_le_mul_of_nonneg_left he hb.le
  rw [Real.exp_neg]
  rw [inv_eq_one_div,div_lt_iff₀ (Real.exp_pos _)]
  nlinarith only [hp,hh]

theorem exp_two_pi_lt : Real.exp (2*Real.pi)<540 := by
  have hb := Real.exp_bound' (x := (11/14 : ℝ)) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at hb
  have hu : Real.exp (11/14 : ℝ)<439/200 := by linarith
  have hp : Real.pi/4<(11/14 : ℝ) := by linarith [Real.pi_lt_d6]
  have hh : Real.exp (Real.pi/4)<439/200 := (Real.exp_lt_exp.mpr hp).trans hu
  have hh8 := pow_lt_pow_left₀ hh (Real.exp_pos _).le (by decide : 8≠0)
  have he : Real.exp (2*Real.pi)=Real.exp (Real.pi/4)^8 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  rw [he]
  norm_num at hh8
  linarith

theorem first_mode_density {r : ℝ} (hr : 4≤r) :
    4*Real.pi^3/(Real.exp (2*Real.pi)-1)<
      r^4*((4/r)*density r 1 1 1 1 (Real.pi/r)) := by
  have hr0 : 0 < r := by linarith
  let θ := Real.pi/r
  have hθ0 : 0 < θ := by dsimp [θ]; positivity
  have hθpi : θ≤Real.pi/4 := by
    dsimp [θ]
    exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hr
  have hθ1 : θ≤1 := by linarith [Real.pi_lt_d2]
  have hθ2 : θ^2≤5/8 := by
    have hpi : Real.pi^2<10 := by nlinarith [Real.pi_lt_d2,Real.pi_pos]
    have hh := pow_le_pow_left₀ hθ0.le hθpi 2
    nlinarith
  have ht := gamma_fifth_defect (show θ∈Icc (0 : ℝ) Real.pi from ⟨hθ0.le,by linarith [hθpi,Real.pi_pos]⟩)
  have h5 : θ^5≤(5/8 : ℝ)*θ^3 := by
    have hh := mul_le_mul_of_nonneg_right hθ2 (pow_nonneg hθ0.le 3)
    nlinarith only [hh]
  have hg : gamma θ≤θ-θ^3/15 := by nlinarith [ht.2,pow_nonneg hθ0.le 3]
  have hrt : r*θ=Real.pi := by dsimp [θ]; field_simp
  have hgstrict : 2*r*gamma θ<2*Real.pi-2*θ^2/5 := by
    have hh := mul_le_mul_of_nonneg_left hg (show 0≤2*r by positivity)
    have hprod : r*θ^3=Real.pi*θ^2 := by nlinarith only [congrArg (fun t : ℝ => t*θ^2) hrt]
    have hpos := mul_pos (sub_pos.mpr Real.pi_gt_three) (sq_pos_of_pos hθ0)
    nlinarith only [hh,hrt,hprod,hpos]
  have hγ := gamma_pos (show θ∈Ioo (0 : ℝ) Real.pi from ⟨hθ0,by linarith [hθpi,Real.pi_pos]⟩)
  have hden : 0 < Real.exp (2*r*gamma θ)-1 := by
    have hh := Real.one_lt_exp_iff.mpr (show 0 < 2*r*gamma θ by positivity)
    linarith
  have hE : 0 < Real.exp (2*Real.pi)-1 := by
    have hh := Real.one_lt_exp_iff.mpr (show 0 < 2*Real.pi by positivity)
    linarith
  have hB : 0 < 1-θ^2/3 := by linarith
  have hexp := exp_negative_correction (sq_pos_of_pos hθ0) hθ2
  have hbound : Real.exp (2*r*gamma θ)-1<
      (Real.exp (2*Real.pi)-1)*(1-θ^2/3) := by
    have h1 := Real.exp_lt_exp.mpr hgstrict
    rw [Real.exp_sub] at h1
    have he : Real.exp (2*Real.pi)/Real.exp (2*θ^2/5)=
        Real.exp (2*Real.pi)*Real.exp (-(2*θ^2/5)) := by rw [Real.exp_neg]; rfl
    rw [he] at h1
    have h2 := mul_lt_mul_of_pos_left hexp (Real.exp_pos (2*Real.pi))
    nlinarith only [h1,h2,sq_pos_of_pos hθ0]
  have hnum : θ^3*(1-θ^2/3)≤Real.sin θ^2*Real.sinh (gamma θ) := by
    have hh := mul_le_mul (sin_sq_lower ⟨hθ0.le,hθ1⟩) (sinh_gamma_ge ⟨hθ0.le,hθ1⟩)
      hθ0.le (sq_nonneg (Real.sin θ))
    convert hh using 1 <;> ring
  have hratio : θ^3/(Real.exp (2*Real.pi)-1)<density r 1 1 1 1 θ := by
    rw [density_singleton_eq,div_lt_div_iff₀ hE hden]
    have h1 := mul_lt_mul_of_pos_left hbound (pow_pos hθ0 3)
    have h2 := mul_le_mul_of_nonneg_right hnum hE.le
    nlinarith only [h1,h2]
  have hh := mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hratio (show 0 < 4/r by positivity)) (pow_pos hr0 4)
  convert hh using 1
  dsimp only [θ]
  field_simp
  <;> ring

end
end SpanningTreeIsoperimetry.BoundarySquareMode
