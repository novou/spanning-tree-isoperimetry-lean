module

public import SpanningTreeIsoperimetry.BoundaryKernelMajorant
public import SpanningTreeIsoperimetry.BoundaryBoseMoments

@[expose] public section

/-! The transformed singleton boundary density dominates the cubic Bose
weight up to the explicit cutoff 5/4. -/
namespace SpanningTreeIsoperimetry.BoundarySingletonWeight
open Set MeasureTheory RectangularRemainder BoundaryKernelMajorant BoundaryBoseMoments
open scoped Topology
noncomputable section

theorem cosh_gamma (θ : ℝ) : Real.cosh (gamma θ)=2-Real.cos θ := by
  have hcos : Real.cos θ=1-2*Real.sin (θ/2)^2 := by
    convert Real.cos_two_mul_eq_one_sub (θ/2) using 1 <;> congr 1 <;> ring
  rw [gamma,Real.cosh_two_mul,Real.sinh_arsinh,Real.cosh_arsinh,Real.sq_sqrt (by positivity)]
  nlinarith [hcos]

theorem cosh_cutoff_lt : Real.cosh (5/4 : ℝ) < 2 := by
  have hu := Real.exp_bound' (x := (5/8 : ℝ)) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial] at hu
  have hu' : Real.exp (5/8 : ℝ) < 15/8 := by linarith
  have hl := Real.sum_le_exp_of_nonneg (x := (5/4 : ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ,Nat.factorial] at hl
  have he : Real.exp (5/4 : ℝ)=Real.exp (5/8 : ℝ)^2 := by
    rw [pow_two,← Real.exp_add]
    norm_num
  have hb : Real.exp (5/4 : ℝ) < 225/64 := by
    rw [he]
    nlinarith [Real.exp_pos (5/8 : ℝ)]
  have hi : (Real.exp (5/4 : ℝ))⁻¹ < 1/3 := by
    rw [inv_lt_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ)<1/3)]
    norm_num
    linarith
  rw [Real.cosh_eq,Real.exp_neg]
  linarith

theorem gamma_half_pi_gt_cutoff : (5/4 : ℝ)<gamma (Real.pi/2) := by
  have hc : Real.cosh (gamma (Real.pi/2))=2 := by rw [cosh_gamma,Real.cos_pi_div_two]; ring
  have hg : 0≤gamma (Real.pi/2) := gamma_nonneg ⟨by positivity,by linarith [Real.pi_pos]⟩
  have h := Real.cosh_lt_cosh.mp (show Real.cosh (5/4 : ℝ)<Real.cosh (gamma (Real.pi/2)) by rw [hc]; exact cosh_cutoff_lt)
  simpa only [abs_of_nonneg hg,abs_of_pos (by norm_num : (0 : ℝ)<5/4)] using h

theorem singleton_weight_lower {θ : ℝ} (hθ : θ∈Icc (0 : ℝ) (Real.pi/2)) :
    (gamma θ)^3≤Real.sin θ*Real.sinh (gamma θ)^2 := by
  let v := Real.sin (θ/2)
  let u := Real.cos (θ/2)
  have hv : 0≤v := Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],by linarith [hθ.2,Real.pi_pos]⟩
  have hu : 0≤u := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1,Real.pi_pos],by linarith [hθ.2,Real.pi_pos]⟩
  have huv : v^2+u^2=1 := Real.sin_sq_add_cos_sq (θ/2)
  have hcθ : 0≤Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1,Real.pi_pos],hθ.2⟩
  have hc : Real.cos θ=1-2*v^2 := by
    dsimp only [v]
    convert Real.cos_two_mul_eq_one_sub (θ/2) using 1 <;> congr 1 <;> ring
  have hv2 : v^2≤1/2 := by linarith
  have hpoly : 0≤1-v^2-v^4 := by
    have hh := pow_le_pow_left₀ (sq_nonneg v) hv2 2
    nlinarith only [hh,hv2]
  have hsq : 1≤(u*(1+v^2))^2 := by
    have he : (u*(1+v^2))^2=1+v^2*(1-v^2-v^4) := by
      rw [mul_pow,show u^2=1-v^2 by linarith]
      ring
    rw [he]
    linarith [mul_nonneg (sq_nonneg v) hpoly]
  have hu1 : 1≤u*(1+v^2) := by
    have hh : 0≤u*(1+v^2) := by positivity
    nlinarith
  have hg : gamma θ≤2*v := by
    have hh := Real.self_le_sinh_iff.mpr (Real.arsinh_nonneg_iff.mpr hv)
    rw [Real.sinh_arsinh] at hh
    dsimp only [gamma,v]
    linarith
  have hsin : Real.sin θ=2*v*u := by
    dsimp only [v,u]
    convert Real.sin_two_mul (θ/2) using 1 <;> congr 1 <;> ring
  have hsg : Real.sinh (gamma θ)^2=4*v^2*(1+v^2) := by
    rw [gamma,Real.sinh_two_mul,Real.sinh_arsinh,Real.cosh_arsinh]
    have hroot := Real.sq_sqrt (show 0≤1+v^2 by positivity)
    dsimp only [v] at hroot ⊢
    nlinarith only [hroot]
  have hg0 := gamma_nonneg (show θ∈Icc (0 : ℝ) Real.pi from ⟨hθ.1,by linarith [hθ.2,Real.pi_pos]⟩)
  have hp := pow_le_pow_left₀ hg0 hg 3
  have hm := mul_le_mul_of_nonneg_left hu1 (show 0≤8*v^3 by positivity)
  rw [hsin,hsg]
  nlinarith only [hp,hm]

end
end SpanningTreeIsoperimetry.BoundarySingletonWeight
