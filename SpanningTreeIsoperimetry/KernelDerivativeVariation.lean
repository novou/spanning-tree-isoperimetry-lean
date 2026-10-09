import SpanningTreeIsoperimetry.LatticeKernelDerivatives
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Explicit total-variation bounds for the third and fifth angular-kernel
derivatives, using the proved numerator polynomials and the FTC. -/
namespace SpanningTreeIsoperimetry.KernelDerivativeVariation

open Set Polynomial MeasureTheory LatticeKernelDerivatives RectangularRemainder
open scoped Interval
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

private def fourthNumerator : ℝ[X] := C 2*P4
private def sixthNumerator : ℝ[X] := -C 4*P6

private theorem fourthNumerator_antitone : AntitoneOn (fun x => fourthNumerator.eval x) (Set.Icc 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
  · exact fourthNumerator.continuous.continuousOn
  · exact fun x _ => (fourthNumerator.hasDerivAt x).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x∈Set.Ioo 0 1 := by simpa only [interior_Icc] using hx
    rw [(fourthNumerator.hasDerivAt x).deriv]
    norm_num [fourthNumerator,P4,Polynomial.derivative_add,Polynomial.derivative_sub,
      Polynomial.derivative_mul,Polynomial.derivative_pow]
    linarith [hx'.2]

private theorem sixthNumerator_convex : ConvexOn ℝ (Set.Icc 0 1) (fun x => sixthNumerator.eval x) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fun x => sixthNumerator.derivative.eval x)
    (f'' := fun x => sixthNumerator.derivative.derivative.eval x) (convex_Icc 0 1)
  · exact sixthNumerator.continuous.continuousOn
  · exact fun x _ => (sixthNumerator.hasDerivAt x).hasDerivWithinAt
  · exact fun x _ => (sixthNumerator.derivative.hasDerivAt x).hasDerivWithinAt
  · intro x hx
    have hx' : x∈Set.Ioo 0 1 := by simpa only [interior_Icc] using hx
    norm_num [sixthNumerator,P6,Polynomial.derivative_add,Polynomial.derivative_sub,
      Polynomial.derivative_mul,Polynomial.derivative_pow]
    nlinarith [hx'.2,sq_nonneg x]

private theorem root_in_unit {f : ℝ → ℝ} (hf : Continuous f) (h0 : 0<f 0) (h1 : f 1<0) :
    ∃ z∈Set.Ioo (0 : ℝ) 1, f z=0 := by
  obtain ⟨z,hz,hfz⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ)≤1) hf.continuousOn
    (show (0 : ℝ)∈Set.Icc (f 1) (f 0) from ⟨h1.le,h0.le⟩)
  refine ⟨z,⟨?_,?_⟩,hfz⟩
  · by_contra hn
    have hz0 : z=0 := by linarith [hz.1]
    rw [hz0] at hfz
    linarith
  · by_contra hn
    have hz1 : z=1 := by linarith [hz.2]
    rw [hz1] at hfz
    linarith

/-- Convexity and a negative right endpoint control both sides of a root.
This is the geometric sign argument for the sixth-derivative numerator. -/
private theorem convex_crossing_signs {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Icc 0 1) f)
    {z : ℝ} (hz : z∈Set.Ioo 0 1) (hfz : f z=0) (hf1 : f 1<0) :
    (∀ x∈Set.Icc 0 z, 0≤f x) ∧ (∀ x∈Set.Icc z 1, f x≤0) := by
  constructor
  · intro x hx
    by_cases he : x=z
    · simp [he,hfz]
    · have hxz : x<z := lt_of_le_of_ne hx.2 he
      have hs := hf.slope_mono_adjacent (show x∈Set.Icc 0 1 from ⟨hx.1,by linarith [hx.2,hz.2]⟩)
        (show (1 : ℝ)∈Set.Icc 0 1 by constructor <;> norm_num) hxz hz.2
      rw [hfz,sub_zero,zero_sub] at hs
      have hright : f 1/(1-z)<0 := div_neg_of_neg_of_pos hf1 (by linarith [hz.2])
      have hleft : -f x/(z-x)<0 := lt_of_le_of_lt hs hright
      have hn := (div_lt_iff₀ (by linarith : 0<z-x)).mp hleft
      linarith
  · intro x hx
    have h := hf.le_max_of_mem_Icc (show z∈Set.Icc 0 1 from ⟨hz.1.le,hz.2.le⟩)
      (show (1 : ℝ)∈Set.Icc 0 1 by constructor <;> norm_num) hx
    rw [hfz,max_eq_left hf1.le] at h
    exact h

private theorem sine_square_monotone : MonotoneOn (fun θ => halfSin θ^2) (Set.Icc 0 Real.pi) := by
  intro x hx y hy hxy
  have hs := Real.strictMonoOn_sin.monotoneOn
    (show x/2∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [hx.1,hx.2,Real.pi_pos])
    (show y/2∈Set.Icc (-(Real.pi/2)) (Real.pi/2) by constructor <;> linarith [hy.1,hy.2,Real.pi_pos])
    (by linarith : x/2≤y/2)
  change halfSin x≤halfSin y at hs
  have hx0 := (halfSin_mem hx).1
  have hy0 := (halfSin_mem hy).1
  nlinarith

private theorem angle_for_sine_square {z : ℝ} (hz : z∈Set.Icc 0 1) :
    ∃ θ∈Set.Icc 0 Real.pi, halfSin θ^2=z := by
  have hcont : Continuous (fun θ => halfSin θ^2) := by unfold halfSin; fun_prop
  apply intermediate_value_Icc Real.pi_pos.le hcont.continuousOn
  simpa [halfSin] using hz

private theorem gammaD4_sign_split :
    ∃ c∈Set.Icc 0 Real.pi,
      (∀ θ∈Set.Icc 0 c, 0≤gammaD4 θ) ∧ (∀ θ∈Set.Icc c Real.pi, gammaD4 θ≤0) := by
  obtain ⟨z,hz,hzero⟩ := root_in_unit fourthNumerator.continuous
    (by norm_num [fourthNumerator,P4]) (by norm_num [fourthNumerator,P4])
  obtain ⟨c,hc,hcval⟩ := angle_for_sine_square ⟨hz.1.le,hz.2.le⟩
  refine ⟨c,hc,?_,?_⟩
  · intro θ hθ
    have hθ' : θ∈Set.Icc 0 Real.pi := ⟨hθ.1,hθ.2.trans hc.2⟩
    have hs := sine_square_monotone hθ' hc hθ.2
    dsimp only at hs
    rw [hcval] at hs
    have hsq : halfSin θ^2∈Set.Icc 0 1 := ⟨sq_nonneg _,by have h := halfSin_mem hθ'; nlinarith [h.1,h.2]⟩
    have hp := fourthNumerator_antitone hsq ⟨hz.1.le,hz.2.le⟩ hs
    dsimp only at hp
    rw [hzero] at hp
    have hp' : 0≤P4.eval (halfSin θ^2) := by
      simp only [fourthNumerator,Polynomial.eval_mul,Polynomial.eval_C] at hp
      linarith
    change 0≤halfSin θ*P4.eval (halfSin θ^2)/kernelRoot θ^7
    exact div_nonneg (mul_nonneg (halfSin_mem hθ').1 hp') (pow_nonneg (kernelRoot_pos θ).le _)
  · intro θ hθ
    have hθ' : θ∈Set.Icc 0 Real.pi := ⟨hc.1.trans hθ.1,hθ.2⟩
    have hs := sine_square_monotone hc hθ' hθ.1
    dsimp only at hs
    rw [hcval] at hs
    have hsq : halfSin θ^2∈Set.Icc 0 1 := ⟨sq_nonneg _,by have h := halfSin_mem hθ'; nlinarith [h.1,h.2]⟩
    have hp := fourthNumerator_antitone ⟨hz.1.le,hz.2.le⟩ hsq hs
    dsimp only at hp
    rw [hzero] at hp
    have hp' : P4.eval (halfSin θ^2)≤0 := by
      simp only [fourthNumerator,Polynomial.eval_mul,Polynomial.eval_C] at hp
      linarith
    change halfSin θ*P4.eval (halfSin θ^2)/kernelRoot θ^7≤0
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (halfSin_mem hθ').1 hp')
      (pow_nonneg (kernelRoot_pos θ).le _)

private theorem gammaD6_sign_split :
    ∃ c∈Set.Icc 0 Real.pi,
      (∀ θ∈Set.Icc 0 c, gammaD6 θ≤0) ∧ (∀ θ∈Set.Icc c Real.pi, 0≤gammaD6 θ) := by
  obtain ⟨z,hz,hzero⟩ := root_in_unit sixthNumerator.continuous
    (by norm_num [sixthNumerator,P6]) (by norm_num [sixthNumerator,P6])
  have hsign := convex_crossing_signs sixthNumerator_convex hz hzero (by norm_num [sixthNumerator,P6])
  obtain ⟨c,hc,hcval⟩ := angle_for_sine_square ⟨hz.1.le,hz.2.le⟩
  refine ⟨c,hc,?_,?_⟩
  · intro θ hθ
    have hθ' : θ∈Set.Icc 0 Real.pi := ⟨hθ.1,hθ.2.trans hc.2⟩
    have hs := sine_square_monotone hθ' hc hθ.2
    dsimp only at hs
    rw [hcval] at hs
    have hp := hsign.1 _ ⟨sq_nonneg _,hs⟩
    have hp' : P6.eval (halfSin θ^2)≤0 := by
      simp only [sixthNumerator,Polynomial.eval_mul,Polynomial.eval_neg,Polynomial.eval_C] at hp
      linarith
    change halfSin θ*P6.eval (halfSin θ^2)/kernelRoot θ^11≤0
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (halfSin_mem hθ').1 hp')
      (pow_nonneg (kernelRoot_pos θ).le _)
  · intro θ hθ
    have hθ' : θ∈Set.Icc 0 Real.pi := ⟨hc.1.trans hθ.1,hθ.2⟩
    have hs := sine_square_monotone hc hθ' hθ.1
    dsimp only at hs
    rw [hcval] at hs
    have hsq : halfSin θ^2≤1 := by have h := halfSin_mem hθ'; nlinarith [h.1,h.2]
    have hp := hsign.2 _ ⟨hs,hsq⟩
    have hp' : 0≤P6.eval (halfSin θ^2) := by
      simp only [sixthNumerator,Polynomial.eval_mul,Polynomial.eval_neg,Polynomial.eval_C] at hp
      linarith
    change 0≤halfSin θ*P6.eval (halfSin θ^2)/kernelRoot θ^11
    exact div_nonneg (mul_nonneg (halfSin_mem hθ').1 hp') (pow_nonneg (kernelRoot_pos θ).le _)

private theorem integral_abs_of_derivative_turn (f g : ℝ → ℝ) (a c b : ℝ)
    (hc : a≤c ∧ c≤b) (hg : Continuous g) (hd : ∀ x, HasDerivAt f (g x) x)
    (hl : ∀ x∈Set.Icc a c, 0≤g x) (hr : ∀ x∈Set.Icc c b, g x≤0) :
    (∫ x in a..b, |g x|)=2*f c-f a-f b := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.abs.intervalIntegrable (a := a) (b := c)) (hg.abs.intervalIntegrable (a := c) (b := b))
  have hlEq : (∫ x in a..c, |g x|)=∫ x in a..c, g x := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact abs_of_nonneg (hl x (by simpa only [uIcc_of_le hc.1] using hx))
  have hrEq : (∫ x in c..b, |g x|)=∫ x in c..b, -g x := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact abs_of_nonpos (hr x (by simpa only [uIcc_of_le hc.2] using hx))
  rw [← hadd,hlEq,hrEq,intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hg.intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hg.intervalIntegrable _ _)]
  ring

/-- The actual fourth derivative has the manuscript's total variation bound. -/
theorem integral_abs_gammaD4_le : (∫ θ in (0 : ℝ)..Real.pi, |gammaD4 θ|)≤3/2 := by
  obtain ⟨c,hc,hl,hr⟩ := gammaD4_sign_split
  have hg : Continuous gammaD4 := continuous_iff_continuousAt.mpr fun x => (hasDerivAt_gammaD4 x).continuousAt
  have h := integral_abs_of_derivative_turn gammaD3 gammaD4 0 c Real.pi hc hg hasDerivAt_gammaD3 hl hr
  rw [gammaD3_zero,gammaD3_pi] at h
  have hb := (abs_le.mp (gammaD3_abs_le hc)).2
  linarith

/-- The actual sixth derivative has the manuscript's total variation bound. -/
theorem integral_abs_gammaD6_le : (∫ θ in (0 : ℝ)..Real.pi, |gammaD6 θ|)≤15/4 := by
  obtain ⟨c,hc,hl,hr⟩ := gammaD6_sign_split
  have hg : Continuous gammaD6 := continuous_evenForm P6 10
  have h := integral_abs_of_derivative_turn (fun x => -gammaD5 x) (fun x => -gammaD6 x)
    0 c Real.pi hc hg.neg (fun x => (hasDerivAt_gammaD5 x).neg)
    (fun x hx => by have hh := hl x hx; linarith) (fun x hx => by have hh := hr x hx; linarith)
  simp only [abs_neg,gammaD5_zero,gammaD5_pi] at h
  have hb := (abs_le.mp (gammaD5_abs_le hc)).1
  linarith

end
end SpanningTreeIsoperimetry.KernelDerivativeVariation
