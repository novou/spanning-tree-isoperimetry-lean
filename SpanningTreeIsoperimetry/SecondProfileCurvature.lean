module

public import SpanningTreeIsoperimetry.SecondProfileCalculus

@[expose] public section

set_option backward.privateInPublic true

/-! Explicit curvature bounds for the genuine second rectangular profile. -/
namespace SpanningTreeIsoperimetry.SecondProfileCurvature

open SecondProfileModes SecondProfileCalculus RectangularSecondProfile CoupledRectangleError
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

private def endpointPolynomial (x : ℝ) : ℝ := 160*x^2-100*x+10
private def upperWeight (n : ℕ) : ℝ := ((n : ℝ)+1)^4-if n=1 then 7 else 0
private def endpointOneMajorant (q : ℝ) (n : ℕ) : ℝ :=
  upperWeight n*endpointPolynomial ((n : ℝ)+1)*q^(n+1)
private def endpointThreeMajorant (q : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ)+1)^4*(1920*((n : ℝ)+1)^2+22)*q^(n+1)

private theorem upperWeight_ge (n : ℕ) : weight n≤upperWeight n := by
  by_cases hn : n=1
  · subst n
    norm_num [upperWeight,weight_one]
  · simpa only [upperWeight,if_neg hn,sub_zero] using weight_le_fourth n

private theorem endpointPolynomial_nonneg {x : ℝ} (hx : 1≤x) : 0≤endpointPolynomial x := by
  unfold endpointPolynomial
  nlinarith [sq_nonneg (x-1)]

private theorem pi_bounds : (25 : ℝ)/8≤Real.pi ∧ Real.pi^2≤10 ∧ Real.pi≤22/7 := by
  have hu := Real.pi_lt_d4
  have hl := Real.pi_gt_d2
  have hp := Real.pi_pos
  constructor
  · linarith
  constructor
  · nlinarith
  · linarith

private theorem mode_one_polynomial_le (n : ℕ) :
    secondModePolynomial (frequency n) 1≤endpointPolynomial ((n : ℝ)+1) := by
  have h1 := mul_le_mul_of_nonneg_right pi_bounds.1 (show 0≤32*((n : ℝ)+1) by positivity)
  have h2 := mul_le_mul_of_nonneg_right pi_bounds.2.1 (show 0≤16*((n : ℝ)+1)^2 by positivity)
  unfold secondModePolynomial frequency endpointPolynomial
  norm_num
  nlinarith

private theorem mode_three_polynomial_le (n : ℕ) :
    secondModePolynomial (frequency n) 3≤1920*((n : ℝ)+1)^2+22 := by
  have h2 := mul_le_mul_of_nonneg_right pi_bounds.2.1 (show 0≤192*((n : ℝ)+1)^2 by positivity)
  have hp := mul_nonneg Real.pi_pos.le (show 0≤(n : ℝ)+1 by positivity)
  unfold secondModePolynomial frequency
  norm_num
  nlinarith

private theorem exponential_q_bound : Real.exp (-2*Real.pi)≤(1 : ℝ)/530 := by
  rw [show -2*Real.pi= -(2*Real.pi) by ring,Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<530)
    exp_two_pi_gt_fivehundredthirty.le

private theorem weightedMode_one_le (n : ℕ) : weightedMode n 2 1≤endpointOneMajorant (1/530) n := by
  rw [weightedMode,coefficient_two,exp_frequency_eq]
  norm_num only [mul_one]
  have hw := weight_nonneg n
  have hw' := upperWeight_ge n
  have hupper : 0≤upperWeight n := hw.trans hw'
  have hEP : 0≤endpointPolynomial ((n : ℝ)+1) := endpointPolynomial_nonneg (by have h : (0 : ℝ)≤n := Nat.cast_nonneg n; linarith)
  have hpoly := mode_one_polynomial_le n
  have hpoly0 := (secondModePolynomial_pos (frequency_ge_six n) (by norm_num : (1 : ℝ)≤1)).le
  have hp := exponential_q_bound
  unfold endpointOneMajorant
  gcongr

private theorem weightedMode_three_le (n : ℕ) :
    weightedMode n 2 3≤endpointThreeMajorant ((1/530)^3) n := by
  rw [weightedMode,coefficient_two,exp_frequency_eq]
  have he : Real.exp (-2*Real.pi*3)=Real.exp (-2*Real.pi)^3 := by
    rw [← Real.exp_nat_mul]
    norm_num <;> ring
  rw [he]
  have hw := weight_nonneg n
  have hw' := weight_le_fourth n
  have hpoly := mode_three_polynomial_le n
  have hpoly0 := (secondModePolynomial_pos (frequency_ge_six n) (by norm_num : (1 : ℝ)≤3)).le
  have hp := exponential_q_bound
  unfold endpointThreeMajorant
  gcongr

private theorem hasSum_shift_of_zero {f : ℕ → ℝ} {M : ℝ} (hf : HasSum f M) (h0 : f 0=0) :
    HasSum (fun n : ℕ => f (n+1)) M := by
  have hs := (summable_nat_add_iff 1).mpr hf.summable
  have hv := hf.summable.sum_add_tsum_nat_add 1
  have hv' : (∑' n : ℕ, f (n+1))=M := by
    simpa only [Finset.sum_range_one,h0,zero_add,hf.tsum_eq] using hv
  simpa only [hv'] using hs.hasSum

private theorem shiftedMoment_four {q : ℝ} (hq : |q|<1) :
    HasSum (fun n : ℕ => ((n : ℝ)+1)^4*q^(n+1)) (moment4 q) := by
  have h := (geometricMoment_summable 4 hq).hasSum
  rw [← geometricMoment,geometricMoment_four hq] at h
  simpa only [Nat.cast_add,Nat.cast_one] using hasSum_shift_of_zero h (by norm_num)

private theorem shiftedMoment_five {q : ℝ} (hq : |q|<1) :
    HasSum (fun n : ℕ => ((n : ℝ)+1)^5*q^(n+1)) (moment5 q) := by
  have h := (geometricMoment_summable 5 hq).hasSum
  rw [← geometricMoment,geometricMoment_five hq] at h
  simpa only [Nat.cast_add,Nat.cast_one] using hasSum_shift_of_zero h (by norm_num)

private theorem shiftedMoment_six {q : ℝ} (hq : |q|<1) :
    HasSum (fun n : ℕ => ((n : ℝ)+1)^6*q^(n+1)) (moment6 q) := by
  have h := (geometricMoment_summable 6 hq).hasSum
  rw [← geometricMoment,geometricMoment_six hq] at h
  simpa only [Nat.cast_add,Nat.cast_one] using hasSum_shift_of_zero h (by norm_num)

private theorem endpointOneMajorant_hasSum {q : ℝ} (hq : |q|<1) :
    HasSum (endpointOneMajorant q) (160*moment6 q-100*moment5 q+10*moment4 q-3150*q^2) := by
  have hd := hasSum_ite_eq (1 : ℕ) (3150*q^2)
  have h := ((((shiftedMoment_six hq).mul_left 160).sub ((shiftedMoment_five hq).mul_left 100)).add
    ((shiftedMoment_four hq).mul_left 10)).sub hd
  convert h using 1
  funext n
  by_cases hn : n=1
  · subst n
    norm_num [endpointOneMajorant,upperWeight,endpointPolynomial]
    ring
  · simp only [endpointOneMajorant,upperWeight,if_neg hn,endpointPolynomial,Pi.sub_apply,Pi.add_apply]
    ring

private theorem endpointThreeMajorant_hasSum {q : ℝ} (hq : |q|<1) :
    HasSum (endpointThreeMajorant q) (1920*moment6 q+22*moment4 q) := by
  have h := ((shiftedMoment_six hq).mul_left 1920).add ((shiftedMoment_four hq).mul_left 22)
  convert h using 1
  funext n
  simp only [endpointThreeMajorant,Pi.add_apply]
  ring

theorem K2D2_one_lt : K2D2 1<1 := by
  have hm := endpointOneMajorant_hasSum (q := (1 : ℝ)/530) (by norm_num)
  have hs : sumMode 2 1≤160*moment6 (1/530)-100*moment5 (1/530)+10*moment4 (1/530)-3150*(1/530)^2 :=
    ((weightedMode_summable (by norm_num : (0 : ℝ)<1) (k := 2) (by omega)).tsum_le_tsum
      weightedMode_one_le hm.summable).trans_eq hm.tsum_eq
  have hs0 := sumMode_two_nonneg (by norm_num : (1 : ℝ)≤1)
  have hM0 : 0≤160*moment6 (1/530)-100*moment5 (1/530)+10*moment4 (1/530)-3150*(1/530)^2 :=
    hs0.trans hs
  unfold K2D2 profilePolynomialSecond
  norm_num only [mul_one]
  apply lt_of_le_of_lt _ curvature_single_coefficient_one_lt
  have hp := pi_bounds.2.2
  gcongr

theorem K2D2_three_lt : K2D2 3<1/2 := by
  have hm := endpointThreeMajorant_hasSum (q := ((1 : ℝ)/530)^3) (by norm_num)
  have hs : sumMode 2 3≤1920*moment6 ((1/530)^3)+22*moment4 ((1/530)^3) :=
    ((weightedMode_summable (by norm_num : (0 : ℝ)<3) (k := 2) (by omega)).tsum_le_tsum
      weightedMode_three_le hm.summable).trans_eq hm.tsum_eq
  have hs0 := sumMode_two_nonneg (by norm_num : (1 : ℝ)≤3)
  have hM0 : 0≤1920*moment6 ((1/530)^3)+22*moment4 ((1/530)^3) := hs0.trans hs
  unfold K2D2 profilePolynomialSecond
  norm_num only
  apply lt_of_le_of_lt _ curvature_single_coefficient_three_lt
  have hp := pi_bounds.2.2
  gcongr

theorem K2D2_lt_one {u : ℝ} (hu : u∈Set.Icc 1 3) : K2D2 u<1 :=
  (K2D2_le_endpoints hu).trans_lt (max_lt K2D2_one_lt (K2D2_three_lt.trans (by norm_num)))

/-- Actual second-profile curvature, with all series estimates discharged. -/
theorem K2_curvature {u : ℝ} (hu : u∈Set.Icc 1 3) :
    0 < iteratedDeriv 2 K2 u ∧ iteratedDeriv 2 K2 u < 1 := by
  rw [iteratedDeriv_K2_two (by linarith [hu.1] : 0<u)]
  exact ⟨K2D2_pos hu.1,K2D2_lt_one hu⟩

end
end SpanningTreeIsoperimetry.SecondProfileCurvature
