module

public import SpanningTreeIsoperimetry.BoundarySingletonTail

@[expose] public section

/-! Explicit moment lower bounds for the two-cell and square-defect
corrections. Scaling makes both tail estimates uniform for real r≥5. -/
namespace SpanningTreeIsoperimetry.BoundaryShortMoments
open MeasureTheory Set Filter BoundaryBoseMoments BoundaryBoseTail BoundarySingletonTail
open scoped BigOperators Topology
noncomputable section

theorem cubic_tail {r : ℝ} (hr : 5≤r) :
    r^4*(∫ x : ℝ in Ioi 1, bose 3 r x)<(683 : ℝ)/(8*21999) := by
  have hr0 : 0 < r := by linarith
  rw [integral_bose_scale 3 hr0 1,mul_one]
  have hm : (∫ x : ℝ in Ioi r, bose 3 1 x)≤∫ x : ℝ in Ioi 5, bose 3 1 x := by
    apply setIntegral_mono_set ((bose_three_integrable (by norm_num : (0 : ℝ)<1)).mono_set
      (Ioi_subset_Ioi (by norm_num : (0 : ℝ)≤5)))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      exact bose_nonneg 3 (by norm_num) (by have hx' : (5 : ℝ)<x := hx; linarith)
    · exact Filter.Eventually.of_forall (Ioi_subset_Ioi hr)
  have ht := integral_bose_tail_le 3 (r := 1) (A := 5) (by norm_num) (by norm_num)
  norm_num [tailPolynomial,Finset.sum_range_succ,Nat.factorial,Nat.choose] at ht
  apply (hm.trans ht).trans_lt
  rw [div_lt_div_iff₀ (show 0 < Real.exp 10-1 by linarith [exp_ten_gt]) (by norm_num : (0 : ℝ)<8*21999)]
  nlinarith [exp_ten_gt]

theorem fifth_tail {r : ℝ} (hr : 5≤r) :
    r^4*(∫ x : ℝ in Ioi 1, bose 5 r x)<(4433 : ℝ)/(40*21999) := by
  have hr0 : 0 < r := by linarith
  have hm : (∫ x : ℝ in Ioi r, bose 5 1 x)≤∫ x : ℝ in Ioi 5, bose 5 1 x := by
    apply setIntegral_mono_set ((bose_five_integrable (by norm_num : (0 : ℝ)<1)).mono_set
      (Ioi_subset_Ioi (by norm_num : (0 : ℝ)≤5)))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      exact bose_nonneg 5 (by norm_num) (by have hx' : (5 : ℝ)<x := hx; linarith)
    · exact Filter.Eventually.of_forall (Ioi_subset_Ioi hr)
  have ht := integral_bose_tail_le 5 (r := 1) (A := 5) (by norm_num) (by norm_num)
  norm_num [tailPolynomial,Finset.sum_range_succ,Nat.factorial,Nat.choose] at ht
  have hscale := integral_bose_scale 5 hr0 1
  simp only [mul_one] at hscale
  have ht0 : 0≤∫ x : ℝ in Ioi 1, bose 5 r x := by
    apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact bose_nonneg 5 hr0.le (by have hx' : (1 : ℝ)<x := hx; linarith)
  have hr2 : (25 : ℝ)≤r^2 := by nlinarith
  have hpower := mul_le_mul_of_nonneg_right hr2
    (show 0≤r^4*(∫ x : ℝ in Ioi 1, bose 5 r x) by positivity)
  have hbound : r^4*(∫ x : ℝ in Ioi 1, bose 5 r x)≤(4433/40 : ℝ)/(Real.exp 10-1) := by
    have h := hm.trans ht
    rw [← hscale] at h
    have hE : 0 < Real.exp 10-1 := by linarith [exp_ten_gt]
    apply (le_div_iff₀ hE).mpr
    have hh := (le_div_iff₀ hE).mp h
    have hh' := mul_le_mul_of_nonneg_right hpower hE.le
    nlinarith only [hh,hh']
  apply hbound.trans_lt
  rw [div_lt_div_iff₀ (show 0 < Real.exp 10-1 by linarith [exp_ten_gt]) (by norm_num : (0 : ℝ)<40*21999)]
  nlinarith [exp_ten_gt]

theorem strip_moment_lower {r : ℝ} (hr : 5≤r) :
    (21/4 : ℝ)<r^4*((4/Real.pi)*((73/6 : ℝ)*(∫ x in (0 : ℝ)..1, bose 3 r x)-
      (1127/120 : ℝ)*(∫ x in (0 : ℝ)..1, bose 5 r x))) := by
  have hr0 : 0 < r := by linarith
  have h3 := intervalIntegral.integral_Ioi_sub_Ioi (bose_three_integrable hr0) (by norm_num : (0 : ℝ)≤1)
  have h5 := intervalIntegral.integral_Ioi_sub_Ioi (bose_five_integrable hr0) (by norm_num : (0 : ℝ)≤1)
  rw [integral_bose_three hr0] at h3
  rw [integral_bose_five hr0] at h5
  have htail := cubic_tail hr
  have ht5 : 0≤∫ x : ℝ in Ioi 1, bose 5 r x := by
    apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact bose_nonneg 5 hr0.le (by have hx' : (1 : ℝ)<x := hx; linarith)
  have hp3 : (157/50 : ℝ)^3<Real.pi^3 :=
    pow_lt_pow_left₀ (by linarith [Real.pi_gt_d2]) (by norm_num) (by decide)
  have hp5 : Real.pi^5<(63/20 : ℝ)^5 :=
    pow_lt_pow_left₀ (by linarith [Real.pi_lt_d2]) Real.pi_pos.le (by decide)
  have hr2 : (25 : ℝ)≤r^2 := by nlinarith
  have hneg : Real.pi^5/r^2≤(63/20 : ℝ)^5/25 := by
    calc
      _≤Real.pi^5/25 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hr2
      _≤_ := div_le_div_of_nonneg_right hp5.le (by norm_num)
  have hinv : 4/Real.pi<4/3 := by
    rw [div_lt_div_iff₀ Real.pi_pos (by norm_num : (0 : ℝ)<3)]
    nlinarith [Real.pi_gt_three]
  have ht := mul_lt_mul_of_pos_left htail (show 0 < (4/Real.pi)*(73/6 : ℝ) by positivity)
  have hu := mul_lt_mul_of_pos_right hinv (by norm_num : (0 : ℝ)<(73/6)*(683/(8*21999)))
  have hn := mul_le_mul_of_nonneg_left hneg (by norm_num : (0 : ℝ)≤(1127/120)/126)
  have hid : r^4*((4/Real.pi)*((73/6 : ℝ)*(∫ x in (0 : ℝ)..1, bose 3 r x)-
      (1127/120 : ℝ)*(∫ x in (0 : ℝ)..1, bose 5 r x)))=
      (73/6 : ℝ)*Real.pi^3/60-(1127/120 : ℝ)/126*(Real.pi^5/r^2)-
      (4/Real.pi)*(73/6 : ℝ)*(r^4*(∫ x : ℝ in Ioi 1, bose 3 r x))+
      (4/Real.pi)*(1127/120 : ℝ)*r^4*(∫ x : ℝ in Ioi 1, bose 5 r x) := by
    rw [← h3,← h5]
    field_simp
    <;> ring
  rw [hid]
  have hpos : 0≤(4/Real.pi)*(1127/120 : ℝ)*r^4*(∫ x : ℝ in Ioi 1, bose 5 r x) := by positivity
  nlinarith only [hp3,ht,hu,hn,hpos]

theorem square_moment_lower {r : ℝ} (hr : 5≤r) :
    (20 : ℝ)<r^4*((4/Real.pi)*(40*(∫ x in (0 : ℝ)..1, bose 3 r x)+
      (29/5 : ℝ)*(∫ x in (0 : ℝ)..1, bose 5 r x)-11*(∫ x in (0 : ℝ)..1, bose 7 r x))) := by
  have hr0 : 0 < r := by linarith
  have h3 := intervalIntegral.integral_Ioi_sub_Ioi (bose_three_integrable hr0) (by norm_num : (0 : ℝ)≤1)
  have h5 := intervalIntegral.integral_Ioi_sub_Ioi (bose_five_integrable hr0) (by norm_num : (0 : ℝ)≤1)
  have h7 := intervalIntegral.integral_Ioi_sub_Ioi (bose_seven_integrable hr0) (by norm_num : (0 : ℝ)≤1)
  rw [integral_bose_three hr0] at h3
  rw [integral_bose_five hr0] at h5
  rw [integral_bose_seven hr0] at h7
  have ht3 := cubic_tail hr
  have ht5 := fifth_tail hr
  have ht7 : 0≤∫ x : ℝ in Ioi 1, bose 7 r x := by
    apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact bose_nonneg 7 hr0.le (by have hx' : (1 : ℝ)<x := hx; linarith)
  have hp3 : (157/50 : ℝ)^3<Real.pi^3 :=
    pow_lt_pow_left₀ (by linarith [Real.pi_gt_d2]) (by norm_num) (by decide)
  have hpi2 : Real.pi^2<10 := by nlinarith [Real.pi_lt_d2,Real.pi_pos]
  have hr2 : (25 : ℝ)≤r^2 := by nlinarith
  have hc : 0≤(29/2520 : ℝ)*r^2-(11/480 : ℝ)*Real.pi^2 := by nlinarith only [hr2,hpi2]
  have hextra : 0≤(29/5 : ℝ)*Real.pi^6/(504*r^2)-11*Real.pi^8/(480*r^4) := by
    have he : (29/5 : ℝ)*Real.pi^6/(504*r^2)-11*Real.pi^8/(480*r^4)=
        (Real.pi^6/r^4)*((29/2520 : ℝ)*r^2-(11/480 : ℝ)*Real.pi^2) := by
      field_simp
      <;> ring
    rw [he]
    exact mul_nonneg (by positivity) hc
  let K : ℝ := 40*(683/(8*21999))+(29/5)*(4433/(40*21999))
  have hK : 0 < K := by norm_num [K]
  have ht : 40*(r^4*(∫ x : ℝ in Ioi 1, bose 3 r x))+
      (29/5)*(r^4*(∫ x : ℝ in Ioi 1, bose 5 r x))<K := by dsimp [K]; linarith
  have ht' := mul_lt_mul_of_pos_left ht (show 0 < 4/Real.pi by positivity)
  have hinv : 4/Real.pi<4/3 := by
    rw [div_lt_div_iff₀ Real.pi_pos (by norm_num : (0 : ℝ)<3)]
    nlinarith [Real.pi_gt_three]
  have hu := mul_lt_mul_of_pos_right hinv hK
  have hplus := mul_nonneg (show 0≤4/Real.pi by positivity) hextra
  have hpos : 0≤(4/Real.pi)*11*r^4*(∫ x : ℝ in Ioi 1, bose 7 r x) := by positivity
  have hid : r^4*((4/Real.pi)*(40*(∫ x in (0 : ℝ)..1, bose 3 r x)+
      (29/5 : ℝ)*(∫ x in (0 : ℝ)..1, bose 5 r x)-11*(∫ x in (0 : ℝ)..1, bose 7 r x)))=
      40*Real.pi^3/60+(4/Real.pi)*((29/5 : ℝ)*Real.pi^6/(504*r^2)-11*Real.pi^8/(480*r^4))-
      (4/Real.pi)*(40*(r^4*(∫ x : ℝ in Ioi 1, bose 3 r x))+
        (29/5)*(r^4*(∫ x : ℝ in Ioi 1, bose 5 r x)))+
      (4/Real.pi)*11*r^4*(∫ x : ℝ in Ioi 1, bose 7 r x) := by
    rw [← h3,← h5,← h7]
    field_simp
    <;> ring
  rw [hid]
  dsimp only [K] at hu ht'
  nlinarith only [hp3,ht',hu,hplus,hpos]

end
end SpanningTreeIsoperimetry.BoundaryShortMoments
