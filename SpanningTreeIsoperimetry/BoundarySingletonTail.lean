module

public import SpanningTreeIsoperimetry.BoundaryBoseTail
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-! Scaling reduces every singleton cubic tail, for real r≥4, to a single
explicit tail at 5. No monotonicity assumption or integer induction is used. -/
namespace SpanningTreeIsoperimetry.BoundarySingletonTail
open MeasureTheory Set Filter BoundaryBoseMoments BoundaryBoseTail
open scoped BigOperators Topology
noncomputable section

theorem bose_nonneg (m : ℕ) {r x : ℝ} (hr : 0≤r) (hx : 0≤x) : 0≤bose m r x := by
  unfold bose
  have he := Real.one_le_exp_iff.mpr (show 0≤2*r*x by positivity)
  positivity

theorem bose_scale (m : ℕ) (r x : ℝ) : bose m 1 (r*x)=r^m*bose m r x := by
  unfold bose
  rw [mul_pow]
  congr 1 <;> ring

theorem integral_bose_scale (m : ℕ) {r : ℝ} (hr : 0 < r) (A : ℝ) :
    r^(m+1)*(∫ x : ℝ in Ioi A, bose m r x)=∫ x : ℝ in Ioi (r*A), bose m 1 x := by
  have h := integral_comp_mul_left_Ioi' (bose m 1) A hr
  simp_rw [bose_scale] at h
  rw [integral_const_mul] at h
  simpa only [smul_eq_mul,pow_succ,mul_assoc,mul_comm,mul_left_comm] using h

theorem exp_ten_gt : (22000 : ℝ)<Real.exp 10 := by
  have h := Real.sum_le_exp_of_nonneg (x := (10 : ℝ)) (by norm_num) 25
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  linarith

theorem scaled_cubic_tail_le {r : ℝ} (hr : 4≤r) :
    r^4*(∫ x : ℝ in Ioi (5/4), bose 3 r x)≤(683/8 : ℝ)/(Real.exp 10-1) := by
  rw [integral_bose_scale 3 (by linarith) (5/4)]
  have hmono : (∫ x : ℝ in Ioi (r*(5/4)), bose 3 1 x)≤∫ x : ℝ in Ioi 5, bose 3 1 x := by
    apply setIntegral_mono_set ((bose_three_integrable (by norm_num : (0 : ℝ)<1)).mono_set
      (Ioi_subset_Ioi (by norm_num : (0 : ℝ)≤5)))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      exact bose_nonneg 3 (by norm_num) (by have hx' : (5 : ℝ)<x := hx; linarith)
    · exact Filter.Eventually.of_forall (fun x hx => by simp only [mem_Ioi] at hx ⊢; nlinarith)
  have ht := integral_bose_tail_le 3 (r := 1) (A := 5) (by norm_num) (by norm_num)
  norm_num [tailPolynomial,Finset.sum_range_succ,Nat.factorial,Nat.choose] at ht
  exact hmono.trans ht

theorem scaled_cubic_tail_lt {r : ℝ} (hr : 4≤r) :
    r^4*(∫ x : ℝ in Ioi (5/4), bose 3 r x)<(683 : ℝ)/(8*21999) := by
  apply (scaled_cubic_tail_le hr).trans_lt
  have he : 0 < Real.exp 10-1 := by linarith [exp_ten_gt]
  rw [div_lt_div_iff₀ he (by norm_num : (0 : ℝ)<8*21999)]
  nlinarith [exp_ten_gt]

/-- A deliberately rational lower constant, stronger than needed after the
actual singleton Green value is inserted. -/
theorem truncated_cubic_lower {r : ℝ} (hr : 4≤r) :
    (50/99 : ℝ)<r^4*((4/Real.pi)*(∫ x in (0 : ℝ)..(5/4), bose 3 r x)) := by
  have hr0 : 0 < r := by linarith
  have he := intervalIntegral.integral_Ioi_sub_Ioi (bose_three_integrable hr0)
    (by norm_num : (0 : ℝ)≤5/4)
  rw [integral_bose_three hr0] at he
  have ht := scaled_cubic_tail_lt hr
  have hp : (157/50 : ℝ)<Real.pi := by linarith [Real.pi_gt_d2]
  have hp3 : (157/50 : ℝ)^3<Real.pi^3 := pow_lt_pow_left₀ hp (by norm_num) (by decide : 3≠0)
  have hinv : 4/Real.pi<4/3 := by
    rw [div_lt_div_iff₀ Real.pi_pos (by norm_num : (0 : ℝ)<3)]
    nlinarith [Real.pi_gt_three]
  have htail0 : 0≤r^4*(∫ x : ℝ in Ioi (5/4), bose 3 r x) := by
    apply mul_nonneg (by positivity)
    apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact bose_nonneg 3 hr0.le (by have hx' : (5/4 : ℝ)<x := hx; linarith)
  have hm := mul_lt_mul_of_pos_left ht (show 0 < 4/Real.pi by positivity)
  have hm' := mul_lt_mul_of_pos_right hinv (by norm_num : (0 : ℝ)<683/(8*21999))
  have hid : r^4*((4/Real.pi)*(∫ x in (0 : ℝ)..(5/4), bose 3 r x))=
      Real.pi^3/60-(4/Real.pi)*(r^4*(∫ x : ℝ in Ioi (5/4), bose 3 r x)) := by
    rw [← he]
    field_simp
    <;> ring
  rw [hid]
  nlinarith only [hp3,hm,hm']

end
end SpanningTreeIsoperimetry.BoundarySingletonTail
