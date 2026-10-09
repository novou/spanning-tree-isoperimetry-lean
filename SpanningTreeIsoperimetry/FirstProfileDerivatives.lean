import SpanningTreeIsoperimetry.FirstProfileModular
import SpanningTreeIsoperimetry.CoupledRectangleError
import Mathlib.Analysis.Calculus.SmoothSeries

/-! Explicit first and second derivatives of the actual first rectangular
profile. All differentiated series are locally uniformly summable. -/
namespace SpanningTreeIsoperimetry.FirstProfileDerivatives
open RectangularRemainder RectangleProfileContinuity CoupledRectangleError Filter Set
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def frequency (n : ℕ) : ℝ := 2*Real.pi*((n : ℝ)+1)
def decay (n : ℕ) (u : ℝ) : ℝ := Real.exp (-frequency n*u)
def firstMode (n : ℕ) (u : ℝ) : ℝ := frequency n*decay n u/(1-decay n u)
def secondMode (n : ℕ) (u : ℝ) : ℝ := -(frequency n)^2*decay n u/(1-decay n u)^2

theorem frequency_ge_one (n : ℕ) : 1≤frequency n := by
  unfold frequency
  nlinarith [Real.pi_gt_three,Nat.cast_nonneg (α := ℝ) n,
    mul_nonneg Real.pi_pos.le (Nat.cast_nonneg (α := ℝ) n)]

theorem decay_pos (n : ℕ) (u : ℝ) : 0<decay n u := Real.exp_pos _
theorem decay_lt_one {u : ℝ} (hu : 0<u) (n : ℕ) : decay n u<1 := by
  apply Real.exp_lt_one_iff.mpr
  have hp : 0<frequency n*u := mul_pos (by linarith [frequency_ge_one n]) hu
  linarith

theorem decay_pow (n : ℕ) (u : ℝ) : decay n u=Real.exp (-2*Real.pi*u)^(n+1) := by
  rw [← Real.exp_nat_mul]
  unfold decay frequency
  congr 1
  push_cast
  ring

theorem hasDerivAt_decay (n : ℕ) (u : ℝ) :
    HasDerivAt (decay n) (-frequency n*decay n u) u := by
  convert (((hasDerivAt_id u).const_mul (-frequency n)).exp) using 1 <;>
    (try funext v) <;> simp only [decay,id_eq,mul_one,neg_mul] <;> ring

theorem hasDerivAt_term {u : ℝ} (hu : 0<u) (n : ℕ) :
    HasDerivAt (fun v => term v n) (firstMode n u) u := by
  have h := ((hasDerivAt_decay n u).const_sub 1).log
    (ne_of_gt (sub_pos.mpr (decay_lt_one hu n)))
  convert h using 1
  · funext v
    unfold term decay frequency
    congr 2
    ring
  · unfold firstMode
    ring

theorem hasDerivAt_firstMode {u : ℝ} (hu : 0<u) (n : ℕ) :
    HasDerivAt (firstMode n) (secondMode n u) u := by
  have hne : 1-decay n u≠0 := ne_of_gt (sub_pos.mpr (decay_lt_one hu n))
  have h := ((hasDerivAt_decay n u).const_mul (frequency n)).div
    ((hasDerivAt_decay n u).const_sub 1) hne
  convert h using 1
  · rfl
  · unfold secondMode
    field_simp [hne]
    <;> ring

def majorant (a : ℝ) (n : ℕ) : ℝ :=
  (frequency n)^2*Real.exp (-2*Real.pi*a)^(n+1)/(1-Real.exp (-2*Real.pi*a))^2

theorem majorant_summable {a : ℝ} (ha : 0<a) : Summable (majorant a) := by
  let q := Real.exp (-2*Real.pi*a)
  have hq0 : 0<q := Real.exp_pos _
  have hq1 : q<1 := by rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have h := geometricMoment_summable 2 (show |q|<1 by rwa [abs_of_pos hq0])
  have hs : Summable (fun n : ℕ => ((n : ℝ)+1)^2*q^(n+1)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr h
  apply (hs.mul_left (4*Real.pi^2/(1-q)^2)).congr
  intro n
  dsimp only [majorant,frequency,q]
  ring

theorem secondMode_nonpos (n : ℕ) (u : ℝ) : secondMode n u≤0 := by
  have h : 0≤(frequency n)^2*decay n u/(1-decay n u)^2 := by
    have hp := decay_pos n u
    positivity
  simpa only [secondMode,neg_mul,neg_div] using neg_nonpos.mpr h

theorem mode_norm_bounds {a u : ℝ} (ha : 0<a) (hau : a≤u) (n : ℕ) :
    ‖firstMode n u‖≤majorant a n ∧ ‖secondMode n u‖≤majorant a n := by
  let q := Real.exp (-2*Real.pi*a)
  have hq0 : 0<q := Real.exp_pos _
  have hq1 : q<1 := by rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have hb : 1≤frequency n := frequency_ge_one n
  have hb0 : 0<frequency n := by linarith
  have he0 := decay_pos n u
  have he1 := decay_lt_one (ha.trans_le hau) n
  have hpowq : q^(n+1)≤q := by
    calc
      q^(n+1)=q^n*q := pow_succ _ _
      _≤1*q := mul_le_mul_of_nonneg_right (pow_le_one₀ hq0.le hq1.le) hq0.le
      _=q := one_mul q
  have he : decay n u≤q^(n+1) := by
    rw [← decay_pow]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hau (by linarith)
  have hd : 0<1-q := sub_pos.mpr hq1
  have hden : 1-q≤1-decay n u := by linarith [he.trans hpowq]
  have hpos : 0≤firstMode n u := by unfold firstMode; positivity
  have hneg := secondMode_nonpos n u
  rw [Real.norm_eq_abs,abs_of_nonneg hpos,Real.norm_eq_abs,abs_of_nonpos hneg]
  constructor
  · calc
      firstMode n u≤frequency n*q^(n+1)/(1-q) := by
        unfold firstMode
        exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left he hb0.le) hd hden
      _≤(frequency n)^2*q^(n+1)/(1-q)^2 := by
        apply (div_le_div_iff₀ hd (sq_pos_of_pos hd)).mpr
        have hn : 0≤frequency n*q^(n+1) := by positivity
        have hfactor : (1-q)^2≤frequency n*(1-q) := by
          nlinarith [mul_nonneg (show 0≤frequency n-1 by linarith) hd.le]
        nlinarith [mul_le_mul_of_nonneg_left hfactor hn]
      _=majorant a n := rfl
  · have h : (frequency n)^2*decay n u/(1-decay n u)^2≤
        (frequency n)^2*q^(n+1)/(1-q)^2 := by
      exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left he (sq_nonneg _))
        (sq_pos_of_pos hd) (pow_le_pow_left₀ hd.le hden 2)
    simpa only [secondMode,neg_div,neg_mul,neg_neg,majorant,q] using h

theorem firstMode_summable {u : ℝ} (hu : 0<u) : Summable (fun n => firstMode n u) :=
  Summable.of_norm_bounded (majorant_summable hu) (fun n => (mode_norm_bounds hu le_rfl n).1)

theorem secondMode_summable {u : ℝ} (hu : 0<u) : Summable (fun n => secondMode n u) :=
  Summable.of_norm_bounded (majorant_summable hu) (fun n => (mode_norm_bounds hu le_rfl n).2)

def firstSum (u : ℝ) : ℝ := ∑' n : ℕ, firstMode n u
def secondSum (u : ℝ) : ℝ := ∑' n : ℕ, secondMode n u

theorem hasDerivAt_linearResidual {u : ℝ} (hu : 0<u) :
    HasDerivAt linearResidual (firstSum u) u := by
  exact hasDerivAt_tsum_of_isPreconnected (majorant_summable (half_pos hu))
    isOpen_Ioi (convex_Ioi (u/2)).isPreconnected
    (fun n v hv => hasDerivAt_term (lt_trans (half_pos hu) hv) n)
    (fun n v hv => (mode_norm_bounds (half_pos hu) hv.le n).1)
    (show u∈Ioi (u/2) by change u/2<u; linarith) (linearResidual_summable hu)
    (show u∈Ioi (u/2) by change u/2<u; linarith)

theorem hasDerivAt_firstSum {u : ℝ} (hu : 0<u) :
    HasDerivAt firstSum (secondSum u) u := by
  exact hasDerivAt_tsum_of_isPreconnected (majorant_summable (half_pos hu))
    isOpen_Ioi (convex_Ioi (u/2)).isPreconnected
    (fun n v hv => hasDerivAt_firstMode (lt_trans (half_pos hu) hv) n)
    (fun n v hv => (mode_norm_bounds (half_pos hu) hv.le n).2)
    (show u∈Ioi (u/2) by change u/2<u; linarith) (firstMode_summable hu)
    (show u∈Ioi (u/2) by change u/2<u; linarith)

def Jfirst (u : ℝ) : ℝ := -Real.pi/12+firstSum u+(1/4)*u⁻¹
def Jsecond (u : ℝ) : ℝ := secondSum u-1/(4*u^2)

theorem hasDerivAt_J_explicit {u : ℝ} (hu : 0<u) : HasDerivAt J (Jfirst u) u := by
  have h := (((hasDerivAt_const u ((5/4)*Real.log 2)).sub
    (((hasDerivAt_id u).const_mul Real.pi).div_const 12)).add
      (hasDerivAt_linearResidual hu)).add ((Real.hasDerivAt_log hu.ne').const_mul (1/4))
  convert h using 1 <;> (try funext v) <;> simp only [J,B,Jfirst,id_eq,Pi.add_apply,Pi.sub_apply] <;> ring

theorem hasDerivAt_Jfirst {u : ℝ} (hu : 0<u) : HasDerivAt Jfirst (Jsecond u) u := by
  have h := ((hasDerivAt_firstSum hu).const_add (-Real.pi/12)).add
    ((hasDerivAt_inv hu.ne').const_mul (1/4))
  convert h using 1 <;> (try funext v) <;> simp only [Jfirst,Jsecond,Pi.add_apply,Pi.sub_apply,div_eq_mul_inv,mul_inv_rev] <;> ring

theorem iteratedDeriv_J_two {u : ℝ} (hu : 0<u) : iteratedDeriv 2 J u=Jsecond u := by
  have he : deriv J=ᶠ[𝓝 u] Jfirst := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    exact (hasDerivAt_J_explicit hv).deriv
  have hd := (hasDerivAt_Jfirst hu).congr_of_eventuallyEq he
  rw [iteratedDeriv_succ,iteratedDeriv_succ,iteratedDeriv_zero]
  exact hd.deriv

def curvatureSeries (u : ℝ) : ℝ := ∑' n : ℕ,
  ((n : ℝ)+1)^2*Real.exp (-2*Real.pi*u*((n : ℝ)+1))/
    (1-Real.exp (-2*Real.pi*u*((n : ℝ)+1)))^2

theorem secondSum_eq (u : ℝ) : secondSum u= -4*Real.pi^2*curvatureSeries u := by
  rw [curvatureSeries,← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold secondMode decay frequency
  have he : -(2*Real.pi*((n : ℝ)+1))*u= -2*Real.pi*u*((n : ℝ)+1) := by ring
  rw [he]
  ring

/-- Appendix A's explicit second derivative; the positive index j is n+1. -/
theorem second_derivative_formula {u : ℝ} (hu : 0<u) :
    iteratedDeriv 2 J u= -1/(4*u^2)-4*Real.pi^2*curvatureSeries u := by
  rw [iteratedDeriv_J_two hu,Jsecond,secondSum_eq]
  ring

theorem majorant_tsum {a : ℝ} (ha : 0<a) :
    (∑' n : ℕ,majorant a n)=4*Real.pi^2*Real.exp (-2*Real.pi*a)*
      (1+Real.exp (-2*Real.pi*a))/(1-Real.exp (-2*Real.pi*a))^5 := by
  let q := Real.exp (-2*Real.pi*a)
  have hq0 : 0<q := Real.exp_pos _
  have hq1 : q<1 := by rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have hq : |q|<1 := by rwa [abs_of_pos hq0]
  have hs := geometricMoment_summable 2 hq
  have hshift : (∑' n : ℕ,((n : ℝ)+1)^2*q^(n+1))=moment2 q := by
    have h := hs.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one,Nat.cast_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,
      not_false_eq_true,pow_zero,mul_one,zero_mul,zero_add,Nat.cast_add,Nat.cast_one] at h
    exact h.trans (geometricMoment_two hq)
  calc
    (∑' n : ℕ,majorant a n)=4*Real.pi^2/(1-q)^2*
        (∑' n : ℕ,((n : ℝ)+1)^2*q^(n+1)) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      unfold majorant frequency q
      ring
    _=4*Real.pi^2*q*(1+q)/(1-q)^5 := by
      rw [hshift,moment2]
      field_simp [ne_of_gt (sub_pos.mpr hq1)]
      <;> ring
    _=_ := rfl

theorem secondSum_nonpos (u : ℝ) : secondSum u≤0 := by
  apply tsum_nonpos
  intro n
  exact secondMode_nonpos n u

theorem negative_secondSum_le {u : ℝ} (hu : 1≤u) :
    -secondSum u≤40*((1/500 : ℝ)*(1+1/500)/(1-1/500)^5) := by
  have hu0 : 0<u := by linarith
  have h := ((secondMode_summable hu0).neg).tsum_le_tsum
    (fun n => by
      have hm := (mode_norm_bounds (by norm_num : (0 : ℝ)<1) hu n).2
      have hn := secondMode_nonpos n u
      simpa only [Real.norm_eq_abs,abs_of_nonpos hn] using hm)
    (majorant_summable (by norm_num : (0 : ℝ)<1))
  rw [tsum_neg,majorant_tsum (by norm_num : (0 : ℝ)<1)] at h
  let q := Real.exp (-2*Real.pi)
  have hq0 : 0<q := Real.exp_pos _
  have hq : q≤(1 : ℝ)/500 := by
    dsimp [q]
    rw [show -2*Real.pi= -(2*Real.pi) by ring,Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<500)
      (show (500 : ℝ)≤Real.exp (2*Real.pi) by linarith [exp_two_pi_gt_fivehundredthirty])
  have hpi2 : Real.pi^2≤10 := by nlinarith [mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d2]
  have hden : 0<1-q := by linarith
  have hbound : 4*Real.pi^2*q*(1+q)/(1-q)^5≤
      40*((1/500 : ℝ)*(1+1/500)/(1-1/500)^5) := by
    calc
      _≤(40 : ℝ)*(1/500)*(1+1/500)/(1-1/500)^5 := by gcongr <;> linarith
      _=_ := by ring
  exact h.trans (by simpa only [mul_one] using hbound)

/-- The exact global curvature bound printed in Appendix A. -/
theorem second_derivative_bounds {u : ℝ} (hu : 1≤u) :
    0< -(iteratedDeriv 2 J u) ∧ -(iteratedDeriv 2 J u)<(1 : ℝ)/3 := by
  have hu0 : 0<u := by linarith
  rw [iteratedDeriv_J_two hu0,Jsecond]
  have hs := secondSum_nonpos u
  have hb := negative_secondSum_le hu
  have hbase : 0<1/(4*u^2) := by positivity
  have hbase' : 1/(4*u^2)≤(1 : ℝ)/4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<4*u^2)).mpr
    nlinarith
  constructor
  · linarith
  · have hn : (1/4 : ℝ)+40*((1/500)*(1+1/500)/(1-1/500)^5)<1/3 := by norm_num
    linarith only [hb,hbase',hn]

theorem deriv_K_one : deriv K 1=0 := by
  have hJ := FirstProfileModular.hasDerivAt_J (by norm_num : (0 : ℝ)<1)
  rw [FirstProfileModular.deriv_J_one] at hJ
  have hlog1 := (((hasDerivAt_id (1 : ℝ)).const_add 1).log (by norm_num)).const_mul (1/2)
  have hlog2 := (Real.hasDerivAt_log (by norm_num : (1 : ℝ)≠0)).const_mul (1/4)
  have h := (hJ.add hlog1).sub hlog2
  have he : HasDerivAt K 0 1 := by
    convert h using 1
    · funext v
      simp only [K,J,Pi.add_apply,Pi.sub_apply,id_eq]
      ring
    · norm_num
  exact he.deriv

end
end SpanningTreeIsoperimetry.FirstProfileDerivatives
