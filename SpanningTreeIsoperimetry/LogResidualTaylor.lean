module

public import SpanningTreeIsoperimetry.RectangleResidualBounds
public import Mathlib.Analysis.Calculus.Taylor

@[expose] public section

set_option backward.privateInPublic true

/-! Second-order control of the actual logarithmic lattice modes. -/
namespace SpanningTreeIsoperimetry.LogResidualTaylor

open Set Filter RectangularRemainder RectangleResidualBounds AngularKernelTaylor
open scoped Topology Interval
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def logPrime (s x : ℝ) : ℝ := 2*s/(Real.exp (2*s*x)-1)
def logSecond (s x : ℝ) : ℝ := -4*s^2*Real.exp (2*s*x)/(Real.exp (2*s*x)-1)^2

theorem contDiffAt_logTerm {s x : ℝ} (hs : 0<s) (hx : 0<x) :
    ContDiffAt ℝ ⊤ (logTerm s) x := by
  unfold logTerm
  apply ContDiffAt.log
  · fun_prop
  · exact (logTerm_arg_pos hs hx).ne'

theorem hasDerivAt_logPrime {s x : ℝ} (hs : 0<s) (hx : 0<x) :
    HasDerivAt (logPrime s) (logSecond s x) x := by
  have he := ((hasDerivAt_id x).const_mul (2*s)).exp
  have hd := he.sub_const 1
  have hden : Real.exp (2*s*x)-1≠0 :=
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))).ne'
  have h := (hasDerivAt_const x (2*s)).fun_div hd hden
  unfold logPrime logSecond
  convert h using 1 <;> (try rfl) <;> simp only [id_eq,mul_one] <;> ring

theorem hasDerivAt_deriv_logTerm {s x : ℝ} (hs : 0<s) (hx : 0<x) :
    HasDerivAt (deriv (logTerm s)) (logSecond s x) x := by
  have he : deriv (logTerm s)=ᶠ[𝓝 x] logPrime s := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (hasDerivAt_logTerm hs hy).deriv
  exact (hasDerivAt_logPrime hs hx).congr_of_eventuallyEq he

theorem iteratedDeriv_logTerm_two {s x : ℝ} (hs : 0<s) (hx : 0<x) :
    iteratedDeriv 2 (logTerm s) x=logSecond s x := by
  rw [iteratedDeriv_succ,iteratedDeriv_succ,iteratedDeriv_zero]
  exact (hasDerivAt_deriv_logTerm hs hx).deriv

theorem logSecond_abs {s x : ℝ} (hs : 0<s) (hx : 0<x) :
    |logSecond s x|=4*s^2*Real.exp (-2*s*x)/(1-Real.exp (-2*s*x))^2 := by
  have he := Real.exp_pos (2*s*x)
  have hd : 0<Real.exp (2*s*x)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  have hn : logSecond s x≤0 := by
    unfold logSecond
    apply div_nonpos_of_nonpos_of_nonneg
    · have hp : 0≤4*s^2*Real.exp (2*s*x) := by positivity
      nlinarith
    · exact sq_nonneg _
  rw [abs_of_nonpos hn,logSecond,show -2*s*x= -(2*s*x) by ring,Real.exp_neg]
  field_simp [he.ne',hd.ne'] <;> ring

theorem logSecond_abs_bound {s x c : ℝ} (hs : 0<s) (hx : 0<x) (hxc : x≤c) :
    |logSecond s c|≤4*s^2*Real.exp (-2*s*x)/(1-Real.exp (-2*s*x))^2 := by
  have hc : 0<c := hx.trans_le hxc
  rw [logSecond_abs hs hc]
  have hq : Real.exp (-2*s*c)≤Real.exp (-2*s*x) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hxc (show 0≤2*s by positivity)
    nlinarith
  have hqx : Real.exp (-2*s*x)<1 := by rw [Real.exp_lt_one_iff]; nlinarith
  have hqc : Real.exp (-2*s*c)<1 := by rw [Real.exp_lt_one_iff]; nlinarith
  gcongr

/-- The quadratic prefactor is absorbed by exponential decay past u=1. -/
theorem scaled_exponential_square_antitone {c : ℝ} (hc : 2≤c) :
    AntitoneOn (fun u : ℝ => u^2*Real.exp (-c*u)) (Ici 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
  · fun_prop
  · intro x hx
    fun_prop
  · intro x hx
    have hx' : 1<x := by simpa only [interior_Ici,mem_Ioi] using hx
    have hd : HasDerivAt (fun u : ℝ => u^2*Real.exp (-c*u))
        (x*Real.exp (-c*x)*(2-c*x)) x := by
      convert ((hasDerivAt_id x).fun_pow 2).fun_mul (((hasDerivAt_id x).const_mul (-c)).exp) using 1 <;>
        simp only [id_eq,mul_one,Nat.cast_ofNat,pow_one] <;> ring
    rw [hd.deriv]
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    nlinarith

/-- The full second-derivative mode factor decreases with aspect. -/
theorem scaled_curvature_antitone {c : ℝ} (hc : 2≤c) :
    AntitoneOn (fun u : ℝ => u^2*Real.exp (-c*u)/(1-Real.exp (-c*u))^2) (Ici 1) := by
  intro u hu v hv huv
  have hc0 : 0<c := by linarith
  have hu0 : 0<u := by have h : 1≤u := hu; linarith
  have hv0 : 0<v := hu0.trans_le huv
  have hqu : Real.exp (-c*u)<1 := by rw [Real.exp_lt_one_iff]; nlinarith
  have hqv : Real.exp (-c*v)<1 := by rw [Real.exp_lt_one_iff]; nlinarith
  have hq : Real.exp (-c*v)≤Real.exp (-c*u) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left huv (by linarith)
  have hnum := scaled_exponential_square_antitone hc hu hv huv
  calc
    _≤(u^2*Real.exp (-c*u))/(1-Real.exp (-c*v))^2 :=
      div_le_div_of_nonneg_right hnum (sq_nonneg _)
    _≤_ := by
      apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos (by linarith))
      gcongr

private theorem log_taylor_one {s x y : ℝ} (hs : 0<s) (hx : 0<x) (hxy : x<y) :
    taylorWithinEval (logTerm s) 1 (uIcc y x) y x=
      logTerm s y+(x-y)*logPrime s y := by
  have hy : 0<y := hx.trans hxy
  have hd (n : ℕ) : iteratedDerivWithin n (logTerm s) (uIcc y x) y=
      iteratedDeriv n (logTerm s) y :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hxy.ne')
      ((contDiffAt_logTerm hs hy).of_le le_top) (by simp)
  rw [taylor_within_apply]
  norm_num [Finset.sum_range_succ,hd,iteratedDeriv_zero,(hasDerivAt_logTerm hs hy).deriv,
    logPrime,smul_eq_mul]

/-- The actual logarithmic mode has a quadratic Taylor remainder controlled
by the curvature at the smaller positive endpoint. -/
theorem logTerm_second_remainder {s x y : ℝ} (hs : 0<s) (hx : 0<x) (hxy : x≤y) :
    |logTerm s x-logTerm s y+logPrime s y*(y-x)|≤
      (2*s^2*Real.exp (-2*s*x)/(1-Real.exp (-2*s*x))^2)*(y-x)^2 := by
  by_cases heq : x=y
  · simp [heq]
  · have hxy' : x<y := lt_of_le_of_ne hxy heq
    have hc : ContDiffOn ℝ 2 (logTerm s) (uIcc y x) := by
      intro z hz
      have hz' : z∈Icc x y := by simpa only [uIcc_of_ge hxy] using hz
      exact ((contDiffAt_logTerm hs (hx.trans_le hz'.1)).of_le le_top).contDiffWithinAt
    obtain ⟨c,hcxy,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hxy'.ne' hc
    have hc' : c∈Ioo x y := by simpa only [uIoo_of_gt hxy'] using hcxy
    rw [log_taylor_one hs hx hxy',iteratedDeriv_logTerm_two hs (hx.trans hc'.1)] at he
    norm_num only [Nat.factorial] at he
    have hb := logSecond_abs_bound hs hx hc'.1.le
    have hq : 0<1-Real.exp (-2*s*x) := logTerm_arg_pos hs hx
    calc
      _=|logSecond s c*(x-y)^2/2| := by congr 1; linarith
      _=|logSecond s c| * (y-x)^2/2 := by
        rw [abs_div,abs_mul,abs_of_nonneg (sq_nonneg (x-y)),
          abs_of_pos (by norm_num : (0 : ℝ)<2)]
        ring
      _≤(4*s^2*Real.exp (-2*s*x)/(1-Real.exp (-2*s*x))^2)*(y-x)^2/2 := by gcongr
      _=_ := by field_simp [hq.ne'] <;> ring

/-- The cubic lattice correction has the explicit fifth/sixth-order
logarithmic error needed by the rectangular second profile. -/
theorem gamma_log_next_error {s θ : ℝ} (hs : 0<s) (hθ : θ∈Ioc 0 Real.pi) :
    |logTerm s (gamma θ)-logTerm s θ+s*θ^3/(6*(Real.exp (2*s*θ)-1))|≤
      s*θ^5/(48*(Real.exp (2*s*θ)-1))+
        (s^2*θ^6/72)*Real.exp (-2*s*gamma θ)/(1-Real.exp (-2*s*gamma θ))^2 := by
  have hγ : 0<gamma θ := by
    have h := gamma_strictMonoOn ⟨le_rfl,Real.pi_pos.le⟩ ⟨hθ.1.le,hθ.2⟩ hθ.1
    simpa only [gamma_zero] using h
  have hθ0 := hθ.1
  have hδ := gamma_cubic_defect ⟨hθ.1.le,hθ.2⟩
  have hδ0 := hδ.1
  have hδ3 := hδ.2
  have hδ5 := gamma_fifth_defect ⟨hθ.1.le,hθ.2⟩
  have hd : 0<Real.exp (2*s*θ)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  have hq : 0<1-Real.exp (-2*s*gamma θ) := logTerm_arg_pos hs hγ
  have hp : 0≤logPrime s θ := by unfold logPrime; positivity
  have hbase := logTerm_second_remainder hs hγ (gamma_le_theta ⟨hθ.1.le,hθ.2⟩)
  have hsq : (θ-gamma θ)^2≤(θ^3/12)^2 := by gcongr
  have hquad : |logTerm s (gamma θ)-logTerm s θ+logPrime s θ*(θ-gamma θ)|≤
      (s^2*θ^6/72)*Real.exp (-2*s*gamma θ)/(1-Real.exp (-2*s*gamma θ))^2 := by
    calc
      _≤(2*s^2*Real.exp (-2*s*gamma θ)/(1-Real.exp (-2*s*gamma θ))^2)*(θ-gamma θ)^2 := hbase
      _≤(2*s^2*Real.exp (-2*s*gamma θ)/(1-Real.exp (-2*s*gamma θ))^2)*(θ^3/12)^2 := by gcongr
      _=_ := by field_simp [hq.ne'] <;> ring
  have hlin : |logPrime s θ*(θ^3/12-(θ-gamma θ))|≤s*θ^5/(48*(Real.exp (2*s*θ)-1)) := by
    rw [abs_of_nonneg (mul_nonneg hp hδ5.1)]
    calc
      _≤logPrime s θ*(θ^5/96) := mul_le_mul_of_nonneg_left hδ5.2 hp
      _=_ := by unfold logPrime; field_simp [hd.ne'] <;> ring
  calc
    _=|(logTerm s (gamma θ)-logTerm s θ+logPrime s θ*(θ-gamma θ))+
        logPrime s θ*(θ^3/12-(θ-gamma θ))| := by
      congr 1
      unfold logPrime
      field_simp [hd.ne'] <;> ring
    _≤|logTerm s (gamma θ)-logTerm s θ+logPrime s θ*(θ-gamma θ)|+
        |logPrime s θ*(θ^3/12-(θ-gamma θ))| := abs_add_le _ _
    _≤_ := by linarith

end
end SpanningTreeIsoperimetry.LogResidualTaylor
