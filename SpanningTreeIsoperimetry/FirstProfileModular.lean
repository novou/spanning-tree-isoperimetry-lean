import SpanningTreeIsoperimetry.RectangleProfileContinuity
import SpanningTreeIsoperimetry.SecondProfileModular
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! The actual first rectangle profile on the imaginary axis. The eta
product identifies its logarithmic series; the checked discriminant
transformation gives reciprocal symmetry and stationarity at the square. -/
namespace SpanningTreeIsoperimetry.FirstProfileModular
open RectangularRemainder SecondProfileModular ModularForm Filter
open scoped Topology BigOperators MatrixGroups
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

def etaNorm (u : ℝ) : ℝ := ‖ModularForm.eta ((u : ℂ)*Complex.I)‖

private theorem factor_pos {u : ℝ} (hu : 0<u) (n : ℕ) :
    0<1-Real.exp (-2*Real.pi*u*((n : ℝ)+1)) := by
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  have hh : 0<2*Real.pi*u*((n : ℝ)+1) := by positivity
  linarith

theorem eta_q_axis {u : ℝ} (hu : 0<u) (n : ℕ) :
    ModularForm.eta_q n ((u : ℂ)*Complex.I)=
      (Real.exp (-2*Real.pi*u*((n : ℝ)+1)) : ℂ) := by
  have he : Complex.exp (2*(Real.pi : ℂ)*Complex.I*((u : ℂ)*Complex.I))=
      (Real.exp (-2*Real.pi*u) : ℂ) := imaginaryAxis_q hu
  rw [ModularForm.eta_q_eq_pow,he,← Complex.ofReal_pow,← Real.exp_nat_mul]
  congr 2 <;> push_cast <;> ring

private theorem q24_axis (u : ℝ) :
    Function.Periodic.qParam 24 ((u : ℂ)*Complex.I)=(Real.exp (-Real.pi*u/12) : ℂ) := by
  unfold Function.Periodic.qParam
  rw [show ((24 : ℝ) : ℂ)=(24 : ℂ) by norm_num [Complex.ext_iff]]
  have he : 2*(Real.pi : ℂ)*Complex.I*((u : ℂ)*Complex.I)/24=((-Real.pi*u/12 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [he,← Complex.ofReal_exp]

theorem etaNorm_eq_exp {u : ℝ} (hu : 0<u) :
    etaNorm u=Real.exp (-Real.pi*u/12+linearResidual u) := by
  have hz : ((u : ℂ)*Complex.I)∈UpperHalfPlane.upperHalfPlaneSet := by simpa using hu
  have hm : Multipliable (fun n => 1-ModularForm.eta_q n ((u : ℂ)*Complex.I)) :=
    ModularForm.multipliableLocallyUniformlyOn_eta.multipliable hz
  have hn (n : ℕ) : ‖1-ModularForm.eta_q n ((u : ℂ)*Complex.I)‖=
      1-Real.exp (-2*Real.pi*u*((n : ℝ)+1)) := by
    rw [eta_q_axis hu,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (factor_pos hu n)]
  calc
    etaNorm u=Real.exp (-Real.pi*u/12)*
        ∏' n : ℕ, (1-Real.exp (-2*Real.pi*u*((n : ℝ)+1))) := by
      unfold etaNorm ModularForm.eta
      rw [norm_mul,q24_axis,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),hm.norm_tprod]
      congr 1
      exact tprod_congr hn
    _ = Real.exp (-Real.pi*u/12)*Real.exp (linearResidual u) := by
      congr 1
      exact (Real.rexp_tsum_eq_tprod (factor_pos hu) (linearResidual_summable hu)).symm
    _ = _ := (Real.exp_add _ _).symm

theorem J_eq_log_etaNorm {u : ℝ} (hu : 0<u) :
    J u=(5/4)*Real.log 2+Real.log (etaNorm u)+(1/4)*Real.log u := by
  rw [etaNorm_eq_exp hu,Real.log_exp]
  unfold J B
  ring

theorem J_inv {u : ℝ} (hu : 0<u) : J (u⁻¹)=J u := by
  have hh := congrFun ModularForm.discriminant_S_invariant (imaginaryAxis hu)
  rw [ModularForm.SL_slash_apply,S_imaginaryAxis hu,ModularGroup.denom_S] at hh
  have hI : Complex.I^12=1 := by
    rw [show 12=4*3 by norm_num,pow_mul,Complex.I_pow_four,one_pow]
  have hp : (imaginaryAxis hu : ℂ)^(-(12 : ℤ))=(((u^12)⁻¹ : ℝ) : ℂ) := by
    change ((u : ℂ)*Complex.I)^(-(12 : ℤ))=_
    norm_num [zpow_neg,mul_pow,hI]
  rw [hp] at hh
  have hn := congrArg norm hh
  change ‖(ModularForm.eta (((u⁻¹ : ℝ) : ℂ)*Complex.I))^24 * (((u^12)⁻¹ : ℝ) : ℂ)‖=
    ‖(ModularForm.eta ((u : ℂ)*Complex.I))^24‖ at hn
  rw [norm_mul,norm_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (show 0<(u^12)⁻¹ by positivity)] at hn
  change (etaNorm (u⁻¹))^24*(u^12)⁻¹=(etaNorm u)^24 at hn
  rw [etaNorm_eq_exp (inv_pos.mpr hu),etaNorm_eq_exp hu] at hn
  have hl := congrArg Real.log hn
  rw [Real.log_mul (pow_ne_zero 24 (Real.exp_ne_zero _)) (inv_ne_zero (pow_ne_zero 12 hu.ne'))] at hl
  simp only [Real.log_pow,Real.log_exp,Real.log_inv] at hl
  unfold J B
  rw [Real.log_inv]
  norm_num at hl
  linarith

theorem K_inv {u : ℝ} (hu : 0<u) : K (u⁻¹)=K u := by
  have hh := J_inv hu
  unfold J B at hh
  rw [Real.log_inv] at hh
  unfold K B
  rw [show 1+u⁻¹=(1+u)/u by field_simp [hu.ne'] <;> ring,
    Real.log_div (x := 1+u) (y := u) (by positivity) hu.ne']
  linarith

theorem contDiffAt_J {u : ℝ} (hu : 0<u) : ContDiffAt ℝ 2 J u := by
  have hz : ((u : ℂ)*Complex.I)∈UpperHalfPlane.upperHalfPlaneSet := by simpa using hu
  have hd : DifferentiableOn ℂ ModularForm.eta UpperHalfPlane.upperHalfPlaneSet :=
    fun z hz => (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz).differentiableWithinAt
  have ha : AnalyticAt ℂ ModularForm.eta ((u : ℂ)*Complex.I) :=
    hd.analyticAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)
  have har : AnalyticAt ℝ ModularForm.eta ((u : ℂ)*Complex.I) := ha.restrictScalars
  have heta : ContDiffAt ℝ 2 ModularForm.eta ((u : ℂ)*Complex.I) := har.contDiffAt
  have hreal : ContDiffAt ℝ 2 (fun v : ℝ => (v : ℂ)) u := Complex.ofRealCLM.contDiff.contDiffAt
  have haxis : ContDiffAt ℝ 2 (fun v : ℝ => (v : ℂ)*Complex.I) u :=
    hreal.mul (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ => Complex.I) u)
  have hc : ContDiffAt ℝ 2 (fun v : ℝ => ModularForm.eta ((v : ℂ)*Complex.I)) u :=
    heta.fun_comp u haxis
  have hne := ModularForm.eta_ne_zero hz
  have hnorm : ContDiffAt ℝ 2 etaNorm u := hc.norm ℂ hne
  have hlog := hnorm.log (norm_ne_zero_iff.mpr hne)
  have huLog : ContDiffAt ℝ 2 Real.log u := contDiffAt_id.log hu.ne'
  have hquarter : ContDiffAt ℝ 2 (fun v : ℝ => (1/4)*Real.log v) u :=
    (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ => (1/4 : ℝ)) u).mul huLog
  have hconstant : ContDiffAt ℝ 2 (fun _ : ℝ => (5/4)*Real.log 2) u := contDiffAt_const
  have hformula : ContDiffAt ℝ 2
      (fun v => (5/4)*Real.log 2+Real.log (etaNorm v)+(1/4)*Real.log v) u :=
    (hconstant.add hlog).add hquarter
  apply hformula.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hu] with v hv
  exact J_eq_log_etaNorm hv

theorem hasDerivAt_J {u : ℝ} (hu : 0<u) : HasDerivAt J (deriv J u) u :=
  ((contDiffAt_J hu).differentiableAt (by norm_num)).hasDerivAt

theorem deriv_J_one : deriv J 1=0 := by
  have hd := hasDerivAt_J (by norm_num : (0 : ℝ)<1)
  have hd' : HasDerivAt J (deriv J 1) ((1 : ℝ)⁻¹) := by simpa only [inv_one] using hd
  have hi : HasDerivAt (fun u : ℝ => u⁻¹) (-1) 1 := by
    simpa using hasDerivAt_inv (by norm_num : (1 : ℝ)≠0)
  have hc : HasDerivAt (fun u : ℝ => J (u⁻¹)) (-deriv J 1) 1 := by
    convert! hd'.scomp 1 hi using 1 <;> simp
  have he : J=ᶠ[𝓝 (1 : ℝ)] (fun u => J (u⁻¹)) := by
    filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ)<1)] with u hu
    exact (J_inv hu).symm
  have hh := hd.unique (hc.congr_of_eventuallyEq he)
  linarith

end
end SpanningTreeIsoperimetry.FirstProfileModular
