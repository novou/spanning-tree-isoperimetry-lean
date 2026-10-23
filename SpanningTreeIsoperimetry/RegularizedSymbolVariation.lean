module

public import SpanningTreeIsoperimetry.RegularizedStripSymbol
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

set_option backward.privateInPublic true

/-! Uniform total variation of the first derivative of the regularized
strip symbol. Its curvature numerator crosses zero once on[0,pi]. -/
namespace SpanningTreeIsoperimetry.RegularizedSymbolVariation
open RegularizedStripSymbol Set MeasureTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def radicand (z θ : ℝ) : ℝ := (z/2-Real.cos θ)^2-1
def first (z θ : ℝ) : ℝ := Real.sin θ/Real.sqrt (radicand z θ)
def curvature (z θ : ℝ) : ℝ := (z/2)*Real.cos θ-(Real.cos θ)^2-1
def second (z θ : ℝ) : ℝ := (z/2)*curvature z θ/(Real.sqrt (radicand z θ))^3

theorem radicand_pos {z : ℝ} (hz : 4<z) (θ : ℝ) : 0<radicand z θ := by
  have ha : 1<z/2-Real.cos θ := by linarith [Real.cos_le_one θ]
  unfold radicand
  nlinarith

theorem root_pos {z : ℝ} (hz : 4<z) (θ : ℝ) : 0<Real.sqrt (radicand z θ) :=
  Real.sqrt_pos.mpr (radicand_pos hz θ)

theorem continuous_first {z : ℝ} (hz : 4<z) : Continuous (first z) := by
  have hr : Continuous (radicand z) := by unfold radicand; fun_prop
  exact Real.continuous_sin.div (Real.continuous_sqrt.comp hr) (fun θ => (root_pos hz θ).ne')

theorem continuous_second {z : ℝ} (hz : 4<z) : Continuous (second z) := by
  have hr : Continuous (radicand z) := by unfold radicand; fun_prop
  have hn : Continuous (fun θ => (z/2)*curvature z θ) := by unfold curvature; fun_prop
  exact hn.div ((Real.continuous_sqrt.comp hr).pow 3) (fun θ => pow_ne_zero 3 (root_pos hz θ).ne')

theorem hasDerivAt_first {z : ℝ} (hz : 4<z) (θ : ℝ) :
    HasDerivAt (first z) (second z θ) θ := by
  have hd : HasDerivAt (radicand z)
      (2*(z/2-Real.cos θ)*Real.sin θ) θ := by
    convert (((hasDerivAt_const θ (z/2)).sub (Real.hasDerivAt_cos θ)).pow 2).sub_const 1 using 1
    · funext x
      rfl
    · simp <;> ring
  have hs := (Real.hasDerivAt_sin θ).div (hd.sqrt (radicand_pos hz θ).ne') (root_pos hz θ).ne'
  have hsin : (Real.sin θ)^2=1-(Real.cos θ)^2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
  have hnum : Real.cos θ*(Real.sqrt (radicand z θ))^2-
      (z/2-Real.cos θ)*(Real.sin θ)^2=(z/2)*curvature z θ := by
    rw [Real.sq_sqrt (radicand_pos hz θ).le,hsin]
    unfold radicand curvature
    ring
  convert hs using 1
  · funext x
    rfl
  · unfold second
    rw [← hnum]
    field_simp [(root_pos hz θ).ne']
    <;> ring

theorem hasDerivAt_gamma {z : ℝ} (hz : 4<z) (θ : ℝ) :
    HasDerivAt (gammaZ z) (first z θ) θ := hasDerivAt_gammaZ hz θ

theorem first_zero (z : ℝ) : first z 0=0 := by simp [first]
theorem first_pi (z : ℝ) : first z Real.pi=0 := by simp [first]

theorem first_bounds {z θ : ℝ} (hz : 4<z) (hθ : θ∈Icc 0 Real.pi) :
    0≤first z θ ∧ first z θ≤1 := by
  have hs : 0≤Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
  have hp := root_pos hz θ
  have hfac : 0≤(z/2-2)*(z/2+2-2*Real.cos θ) :=
    mul_nonneg (by linarith) (by linarith [Real.cos_le_one θ])
  have hsq : (Real.sin θ)^2≤radicand z θ := by
    unfold radicand
    nlinarith [Real.sin_sq_add_cos_sq θ,sq_nonneg (Real.cos θ-1)]
  have hsinRoot : Real.sin θ≤Real.sqrt (radicand z θ) := by
    nlinarith [Real.sq_sqrt (radicand_pos hz θ).le]
  exact ⟨div_nonneg hs hp.le,(div_le_one hp).mpr hsinRoot⟩

theorem curvature_antitone {z : ℝ} (hz : 4<z) : AntitoneOn (curvature z) (Icc 0 Real.pi) := by
  intro x hx y hy hxy
  have hcos := Real.antitoneOn_cos hx hy hxy
  have hp : 0≤(Real.cos x-Real.cos y)*(z/2-Real.cos x-Real.cos y) :=
    mul_nonneg (sub_nonneg.mpr hcos) (by linarith [Real.cos_le_one x,Real.cos_le_one y])
  unfold curvature
  nlinarith only [hp]

theorem second_sign_split {z : ℝ} (hz : 4<z) :
    ∃ c∈Icc 0 Real.pi,
      (∀ θ∈Icc 0 c, 0≤second z θ) ∧ (∀ θ∈Icc c Real.pi, second z θ≤0) := by
  have hcont : Continuous (curvature z) := by unfold curvature; fun_prop
  have hcross : (0 : ℝ)∈Icc (curvature z Real.pi) (curvature z 0) := by
    norm_num [curvature]
    constructor <;> linarith
  obtain ⟨c,hc,hzero⟩ := intermediate_value_Icc' Real.pi_pos.le hcont.continuousOn hcross
  have hm := curvature_antitone hz
  refine ⟨c,hc,?_,?_⟩
  · intro θ hθ
    have hq : 0≤curvature z θ := by
      have hh := hm (show θ∈Icc 0 Real.pi from ⟨hθ.1,hθ.2.trans hc.2⟩) hc hθ.2
      simpa only [hzero] using hh
    exact div_nonneg (mul_nonneg (by linarith) hq) (pow_nonneg (root_pos hz θ).le _)
  · intro θ hθ
    have hq : curvature z θ≤0 := by
      have hh := hm hc (show θ∈Icc 0 Real.pi from ⟨hc.1.trans hθ.1,hθ.2⟩) hθ.1
      simpa only [hzero] using hh
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) hq)
      (pow_nonneg (root_pos hz θ).le _)

private theorem integral_abs_of_turn (f g : ℝ → ℝ) (a c b : ℝ)
    (hc : a≤c ∧ c≤b) (hg : Continuous g) (hd : ∀ x,HasDerivAt f (g x) x)
    (hl : ∀ x∈Icc a c,0≤g x) (hr : ∀ x∈Icc c b,g x≤0) :
    (∫ x in a..b,|g x|)=2*f c-f a-f b := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.abs.intervalIntegrable (a := a) (b := c)) (hg.abs.intervalIntegrable (a := c) (b := b))
  have hlEq : (∫ x in a..c,|g x|)=∫ x in a..c,g x := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact abs_of_nonneg (hl x (by simpa only [uIcc_of_le hc.1] using hx))
  have hrEq : (∫ x in c..b,|g x|)=∫ x in c..b,-g x := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact abs_of_nonpos (hr x (by simpa only [uIcc_of_le hc.2] using hx))
  rw [← hadd,hlEq,hrEq,intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hg.intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hg.intervalIntegrable _ _)]
  ring

theorem integral_abs_second_le {z : ℝ} (hz : 4<z) :
    (∫ θ in (0 : ℝ)..Real.pi,|second z θ|)≤2 := by
  obtain ⟨c,hc,hl,hr⟩ := second_sign_split hz
  have he := integral_abs_of_turn (first z) (second z) 0 c Real.pi hc
    (continuous_second hz) (hasDerivAt_first hz) hl hr
  rw [first_zero,first_pi] at he
  linarith only [he,(first_bounds hz hc).2]

end
end SpanningTreeIsoperimetry.RegularizedSymbolVariation
