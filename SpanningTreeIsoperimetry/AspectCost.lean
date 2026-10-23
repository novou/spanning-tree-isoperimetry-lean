module

public import SpanningTreeIsoperimetry.RectangularRemainder

@[expose] public section

set_option backward.privateInPublic true

/-! The elementary aspect cost and its monotonicity for actual convergent
rectangle profiles. No rectangular error estimate is assumed. -/
namespace SpanningTreeIsoperimetry.AspectCost

open RectangularRemainder
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def D (w : ℝ) : ℝ := Real.pi*w/12-(1/2)*Real.log (1+w/2)

def Dprime (w : ℝ) : ℝ := Real.pi/12-1/(2*(w+2))

theorem hasDerivAt_D {w : ℝ} (hw : -2<w) : HasDerivAt D (Dprime w) w := by
  have hlog := (((hasDerivAt_id w).div_const 2).const_add 1).log (show 1+w/2≠0 by linarith)
  have hlin := ((hasDerivAt_id w).const_mul Real.pi).div_const 12
  have h := hlin.fun_sub (hlog.const_mul (1/2))
  have hn : w+2≠0 := by linarith
  have hn' : 1+w/2≠0 := by linarith
  have hnswap : 2+w≠0 := by linarith
  unfold D Dprime
  convert h using 1 <;> simp only [id_eq,Pi.sub_apply]
  all_goals try rfl
  all_goals field_simp [hn,hn',hnswap]
  all_goals ring

theorem Dprime_pos {w : ℝ} (hw : 0≤w) : 0<Dprime w := by
  have hrec : 1/(2*(w+2))≤(1/4 : ℝ) := by
    apply (div_le_div_iff₀ (by positivity : 0<2*(w+2)) (by norm_num : (0 : ℝ)<4)).mpr
    linarith
  unfold Dprime
  linarith [Real.pi_gt_three]

theorem Dprime_monotoneOn : MonotoneOn Dprime (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx0 : 0≤x := hx
  have hy0 : 0≤y := hy
  have hrec : 1/(2*(y+2))≤1/(2*(x+2)) := by
    apply (div_le_div_iff₀ (by linarith : 0<2*(y+2))
      (by linarith : 0<2*(x+2))).mpr
    linarith
  unfold Dprime
  linarith

theorem D_strictMonoOn : StrictMonoOn D (Set.Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro w hw
    exact (hasDerivAt_D (by have h : 0≤w := hw; linarith)).continuousAt.continuousWithinAt
  · intro w hw
    have h : 0<w := by simpa only [interior_Ici,Set.mem_Ioi] using hw
    rw [(hasDerivAt_D (by linarith)).deriv]
    exact Dprime_pos h.le

theorem D_convexOn : ConvexOn ℝ (Set.Ici 0) D := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ici 0)
  · intro w hw
    exact (hasDerivAt_D (by have h : 0≤w := hw; linarith)).continuousAt.continuousWithinAt
  · intro w hw
    have h : 0<w := by simpa only [interior_Ici,Set.mem_Ioi] using hw
    exact (hasDerivAt_D (by linarith)).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    have hx0 : 0<x := by simpa only [interior_Ici,Set.mem_Ioi] using hx
    have hy0 : 0<y := by simpa only [interior_Ici,Set.mem_Ioi] using hy
    rw [(hasDerivAt_D (by linarith : -2<x)).deriv,(hasDerivAt_D (by linarith : -2<y)).deriv]
    exact Dprime_monotoneOn hx0.le hy0.le hxy

/-- Dropping only the nonpositive difference of the genuine residual series
bounds the exact aspect-profile difference by the elementary cost. -/
theorem aspect_difference {a b : ℝ} (ha : 0≤a) (hab : a≤b) :
    K (1+a)-K (1+b)≤D b-D a := by
  have hres := linearResidual_mono (by linarith : 0<1+a) (by linarith : 1+a≤1+b)
  have hlog (w : ℝ) (hw : 0≤w) : Real.log (1+w/2)=Real.log (2+w)-Real.log 2 := by
    rw [show 1+w/2=(2+w)/2 by ring,Real.log_div (by linarith : 2+w≠0) (by norm_num : (2 : ℝ)≠0)]
  unfold K B D
  rw [hlog a ha,hlog b (by linarith)]
  have heA : 1+(1+a)=2+a := by ring
  have heB : 1+(1+b)=2+b := by ring
  rw [heA,heB]
  linarith

private theorem hasDerivAt_const_div_shift (A a x : ℝ) (hx : x+a≠0) :
    HasDerivAt (fun y : ℝ => A/(y+a)) (-A/(x+a)^2) x := by
  have h := (hasDerivAt_const x A).fun_div ((hasDerivAt_id x).add_const a) hx
  convert h using 1 <;> simp only [id_eq,zero_mul,mul_one,zero_sub]

theorem hasDerivAt_shifted_difference {A B a b x : ℝ} (hB : 0≤B) (hAB : B≤A) (hab : a≤b)
    (hx : 0<x+a) :
    HasDerivAt (fun y : ℝ => D (A/(y+a))-D (B/(y+b)))
      (Dprime (B/(x+b))*(B/(x+b)^2)-Dprime (A/(x+a))*(A/(x+a)^2)) x := by
  have hxb : 0<x+b := by linarith
  have hAarg : 0≤A/(x+a) := div_nonneg (by linarith) hx.le
  have hBarg : 0≤B/(x+b) := div_nonneg hB hxb.le
  have h₁ := (hasDerivAt_D (by linarith : -2<A/(x+a))).comp x
    (hasDerivAt_const_div_shift A a x hx.ne')
  have h₂ := (hasDerivAt_D (by linarith : -2<B/(x+b))).comp x
    (hasDerivAt_const_div_shift B b x hxb.ne')
  convert h₁.fun_sub h₂ using 1 <;> simp only [Function.comp_apply,Pi.sub_apply,neg_div] <;> ring

private theorem ratio_order {A B a b x : ℝ} (hB : 0≤B) (hAB : B≤A) (hab : a≤b) (hx : 0<x+a) :
    B/(x+b)≤A/(x+a) ∧ B/(x+b)^2≤A/(x+a)^2 := by
  have hxb : 0<x+b := by linarith
  constructor
  · calc
      B/(x+b)≤B/(x+a) := (div_le_div_iff₀ hxb hx).mpr
        (mul_le_mul_of_nonneg_left (by linarith : x+a≤x+b) hB)
      _≤A/(x+a) := div_le_div_of_nonneg_right hAB hx.le
  · calc
      B/(x+b)^2≤B/(x+a)^2 :=
        (div_le_div_iff₀ (sq_pos_of_pos hxb) (sq_pos_of_pos hx)).mpr
          (mul_le_mul_of_nonneg_left (by nlinarith : (x+a)^2≤(x+b)^2) hB)
      _≤A/(x+a)^2 := div_le_div_of_nonneg_right hAB (sq_nonneg _)

/-- The shifted-ratio aspect cost decreases on its full stated domain. -/
theorem shifted_difference_antitone {A B a b : ℝ} (hB : 0≤B) (hAB : B≤A) (hab : a≤b) :
    AntitoneOn (fun x : ℝ => D (A/(x+a))-D (B/(x+b))) (Set.Ioi (-a)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi (-a))
  · intro x hx
    exact (hasDerivAt_shifted_difference hB hAB hab (by have hx' : -a<x := hx; linarith)).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : -a<x := by simpa only [interior_Ioi,Set.mem_Ioi] using hx
    exact (hasDerivAt_shifted_difference hB hAB hab (by linarith)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : -a<x := by simpa only [interior_Ioi,Set.mem_Ioi] using hx
    have hxa : 0<x+a := by linarith
    have hxb : 0<x+b := by linarith
    have hAarg : 0≤A/(x+a) := div_nonneg (by linarith) hxa.le
    have hBarg : 0≤B/(x+b) := div_nonneg hB hxb.le
    rw [(hasDerivAt_shifted_difference hB hAB hab hxa).deriv]
    have hord := ratio_order hB hAB hab hxa
    have hp := Dprime_monotoneOn hBarg hAarg hord.1
    have hmul := mul_le_mul hp hord.2 (div_nonneg hB (sq_nonneg _)) (Dprime_pos hAarg).le
    linarith

end
end SpanningTreeIsoperimetry.AspectCost
