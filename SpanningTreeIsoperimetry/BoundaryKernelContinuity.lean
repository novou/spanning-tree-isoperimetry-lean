import SpanningTreeIsoperimetry.BoundaryKernelMajorant

/-! The separated loss density has its correct continuous zero endpoint.
The proof uses positive domination, rather than assuming removability. -/
namespace SpanningTreeIsoperimetry.BoundaryKernelContinuity
open Set Filter MeasureTheory RectangularRemainder BoundaryKernelBounds
open BoundaryLossIntegral BoundaryKernelMajorant
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem integrand_small_bound {r c x : ℝ} (hc : 0≤c) (hr : c<r) (hx : x∈Icc (0 : ℝ) 1) :
    integrand r c x≤(Real.sinh c^2/(2*r))*x^2 := by
  by_cases hx0 : x=0
  · simp [integrand,hx0]
  have hxp : 0<x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  have hr0 : 0<r := lt_of_le_of_lt hc hr
  have hs : Real.sinh (c*x)≤x*Real.sinh c := by
    have h := sinh_scale_le (a := x) (c := (1 : ℝ)) (t := c) hx.1 (by norm_num) hx.2 hc
    simpa only [div_one,one_mul,mul_comm x c] using h
  have hs0 : 0≤Real.sinh (c*x) := Real.sinh_nonneg_iff.mpr (mul_nonneg hc hx.1)
  have hd : 2*r*x≤Real.exp (2*r*x)-1 := by linarith [Real.add_one_le_exp (2*r*x)]
  have hd0 : 0<2*r*x := by positivity
  have he0 : 0<Real.exp (2*r*x)-1 := hd0.trans_le hd
  unfold integrand
  calc
    x*Real.sinh (c*x)^2/(Real.exp (2*r*x)-1)≤x*(x*Real.sinh c)^2/(Real.exp (2*r*x)-1) := by
      apply div_le_div_of_nonneg_right _ he0.le
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0 hs 2) hx.1
    _≤x*(x*Real.sinh c)^2/(2*r*x) :=
      div_le_div_of_nonneg_left (by positivity) hd0 hd
    _=(Real.sinh c^2/(2*r))*x^2 := by field_simp <;> ring

theorem integrand_continuousWithinAt_zero {r c : ℝ} (hc : 0≤c) (hr : c<r) :
    ContinuousWithinAt (integrand r c) (Ici 0) 0 := by
  have hz : integrand r c 0=0 := by simp [integrand]
  rw [ContinuousWithinAt,hz]
  have hmajor : Tendsto (fun x : ℝ => (Real.sinh c^2/(2*r))*x^2) (𝓝[Ici 0] 0) (𝓝 0) := by
    have hh : Continuous (fun x : ℝ => (Real.sinh c^2/(2*r))*x^2) := by fun_prop
    simpa only [zero_pow (by decide : 2≠0),mul_zero] using (hh.tendsto 0).mono_left nhdsWithin_le_nhds
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact integrand_nonneg (lt_of_le_of_lt hc hr).le hx
  · filter_upwards [self_mem_nhdsWithin,
      (gt_mem_nhds (show (0 : ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds] with x hx hx1
    exact integrand_small_bound hc hr ⟨hx,hx1.le⟩

theorem integrand_continuousOn {r c : ℝ} (hc : 0≤c) (hr : c<r) :
    ContinuousOn (integrand r c) (Ici 0) := by
  intro x hx
  by_cases hx0 : x=0
  · subst x
    exact integrand_continuousWithinAt_zero hc hr
  · have hxp : 0<x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hr0 : 0<r := lt_of_le_of_lt hc hr
    have hd : Real.exp (2*r*x)-1≠0 := by
      have h := Real.one_lt_exp_iff.mpr (show 0<2*r*x by positivity)
      linarith
    apply ContinuousAt.continuousWithinAt
    unfold integrand
    fun_prop

theorem gamma_integrand_continuousOn {r c : ℝ} (hc : 0≤c) (hr : c<r) :
    ContinuousOn (fun θ => integrand r c (gamma θ)*gammaDeriv θ) (Icc 0 Real.pi) := by
  change ContinuousOn (((integrand r c) ∘ gamma)*gammaDeriv) (Icc 0 Real.pi)
  exact ((integrand_continuousOn hc hr).comp contDiff_gamma.continuous.continuousOn
    (fun θ hθ => gamma_nonneg hθ)).mul continuous_gammaDeriv.continuousOn

/-- Continuity of the raw separated density, including theta=0, follows from
its exact positive majorant tending to zero at the endpoint. -/
theorem density_continuousOn {r a a' c : ℝ} (ha : 0≤a) (ha' : 0≤a') (hc : 0<c)
    (hac : a≤c) (ha'c : a'≤c) (hr : c<r) (b b' : ℕ) :
    ContinuousOn (density r a a' b b') (Icc 0 Real.pi) := by
  intro θ hθ
  by_cases hθ0 : θ=0
  · subst θ
    have hz : density r a a' b b' 0=0 := by simp [density,gamma_zero]
    rw [ContinuousWithinAt,hz]
    let C : ℝ := (a*a'/c^2)*(b : ℝ)*b'
    have hmajor : Tendsto (fun θ => C*(integrand r c (gamma θ)*gammaDeriv θ))
        (𝓝[Icc 0 Real.pi] 0) (𝓝 0) := by
      have h := ((gamma_integrand_continuousOn hc.le hr).const_mul C) 0
        (show (0 : ℝ)∈Icc 0 Real.pi from ⟨le_rfl,Real.pi_pos.le⟩)
      simpa only [ContinuousWithinAt,gamma_zero,integrand,mul_zero,Real.sinh_zero,zero_pow (by decide : 2≠0),
        zero_div,zero_mul] using h
    apply squeeze_zero_norm' _ hmajor
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    by_cases hθ0 : θ=0
    · simp [hθ0,density,gamma_zero,integrand]
    · have hθp : 0<θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
      simpa only [Real.norm_eq_abs,C] using abs_density_le ha ha' hc hac ha'c hr b b' ⟨hθp,hθ.2⟩
  · have hθp : 0<θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
    have hg : 0<gamma θ := by
      have h := gamma_strictMonoOn ⟨le_rfl,Real.pi_pos.le⟩ hθ hθp
      simpa only [gamma_zero] using h
    have hr0 : 0<r := lt_trans hc hr
    have hd : Real.sinh (gamma θ)*(Real.exp (2*r*gamma θ)-1)≠0 := by
      apply mul_ne_zero (Real.sinh_pos_iff.mpr hg).ne'
      have h := Real.one_lt_exp_iff.mpr (show 0<2*r*gamma θ by positivity)
      linarith
    have hgcont := contDiff_gamma.continuous
    apply ContinuousAt.continuousWithinAt
    unfold density
    fun_prop

end
end SpanningTreeIsoperimetry.BoundaryKernelContinuity
