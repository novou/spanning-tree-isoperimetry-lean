module

public import SpanningTreeIsoperimetry.BoundaryKernelBounds
public import SpanningTreeIsoperimetry.BoundaryLossIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

set_option backward.privateInPublic true

/-! Rigorous domination and gamma substitution for the separated one-boundary
loss density. Identification with actual Green limits is kept separate. -/
namespace SpanningTreeIsoperimetry.BoundaryKernelMajorant
open Set Filter MeasureTheory RectangularRemainder BoundaryKernelBounds BoundaryLossIntegral
open scoped Topology
noncomputable section

def density (r a a' : ℝ) (b b' : ℕ) (θ : ℝ) : ℝ :=
  Real.sin ((b : ℝ)*θ)*Real.sin ((b' : ℝ)*θ)*Real.sinh (a*gamma θ)*Real.sinh (a'*gamma θ)/
    (Real.sinh (gamma θ)*(Real.exp (2*r*gamma θ)-1))

private theorem abs_sin_pair_le (b b' : ℕ) (θ : ℝ) :
    |Real.sin ((b : ℝ)*θ)| * |Real.sin ((b' : ℝ)*θ)|≤(b : ℝ)*b'*Real.sin θ^2 := by
  have h := mul_le_mul (abs_sin_nat_mul_le b θ) (abs_sin_nat_mul_le b' θ)
    (abs_nonneg _) (by positivity)
  convert h using 1 <;> rw [mul_mul_mul_comm,← pow_two,sq_abs]

private theorem gamma_pos_Ioc {θ : ℝ} (hθ : θ∈Ioc (0 : ℝ) Real.pi) : 0<gamma θ := by
  have h := gamma_strictMonoOn ⟨le_rfl,Real.pi_pos.le⟩ ⟨hθ.1.le,hθ.2⟩ hθ.1
  simpa only [gamma_zero] using h

theorem abs_density_le {r a a' c : ℝ} (ha : 0≤a) (ha' : 0≤a') (hc : 0<c)
    (hac : a≤c) (ha'c : a'≤c) (hr : c<r) (b b' : ℕ)
    {θ : ℝ} (hθ : θ∈Ioc (0 : ℝ) Real.pi) :
    |density r a a' b b' θ|≤(a*a'/c^2)*(b : ℝ)*b'*
      (integrand r c (gamma θ)*gammaDeriv θ) := by
  have hg : 0<gamma θ := gamma_pos_Ioc hθ
  have hsg : 0<Real.sinh (gamma θ) := Real.sinh_pos_iff.mpr hg
  have hr0 : 0<r := lt_trans hc hr
  have hd : 0<Real.exp (2*r*gamma θ)-1 := by
    have h := Real.one_lt_exp_iff.mpr (show 0<2*r*gamma θ by positivity)
    linarith
  have hsa : 0≤Real.sinh (a*gamma θ) := Real.sinh_nonneg_iff.mpr (mul_nonneg ha hg.le)
  have hsa' : 0≤Real.sinh (a'*gamma θ) := Real.sinh_nonneg_iff.mpr (mul_nonneg ha' hg.le)
  have hnum := mul_le_mul (abs_sin_pair_le b b' θ)
    (sinh_pair_le ha ha' hc hac ha'c hg.le) (mul_nonneg hsa hsa') (by positivity)
  have hj : Real.sin θ^2/Real.sinh (gamma θ)≤gamma θ*gammaDeriv θ := by
    rcases lt_or_eq_of_le hθ.2 with hlt | heq
    · exact sin_sq_div_sinh_gamma_le ⟨hθ.1,hlt⟩
    · subst θ
      simp only [Real.sin_pi,zero_pow (by decide : 2≠0),zero_div]
      exact mul_nonneg (gamma_nonneg ⟨Real.pi_pos.le,le_rfl⟩)
        (gammaDeriv_nonneg ⟨Real.pi_pos.le,le_rfl⟩)
  unfold density
  rw [abs_div,abs_of_pos (mul_pos hsg hd)]
  simp only [abs_mul,abs_of_nonneg hsa,abs_of_nonneg hsa']
  calc
    _=((|Real.sin ((b : ℝ)*θ)| * |Real.sin ((b' : ℝ)*θ)|)*
        (Real.sinh (a*gamma θ)*Real.sinh (a'*gamma θ)))/
        (Real.sinh (gamma θ)*(Real.exp (2*r*gamma θ)-1)) := by ring
    _≤((b : ℝ)*b'*Real.sin θ^2)*((a*a'/c^2)*Real.sinh (c*gamma θ)^2)/
        (Real.sinh (gamma θ)*(Real.exp (2*r*gamma θ)-1)) :=
      div_le_div_of_nonneg_right hnum (mul_pos hsg hd).le
    _=((a*a'/c^2)*((b : ℝ)*b'))*(Real.sin θ^2/Real.sinh (gamma θ))*
        (Real.sinh (c*gamma θ)^2/(Real.exp (2*r*gamma θ)-1)) := by
      field_simp
      <;> ring
    _≤((a*a'/c^2)*((b : ℝ)*b'))*(gamma θ*gammaDeriv θ)*
        (Real.sinh (c*gamma θ)^2/(Real.exp (2*r*gamma θ)-1)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hj (by positivity))
        (div_nonneg (sq_nonneg _) hd.le)
    _=_ := by unfold integrand; ring

theorem integrand_nonneg {r c x : ℝ} (hr : 0≤r) (hx : 0≤x) : 0 ≤ integrand r c x := by
  unfold integrand
  apply div_nonneg (by positivity)
  have h := Real.one_le_exp_iff.mpr (show 0≤2*r*x by positivity)
  linarith

theorem gamma_integrand_intervalIntegrable {r c : ℝ} (hc : 0≤c) (hr : c<r) :
    IntervalIntegrable (fun θ => integrand r c (gamma θ)*gammaDeriv θ) volume 0 Real.pi := by
  have hg : IntervalIntegrable (integrand r c) volume (gamma 0) (gamma Real.pi) := by
    rw [gamma_zero,intervalIntegrable_iff_integrableOn_Ioc_of_le
      (gamma_nonneg (show Real.pi∈Icc (0 : ℝ) Real.pi from ⟨Real.pi_pos.le,le_rfl⟩))]
    exact (integrand_integrable hc hr).mono_set (fun x hx => hx.1)
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi) (f := gamma) (f' := gammaDeriv) (g := integrand r c)
    contDiff_gamma.continuous.continuousOn
    (fun θ _ => hasDerivAt_gamma θ) (fun θ hθ => by
      have hθ' : θ∈Ioo (0 : ℝ) Real.pi := by simpa only [min_eq_left Real.pi_pos.le,max_eq_right Real.pi_pos.le] using hθ
      exact gammaDeriv_nonneg ⟨hθ'.1.le,hθ'.2.le⟩)
  simpa only [Function.comp_def] using hiff.mpr hg

theorem gamma_integral_majorant {r c : ℝ} (hc : 0≤c) (hr : c<r) :
    (4/Real.pi)*(∫ θ in (0 : ℝ)..Real.pi, integrand r c (gamma θ)*gammaDeriv θ)≤
      Real.pi^3*c^2/(60*(r^2-c^2)^2) := by
  have he := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi) (f := gamma) (f' := gammaDeriv) (g := integrand r c)
    contDiff_gamma.continuous.continuousOn
    (fun θ _ => hasDerivAt_gamma θ) (fun θ hθ => by
      have hθ' : θ∈Ioo (0 : ℝ) Real.pi := by simpa only [min_eq_left Real.pi_pos.le,max_eq_right Real.pi_pos.le] using hθ
      exact gammaDeriv_nonneg ⟨hθ'.1.le,hθ'.2.le⟩)
  simp only [Function.comp_def,gamma_zero] at he
  rw [he,intervalIntegral.integral_of_le (gamma_nonneg ⟨Real.pi_pos.le,le_rfl⟩)]
  have hb : (∫ x in Ioc 0 (gamma Real.pi), integrand r c x)≤∫ x in Ioi 0, integrand r c x := by
    apply setIntegral_mono_set (integrand_integrable hc hr)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      exact integrand_nonneg (lt_of_le_of_lt hc hr).le hx.le
    · exact Filter.Eventually.of_forall (fun x hx => hx.1)
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans (integral_majorant hc hr)

/-- No continuity or integrability of the raw loss density is supplied as an
input: measurable domination by the proved positive integrand discharges it. -/
theorem density_intervalIntegrable {r a a' c : ℝ} (ha : 0≤a) (ha' : 0≤a') (hc : 0<c)
    (hac : a≤c) (ha'c : a'≤c) (hr : c<r) (b b' : ℕ) :
    IntervalIntegrable (density r a a' b b') volume 0 Real.pi := by
  have hm : Measurable (density r a a' b b') := by
    have hg := contDiff_gamma.continuous.measurable
    unfold density
    fun_prop
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le]
  have hbase := (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mp
    (gamma_integrand_intervalIntegrable hc.le hr)
  apply (hbase.const_mul ((a*a'/c^2)*(b : ℝ)*b')).mono' hm.aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with θ hθ
  simpa only [Real.norm_eq_abs] using abs_density_le ha ha' hc hac ha'c hr b b' hθ

/-- Exact numerical one-boundary integral estimate, ready to be combined with
the actual Green-limit identification. -/
theorem density_integral_le {r a a' c : ℝ} (ha : 0≤a) (ha' : 0≤a') (hc : 0<c)
    (hac : a≤c) (ha'c : a'≤c) (hr : c<r) (b b' : ℕ) :
    (4/Real.pi)*(∫ θ in (0 : ℝ)..Real.pi, density r a a' b b' θ)≤
      Real.pi^3*a*a'*(b : ℝ)*b'/(60*(r^2-c^2)^2) := by
  let C : ℝ := (a*a'/c^2)*(b : ℝ)*b'
  have hC : 0≤C := by unfold C; positivity
  have hupper := (gamma_integrand_intervalIntegrable hc.le hr).const_mul C
  have hle := intervalIntegral.integral_mono_on_of_le_Ioo Real.pi_pos.le
    (density_intervalIntegrable ha ha' hc hac ha'c hr b b') hupper
    (fun θ hθ => (le_abs_self _).trans (abs_density_le ha ha' hc hac ha'c hr b b' ⟨hθ.1,hθ.2.le⟩))
  rw [intervalIntegral.integral_const_mul] at hle
  have hb := mul_le_mul_of_nonneg_left (gamma_integral_majorant hc.le hr) hC
  calc
    _≤(4/Real.pi)*(C*(∫ θ in (0 : ℝ)..Real.pi, integrand r c (gamma θ)*gammaDeriv θ)) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    _=C*((4/Real.pi)*(∫ θ in (0 : ℝ)..Real.pi, integrand r c (gamma θ)*gammaDeriv θ)) := by ring
    _≤C*(Real.pi^3*c^2/(60*(r^2-c^2)^2)) := hb
    _=_ := by
      unfold C
      have hc0 : c≠0 := hc.ne'
      have hgap : r^2-c^2≠0 := by nlinarith
      field_simp
      <;> ring

end
end SpanningTreeIsoperimetry.BoundaryKernelMajorant
