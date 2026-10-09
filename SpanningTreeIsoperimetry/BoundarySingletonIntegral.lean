import SpanningTreeIsoperimetry.BoundarySingletonWeight
import SpanningTreeIsoperimetry.BoundarySingletonTail
import SpanningTreeIsoperimetry.BoundaryLossKernel

/-! Quantitative lower bound for the actual singleton quadrant-to-strip loss. -/
namespace SpanningTreeIsoperimetry.BoundarySingletonIntegral
open Set Filter MeasureTheory RectangularRemainder BoundaryKernelBounds BoundaryKernelMajorant
  BoundaryBoseMoments BoundarySingletonWeight BoundarySingletonTail BoundaryGreenBounds GreenStripLimits
open scoped Topology
noncomputable section

theorem density_singleton_eq (r θ : ℝ) : density r 1 1 1 1 θ=
    Real.sin θ^2*Real.sinh (gamma θ)/(Real.exp (2*r*gamma θ)-1) := by
  by_cases hs : Real.sinh (gamma θ)=0
  · simp [density,hs]
  · unfold density
    simp only [Nat.cast_one,one_mul]
    field_simp
    <;> ring

theorem density_singleton_nonneg {r θ : ℝ} (hr : 0≤r) (hθ : θ∈Icc (0 : ℝ) Real.pi) :
    0≤density r 1 1 1 1 θ := by
  rw [density_singleton_eq]
  have hg := gamma_nonneg hθ
  have hs := Real.sinh_nonneg_iff.mpr hg
  have he := Real.one_le_exp_iff.mpr (show 0≤2*r*gamma θ by positivity)
  positivity

theorem transformed_cubic_le_density {r θ : ℝ} (hr : 0 < r)
    (hθ : θ∈Ioo (0 : ℝ) (Real.pi/2)) :
    bose 3 r (gamma θ)*gammaDeriv θ≤density r 1 1 1 1 θ := by
  have hθ' : θ∈Ioo (0 : ℝ) Real.pi := ⟨hθ.1,by linarith [hθ.2,Real.pi_pos]⟩
  have hg := gamma_pos hθ'
  have hd := gammaDeriv_nonneg ⟨hθ'.1.le,hθ'.2.le⟩
  have he : 0 < Real.exp (2*r*gamma θ)-1 := by
    have h := Real.one_lt_exp_iff.mpr (show 0 < 2*r*gamma θ by positivity)
    linarith
  have hw := mul_le_mul_of_nonneg_right (singleton_weight_lower ⟨hθ.1.le,hθ.2.le⟩) hd
  have hnum : (gamma θ)^3*gammaDeriv θ≤Real.sin θ^2*Real.sinh (gamma θ) := by
    have hid : Real.sin θ*Real.sinh (gamma θ)^2*gammaDeriv θ=
        Real.sin θ^2*Real.sinh (gamma θ) := by
      calc
        _=(Real.sin θ*Real.sinh (gamma θ))*(Real.sinh (gamma θ)*gammaDeriv θ) := by ring
        _=_ := by rw [sinh_gamma_mul_deriv]; ring
    rwa [hid] at hw
  rw [density_singleton_eq]
  unfold bose
  convert div_le_div_of_nonneg_right hnum he.le using 1 <;> ring

theorem truncated_cubic_le_integral {r : ℝ} (hr : 1 < r) :
    (∫ x in (0 : ℝ)..(5/4), bose 3 r x)≤∫ θ in (0 : ℝ)..Real.pi, density r 1 1 1 1 θ := by
  have hr0 : 0 < r := by linarith
  have hg0 : 0≤gamma (Real.pi/2) := gamma_nonneg ⟨by positivity,by linarith [Real.pi_pos]⟩
  have hb : IntervalIntegrable (bose 3 r) volume 0 (gamma (Real.pi/2)) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hg0]
    exact (bose_three_integrable hr0).mono_set (fun x hx => hx.1)
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi/2) (f := gamma) (f' := gammaDeriv) (g := bose 3 r)
    contDiff_gamma.continuous.continuousOn (fun θ _ => hasDerivAt_gamma θ)
    (fun θ hθ => by
      have hθ' : θ∈Ioo (0 : ℝ) (Real.pi/2) := by simpa only [min_eq_left (by positivity : (0 : ℝ)≤Real.pi/2),max_eq_right (by positivity : (0 : ℝ)≤Real.pi/2)] using hθ
      exact gammaDeriv_nonneg ⟨hθ'.1.le,by linarith [hθ'.2,Real.pi_pos]⟩)
  have hbi : IntervalIntegrable (fun θ => bose 3 r (gamma θ)*gammaDeriv θ) volume 0 (Real.pi/2) := by
    apply hiff.mpr
    simpa only [gamma_zero] using hb
  have he := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi/2) (f := gamma) (f' := gammaDeriv) (g := bose 3 r)
    contDiff_gamma.continuous.continuousOn (fun θ _ => hasDerivAt_gamma θ)
    (fun θ hθ => by
      have hθ' : θ∈Ioo (0 : ℝ) (Real.pi/2) := by simpa only [min_eq_left (by positivity : (0 : ℝ)≤Real.pi/2),max_eq_right (by positivity : (0 : ℝ)≤Real.pi/2)] using hθ
      exact gammaDeriv_nonneg ⟨hθ'.1.le,by linarith [hθ'.2,Real.pi_pos]⟩)
  simp only [Function.comp_def,gamma_zero] at he
  have hi := density_intervalIntegrable (a := 1) (a' := 1) (c := 1)
    (by norm_num) (by norm_num) (by norm_num) le_rfl le_rfl hr 1 1
  have hip : IntervalIntegrable (density r 1 1 1 1) volume 0 (Real.pi/2) :=
    hi.mono_set (by simp only [Set.uIcc_of_le Real.pi_pos.le,Set.uIcc_of_le (show (0 : ℝ)≤Real.pi/2 by positivity)]; intro x hx; exact ⟨hx.1,by linarith [hx.2,Real.pi_pos]⟩)
  calc
    _≤∫ x in (0 : ℝ)..gamma (Real.pi/2), bose 3 r x := by
      apply intervalIntegral.integral_mono_interval le_rfl (by norm_num) gamma_half_pi_gt_cutoff.le _ hb
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
      exact bose_nonneg 3 hr0.le hx.1.le
    _=∫ θ in (0 : ℝ)..(Real.pi/2), bose 3 r (gamma θ)*gammaDeriv θ := he.symm
    _≤∫ θ in (0 : ℝ)..(Real.pi/2), density r 1 1 1 1 θ :=
      intervalIntegral.integral_mono_on_of_le_Ioo (by positivity) hbi hip (fun θ hθ => transformed_cubic_le_density hr0 hθ)
    _≤∫ θ in (0 : ℝ)..Real.pi, density r 1 1 1 1 θ := by
      apply intervalIntegral.integral_mono_interval le_rfl (by positivity) (by linarith [Real.pi_pos]) _ hi
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with θ hθ
      exact density_singleton_nonneg hr0.le ⟨hθ.1.le,hθ.2⟩

/-- Actual one-boundary Green loss with the appendix's rational constant. R
counts faces, so the primal side length is R+1. -/
theorem singleton_strip_loss_lower {R : ℕ} (hR : 3≤R) :
    (50/99 : ℝ)<((R : ℝ)+1)^4*(quadrantGreen (0,0) (0,0)-stripX R (0,0) (0,0)) := by
  have hr : (4 : ℝ)≤(R : ℝ)+1 := by exact_mod_cast (show 4≤R+1 by omega)
  have he := BoundaryLossKernel.stripX_loss_integral R
    (⟨0,by omega⟩ : Fin R) (⟨0,by omega⟩ : Fin R) 0 0
  simp only [Nat.cast_zero,zero_add] at he
  rw [he]
  exact (truncated_cubic_lower hr).trans_le
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (truncated_cubic_le_integral (by linarith : (1 : ℝ)<(R : ℝ)+1)) (by positivity)) (by positivity))

end
end SpanningTreeIsoperimetry.BoundarySingletonIntegral
