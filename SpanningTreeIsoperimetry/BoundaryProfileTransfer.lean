module

public import SpanningTreeIsoperimetry.BoundaryLowerIntegral
public import SpanningTreeIsoperimetry.BoundarySingletonWeight
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-! Monotone gamma substitution transfers a proved profile on[0,1] into
an actual finite-domain correction lower bound. -/
namespace SpanningTreeIsoperimetry.BoundaryProfileTransfer
open Set Filter MeasureTheory RectangularRemainder BoundaryKernelBounds BoundarySingletonWeight
  Ferrers CornerEnergy BoundaryLowerIntegral
open scoped Topology
noncomputable section

theorem exists_cutoff : ∃ c : ℝ, c∈Ioc (0 : ℝ) (Real.pi/2) ∧ gamma c=1 := by
  have hm : (1 : ℝ)∈Icc (gamma 0) (gamma (Real.pi/2)) := by
    rw [gamma_zero]
    constructor
    · norm_num
    · linarith [gamma_half_pi_gt_cutoff]
  obtain ⟨c,hc,hgc⟩ := intermediate_value_Icc
    (by positivity : (0 : ℝ)≤Real.pi/2) contDiff_gamma.continuous.continuousOn hm
  refine ⟨c,⟨?_,hc.2⟩,hgc⟩
  by_contra hn
  have hc0 : c=0 := by linarith [hc.1]
  simp [hc0] at hgc

theorem profile_integral_le {g d : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 1) (hd : IntervalIntegrable d volume 0 Real.pi)
    (hd0 : ∀ θ∈Icc (0 : ℝ) Real.pi, 0≤d θ)
    (hpoint : ∀ θ∈Ioo (0 : ℝ) Real.pi, gamma θ<1 → g (gamma θ)*gammaDeriv θ≤d θ) :
    (∫ t in (0 : ℝ)..1, g t)≤∫ θ in (0 : ℝ)..Real.pi, d θ := by
  obtain ⟨c,hc,hgc⟩ := exists_cutoff
  have hcπ : c<Real.pi := by linarith [hc.2,Real.pi_pos]
  have hcI : c∈Icc (0 : ℝ) Real.pi := ⟨hc.1.le,hcπ.le⟩
  have hderiv (θ : ℝ) (hθ : θ∈Ioo (min (0 : ℝ) c) (max 0 c)) : 0≤gammaDeriv θ := by
    have hθ' : θ∈Ioo (0 : ℝ) c := by simpa only [min_eq_left hc.1.le,max_eq_right hc.1.le] using hθ
    exact gammaDeriv_nonneg ⟨hθ'.1.le,le_of_lt (hθ'.2.trans hcπ)⟩
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := (0 : ℝ)) (b := c) (f := gamma) (f' := gammaDeriv) (g := g)
    contDiff_gamma.continuous.continuousOn (fun θ _ => hasDerivAt_gamma θ) hderiv
  have hgi : IntervalIntegrable (fun θ => g (gamma θ)*gammaDeriv θ) volume 0 c := by
    apply hiff.mpr
    simpa only [gamma_zero,hgc] using hg
  have he := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := c) (f := gamma) (f' := gammaDeriv) (g := g)
    contDiff_gamma.continuous.continuousOn (fun θ _ => hasDerivAt_gamma θ) hderiv
  simp only [Function.comp_def,gamma_zero,hgc] at he
  have hdi : IntervalIntegrable d volume 0 c := hd.mono_set (by
    simp only [uIcc_of_le Real.pi_pos.le,uIcc_of_le hc.1.le]
    intro θ hθ
    exact ⟨hθ.1,hθ.2.trans hcπ.le⟩)
  calc
    _=∫ θ in (0 : ℝ)..c, g (gamma θ)*gammaDeriv θ := he.symm
    _≤∫ θ in (0 : ℝ)..c, d θ := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hc.1.le hgi hdi
      intro θ hθ
      have hθπ : θ∈Ioo (0 : ℝ) Real.pi := ⟨hθ.1,hθ.2.trans hcπ⟩
      have hγ := gamma_strictMonoOn ⟨hθπ.1.le,hθπ.2.le⟩ hcI hθ.2
      rw [hgc] at hγ
      exact hpoint θ hθπ hγ
    _≤∫ θ in (0 : ℝ)..Real.pi, d θ := by
      apply intervalIntegral.integral_mono_interval le_rfl hc.1.le hcπ.le _ hd
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with θ hθ
      exact hd0 θ ⟨hθ.1.le,hθ.2⟩

/-- Reusable profile-to-correction transfer. All matrix signs, positivity,
finite-domain transport, and convergence are discharged; only the local
pointwise profile comparison remains for each concrete small defect. -/
theorem profile_le_correction {R S : ℕ} {M : Diagram} (hM : IsFerrers M)
    (hfit : M⊆faceRectangle R S) {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 1)
    (hpoint : ∀ θ∈Ioo (0 : ℝ) Real.pi, gamma θ<1 →
      g (gamma θ)*gammaDeriv θ≤densityTrace R M θ) :
    (4/Real.pi)*(∫ t in (0 : ℝ)..1, g t)≤correction (faceRectangle R S) M := by
  exact (mul_le_mul_of_nonneg_left
    (profile_integral_le hg (densityTrace_integrable hfit)
      (fun θ hθ => densityTrace_nonneg hM hθ) hpoint) (by positivity)).trans
        (correction_ge_integral hM hfit)

end
end SpanningTreeIsoperimetry.BoundaryProfileTransfer
