import SpanningTreeIsoperimetry.SummableDeterminantAffine
import SpanningTreeIsoperimetry.SummableDeterminantContinuity

/-! Differentiating the actual finite-section determinant along an entrywise
summable kernel path. A remainder small in total entry mass is transferred
through the proved determinant Lipschitz estimate. No kernel Banach-space
instance or external operator determinant derivative is assumed. -/
namespace SpanningTreeIsoperimetry.SummableDeterminantPath
open SummableKernelProduct SummableKernelAlgebra SummableKernelDeterminant
open SummableDeterminantFirstOrder SummableKernelTrace AbsolutelySummableDeterminant
open SummableDeterminantAffine SummableDeterminantContinuity Filter Asymptotics
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem mass_add_le {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) : totalMass (A+B)≤totalMass A+totalMass B := by
  calc
    totalMass (A+B)≤tsum (fun p : ℕ×ℕ => entryNorm A p+entryNorm B p) :=
      (add_summable hA hB).tsum_le_tsum (fun p => abs_add_le _ _) (hA.add hB)
    _=totalMass A+totalMass B := hA.tsum_add hB

def pathDeterminant (K : ℝ → Kernel) (hK : ∀ t,Summable (entryNorm (K t))) (t : ℝ) : ℝ :=
  detLimit (K t) (hK t)

/-- A small mass remainder also supplies the local mass bound needed by the
nonlinear determinant estimate; boundedness is not an extra path hypothesis. -/
theorem path_mass_eventually_bounded {K : ℝ → Kernel} {H : Kernel}
    (hK : ∀ t,Summable (entryNorm (K t))) (hH : Summable (entryNorm H))
    (hrem : (fun t => totalMass (K t-affine (K 0) H t)) =o[𝓝 0] fun t => t) :
    ∀ᶠ t in 𝓝 (0 : ℝ),totalMass (K t)+totalMass (affine (K 0) H t)≤
      1+2*(totalMass (K 0)+totalMass H) := by
  have hr : Tendsto (fun t => totalMass (K t-affine (K 0) H t)) (𝓝 0) (𝓝 0) :=
    hrem.trans_tendsto tendsto_id
  have ht : Tendsto (fun t : ℝ => |t|) (𝓝 0) (𝓝 0) := by
    simpa only [abs_zero] using continuous_abs.tendsto (0 : ℝ)
  filter_upwards [hr.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))] with t hr ht
  have ha : totalMass (affine (K 0) H t)≤totalMass (K 0)+totalMass H := by
    have h := mass_add_le (hK 0) (scale_summable t hH)
    rw [scale_mass] at h
    change totalMass (affine (K 0) H t)≤totalMass (K 0)+|t| *totalMass H at h
    have hm := mul_le_of_le_one_left (totalMass_nonneg H) ht.le
    linarith
  have hk := mass_add_le (difference_summable (hK t) (affine_summable (hK 0) hH t))
    (affine_summable (hK 0) hH t)
  rw [sub_add_cancel] at hk
  linarith

/-- The determinant difference from the affine approximation is little-o(t). -/
theorem determinant_difference_isLittleO {K : ℝ → Kernel} {H : Kernel}
    (hK : ∀ t,Summable (entryNorm (K t))) (hH : Summable (entryNorm H))
    (hrem : (fun t => totalMass (K t-affine (K 0) H t)) =o[𝓝 0] fun t => t) :
    (fun t => pathDeterminant K hK t-affineDeterminant (K 0) H (hK 0) hH t) =o[𝓝 0]
      fun t => t := by
  have hbig : (fun t => pathDeterminant K hK t-affineDeterminant (K 0) H (hK 0) hH t)
      =O[𝓝 0] (fun t => totalMass (K t-affine (K 0) H t)) := by
    apply isBigO_iff.mpr
    refine ⟨Real.exp (1+2*(totalMass (K 0)+totalMass H)),?_⟩
    filter_upwards [path_mass_eventually_bounded hK hH hrem] with t ht
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (totalMass_nonneg _)]
    have h := detLimit_lipschitz (hK t) (affine_summable (hK 0) hH t)
    exact h.trans (by
      rw [mul_comm (Real.exp _)]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ht) (totalMass_nonneg _))
  exact hbig.trans_isLittleO hrem

/-- Actual determinant-path derivative at zero. The inverse equation is a
concrete kernel identity and the derivative is the actual diagonal trace. -/
theorem hasDerivAt_path_zero {K : ℝ → Kernel} {J H : Kernel}
    (hK : ∀ t,Summable (entryNorm (K t))) (hJ : Summable (entryNorm J))
    (hH : Summable (entryNorm H)) (hKJ : composePerturbation (K 0) J=0)
    (hrem : (fun t => totalMass (K t-affine (K 0) H t)) =o[𝓝 0] fun t => t) :
    HasDerivAt (pathDeterminant K hK)
      (detLimit (K 0) (hK 0)*trace (relativeDirection J H)) 0 := by
  have ha := hasDerivAt_affine_zero (hK 0) hJ hH hKJ
  have hr := determinant_difference_isLittleO hK hH hrem
  have ha' : (fun t => affineDeterminant (K 0) H (hK 0) hH t-
      affineDeterminant (K 0) H (hK 0) hH 0-
      t*(detLimit (K 0) (hK 0)*trace (relativeDirection J H))) =o[𝓝 0] fun t => t := by
    simpa only [sub_zero,smul_eq_mul] using ha.isLittleO
  apply HasDerivAt.of_isLittleO
  have hsum := hr.add ha'
  convert hsum using 1
  · funext t
    rw [affineDeterminant_zero]
    simp only [pathDeterminant,sub_zero,smul_eq_mul]
    ring
  · funext t
    exact sub_zero t

/-- The logarithmic derivative is the trace of the actual relative direction,
with nonvanishing discharged by the explicit inverse. -/
theorem hasDerivAt_log_path_zero {K : ℝ → Kernel} {J H : Kernel}
    (hK : ∀ t,Summable (entryNorm (K t))) (hJ : Summable (entryNorm J))
    (hH : Summable (entryNorm H)) (hKJ : composePerturbation (K 0) J=0)
    (hrem : (fun t => totalMass (K t-affine (K 0) H t)) =o[𝓝 0] fun t => t) :
    HasDerivAt (fun t => Real.log (pathDeterminant K hK t)) (trace (relativeDirection J H)) 0 := by
  have hn := (inverse_pair_nonzero (hK 0) hJ hKJ).1
  have hd := (hasDerivAt_path_zero hK hJ hH hKJ hrem).log hn
  convert hd using 1
  change _=(_* _)/detLimit (K 0) (hK 0)
  field_simp

end
end SpanningTreeIsoperimetry.SummableDeterminantPath
