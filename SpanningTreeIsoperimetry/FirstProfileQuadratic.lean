module

public import SpanningTreeIsoperimetry.FirstProfileModular
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! Local quadratic control of the actual first aspect profile at the
square, sufficient for the extremal O(N^(-1/2)) remainder. -/
namespace SpanningTreeIsoperimetry.FirstProfileQuadratic
open RectangularRemainder FirstProfileModular Filter Asymptotics Set
open scoped Topology
noncomputable section

theorem exists_quadratic_bound :
    ∃ C ε : ℝ, 0<C ∧ 0<ε ∧ ∀ u : ℝ, 1≤u → u≤1+ε → |J u-J 1|≤C*(u-1)^2 := by
  have hc : ContDiffAt ℝ 1 (deriv J) 1 :=
    (contDiffAt_J (by norm_num : (0 : ℝ)<1)).derivWithin (by norm_num)
  have hd := (hc.differentiableAt (by norm_num)).hasDerivAt
  have hO : (fun u : ℝ => deriv J u)=O[𝓝 1] (fun u => u-1) := by
    simpa only [deriv_J_one,sub_zero] using hd.isBigO_sub
  obtain ⟨C,hC,hB⟩ := hO.exists_pos
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hB.bound
  refine ⟨C,ε/2,hC,half_pos hε,?_⟩
  intro u hu huε
  have hderiv (v : ℝ) (hv : v∈Icc 1 u) : ‖deriv J v‖≤C*(u-1) := by
    have hvball : v∈Metric.ball (1 : ℝ) ε := by
      rw [Metric.mem_ball,Real.dist_eq,abs_of_nonneg (show 0≤v-1 by linarith [hv.1])]
      linarith [hv.2]
    have hh := hball hvball
    have hh' : ‖deriv J v‖≤C*(v-1) := by
      simpa only [Set.mem_setOf_eq,Real.norm_eq_abs,abs_of_nonneg (show 0≤v-1 by linarith [hv.1])] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_left (by linarith [hv.2]) hC.le)
  have hmean := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun v (hv : v∈Icc 1 u) => (hasDerivAt_J (show 0<v by linarith [hv.1])).differentiableAt)
    hderiv (convex_Icc 1 u) (show (1 : ℝ)∈Icc 1 u from ⟨le_rfl,hu⟩)
    (show u∈Icc 1 u from ⟨hu,le_rfl⟩)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hu),pow_two,mul_assoc] using hmean

end
end SpanningTreeIsoperimetry.FirstProfileQuadratic
