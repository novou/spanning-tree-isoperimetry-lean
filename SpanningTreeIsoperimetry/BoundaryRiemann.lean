import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! A one-dimensional uniform-grid Riemann limit for the finite sine sums.
Only continuity on the compact interval is required. -/
namespace SpanningTreeIsoperimetry.BoundaryRiemann
open Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section

def node (n j : ℕ) : ℝ := (j : ℝ)/n

def leftSum (f : ℝ → ℝ) (n : ℕ) : ℝ := (1/(n : ℝ))*∑ j ∈ Finset.range n, f (node n j)

theorem node_step {n : ℕ} (hn : 0<n) (j : ℕ) : node n (j+1)-node n j=1/(n : ℝ) := by
  unfold node
  push_cast
  ring

theorem node_mono {n : ℕ} (hn : 0<n) {i j : ℕ} (hij : i≤j) : node n i≤node n j := by
  unfold node
  exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)

theorem node_mem {n : ℕ} (hn : 0<n) {j : ℕ} (hj : j≤n) : node n j∈Icc (0 : ℝ) 1 := by
  constructor
  · unfold node; positivity
  · unfold node
    exact (div_le_one₀ (by exact_mod_cast hn : (0 : ℝ)<n)).mpr (by exact_mod_cast hj)

private theorem cell_integrable {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    {n : ℕ} (hn : 0<n) {j : ℕ} (hj : j<n) :
    IntervalIntegrable f volume (node n j) (node n (j+1)) := by
  apply ContinuousOn.intervalIntegrable_of_Icc (node_mono hn (Nat.le_succ j))
  apply hf.mono
  intro x hx
  exact ⟨(node_mem hn (by omega : j≤n)).1.trans hx.1,
    hx.2.trans (node_mem hn (by omega : j+1≤n)).2⟩

/-- Cellwise oscillation controls the complete finite Riemann-sum error. -/
theorem leftSum_error_le {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    {n : ℕ} (hn : 0<n) (ε : ℝ)
    (hosc : ∀ j<n, ∀ x∈Icc (node n j) (node n (j+1)), |f (node n j)-f x|≤ε) :
    |leftSum f n-∫ x in (0 : ℝ)..1, f x|≤ε := by
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hsum : (∑ j ∈ Finset.range n, ∫ x in node n j..node n (j+1), f x)=
      ∫ x in (0 : ℝ)..1, f x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (a := node n) (n := n) (fun j hj => cell_integrable hf hn hj)
    simpa only [node,Nat.cast_zero,zero_div,div_self hn0] using h
  have hcell (j : ℕ) (hj : j<n) :
      |(1/(n : ℝ))*f (node n j)-(∫ x in node n j..node n (j+1), f x)|≤ε*(1/n) := by
    have hbound : ∀ x∈uIoc (node n j) (node n (j+1)), ‖f (node n j)-f x‖≤ε := by
      intro x hx
      rw [uIoc_of_le (node_mono hn (Nat.le_succ j))] at hx
      simpa only [Real.norm_eq_abs] using hosc j hj x ⟨hx.1.le,hx.2⟩
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [intervalIntegral.integral_sub intervalIntegrable_const (cell_integrable hf hn hj),
      intervalIntegral.integral_const,node_step hn j,smul_eq_mul,Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ)<1/n)] at h
    exact h
  rw [leftSum,Finset.mul_sum,← hsum,← Finset.sum_sub_distrib]
  calc
    _≤∑ j ∈ Finset.range n, |(1/(n : ℝ))*f (node n j)-∫ x in node n j..node n (j+1), f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _≤∑ _j ∈ Finset.range n, ε*(1/(n : ℝ)) :=
      Finset.sum_le_sum (fun j hj => hcell j (Finset.mem_range.mp hj))
    _=ε := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      field_simp

/-- The ordinary uniform-grid Riemann theorem, obtained directly from compact
uniform continuity and the checked finite-cell error inequality. -/
theorem leftSum_tendsto {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Tendsto (leftSum f) atTop (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hf
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuousOn_iff.mp huc (ε/2) (half_pos hε)
  have hlim : Tendsto (fun n : ℕ => (1 : ℝ)/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (gt_mem_nhds hδ),eventually_ge_atTop (1 : ℕ)] with n hnδ hn
  have hnpos : 0<n := by omega
  rw [Real.dist_eq]
  apply lt_of_le_of_lt (leftSum_error_le hf hnpos (ε/2) ?_) (half_lt_self hε)
  intro j hj x hx
  have hjmem := node_mem hnpos (show j≤n by omega)
  have hxmem : x∈Icc (0 : ℝ) 1 :=
    ⟨hjmem.1.trans hx.1,hx.2.trans (node_mem hnpos (show j+1≤n by omega)).2⟩
  have hdist : dist (node n j) x<δ := by
    rw [Real.dist_eq,abs_of_nonpos (by linarith [hx.1] : node n j-x≤0)]
    have hstep := node_step hnpos j
    linarith [hx.2]
  simpa only [Real.dist_eq] using (hmod (node n j) hjmem x hxmem hdist).le

end
end SpanningTreeIsoperimetry.BoundaryRiemann
