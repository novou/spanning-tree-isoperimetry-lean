import SpanningTreeIsoperimetry.Targets
import SpanningTreeIsoperimetry.ConcreteCounts

/-! Exact checks against the manuscript's actual canonical selector. -/
namespace SpanningTreeIsoperimetry

private theorem minimumSideSum_seven : minimumSideSum 7 = 6 := by
  unfold minimumSideSum
  apply (Nat.ceil_eq_iff (by decide : 6 ≠ 0)).mpr
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)
  have hn := Real.sqrt_nonneg (7 : ℝ)
  constructor <;> norm_num <;> nlinarith

private theorem minimumSideSum_fourteen : minimumSideSum 14 = 8 := by
  unfold minimumSideSum
  apply (Nat.ceil_eq_iff (by decide : 8 ≠ 0)).mpr
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 14)
  have hn := Real.sqrt_nonneg (14 : ℝ)
  constructor <;> norm_num <;> nlinarith

private theorem minimumSideSum_seventeen : minimumSideSum 17 = 9 := by
  unfold minimumSideSum
  apply (Nat.ceil_eq_iff (by decide : 9 ≠ 0)).mpr
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 17)
  have hn := Real.sqrt_nonneg (17 : ℝ)
  constructor <;> norm_num <;> nlinarith

theorem canonicalDomain_seven : canonicalDomain 7 = ConcreteCounts.canonical7Domain := by
  simp only [canonicalDomain, canonicalParameters, minimumSideSum_seven]
  norm_num [selectorIndex, Nat.sqrt, cornerStrip, ConcreteCounts.canonical7Domain]
  decide

theorem canonicalDomain_fourteen : canonicalDomain 14 = ConcreteCounts.canonical14Domain := by
  simp only [canonicalDomain, canonicalParameters, minimumSideSum_fourteen]
  norm_num [selectorIndex, Nat.sqrt, cornerStrip, ConcreteCounts.canonical14Domain]
  decide

theorem canonicalDomain_seventeen : canonicalDomain 17 = SmallCases.canonical17Domain := by
  simp only [canonicalDomain, canonicalParameters, minimumSideSum_seventeen]
  norm_num [selectorIndex, Nat.sqrt, cornerStrip, SmallCases.canonical17Domain]
  decide

theorem canonicalDomain_exception_counts :
    treeCount (canonicalDomain 7) = 15 ∧ treeCount (canonicalDomain 14) = 8948 ∧
    treeCount (canonicalDomain 17) = 112272 := by
  rw [canonicalDomain_seven, canonicalDomain_fourteen, canonicalDomain_seventeen]
  exact ⟨ConcreteCounts.canonical7_treeCount, ConcreteCounts.canonical14_treeCount,
    ConcreteCounts.canonical17_treeCount⟩

theorem canonicalDomain_not_maximal_seven : ¬ IsMaximizer (canonicalDomain 7) := by
  rw [canonicalDomain_seven]
  exact ConcreteCounts.canonical7_not_isMaximizer

theorem canonicalDomain_not_maximal_fourteen : ¬ IsMaximizer (canonicalDomain 14) := by
  rw [canonicalDomain_fourteen]
  exact ConcreteCounts.canonical14_not_isMaximizer

/-- The manuscript's N=17 obstruction to extending the canonical theorem below 18. -/
theorem canonicalDomain_not_maximal_seventeen : ¬ IsMaximizer (canonicalDomain 17) := by
  rw [canonicalDomain_seventeen]
  exact ConcreteCounts.canonical17_not_isMaximizer

end SpanningTreeIsoperimetry
