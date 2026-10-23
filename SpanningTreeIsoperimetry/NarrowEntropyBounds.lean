module

public import SpanningTreeIsoperimetry.CatalanEulerBounds

@[expose] public section

/-! Narrow entropy bounds from one Euler correction of checked blocks. -/
namespace SpanningTreeIsoperimetry.NarrowEntropyBounds
open LocalBounds RefinedEntropyBounds CatalanEulerBounds
open scoped BigOperators
noncomputable section
set_option maxRecDepth 4096

theorem catalan_lower : (9159655939 : ℝ)/10000000000<catalanConstant := by
  have hl := catalan_euler_bounds.1
  have hb := block_sum_bounds.1
  have hn : (9159655939 : ℝ)/10000000000<
      (∑ j : Fin 16,blockLower j)+catalanTerm 800/2 := by
    norm_num [blockLower,Fin.sum_univ_succ,catalanTerm]
  linarith only [hl,hb,hn]

theorem catalan_upper : catalanConstant<(9159655945 : ℝ)/10000000000 := by
  have hu := catalan_euler_bounds.2
  have hb := block_sum_bounds.2
  have hn : (∑ j : Fin 16,blockUpper j)+catalanTerm 800/2+delta 800/2<
      (9159655945 : ℝ)/10000000000 := by
    norm_num [blockUpper,Fin.sum_univ_succ,catalanTerm,delta]
  linarith only [hu,hb,hn]

theorem entropy_lower : (1166243615 : ℝ)/1000000000<SquareMaximality.squareLatticeEntropy := by
  rw [← entropy_eq_foundation,entropyConstant,lt_div_iff₀ Real.pi_pos]
  nlinarith [catalan_lower,Real.pi_lt_d20]

theorem entropy_upper : SquareMaximality.squareLatticeEntropy<(1166243617 : ℝ)/1000000000 := by
  rw [← entropy_eq_foundation,entropyConstant,div_lt_iff₀ Real.pi_pos]
  nlinarith [catalan_upper,Real.pi_gt_d20]

end
end SpanningTreeIsoperimetry.NarrowEntropyBounds
