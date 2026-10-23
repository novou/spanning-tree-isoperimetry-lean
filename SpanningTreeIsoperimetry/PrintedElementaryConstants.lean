module

public import SpanningTreeIsoperimetry.NarrowEntropyBounds

@[expose] public section

set_option backward.privateInPublic true

/-! Literal rational intervals printed in the quadrant-certificate appendix. -/
namespace SpanningTreeIsoperimetry.PrintedElementaryConstants
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem pi_bounds : (3141592653589793 : ℝ)/1000000000000000<Real.pi ∧
    Real.pi<(3141592653589794 : ℝ)/1000000000000000 := by
  constructor <;> linarith [Real.pi_gt_d20,Real.pi_lt_d20]

theorem sqrt_two_bounds : (1414213562373095 : ℝ)/1000000000000000<Real.sqrt 2 ∧
    Real.sqrt 2<(1414213562373096 : ℝ)/1000000000000000 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

theorem entropy_bounds : (11662436 : ℝ)/10000000<SquareMaximality.squareLatticeEntropy ∧
    SquareMaximality.squareLatticeEntropy<(11662437 : ℝ)/10000000 := by
  constructor <;> linarith [NarrowEntropyBounds.entropy_lower,NarrowEntropyBounds.entropy_upper]

private theorem alpha_log_lower : (8813735 : ℝ)/10000000<
    Real.log (1+(1414213562373095 : ℝ)/1000000000000000) := by
  have hs := Real.hasSum_log_one_add (a := (1414213562373095 : ℝ)/1000000000000000) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 12) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  linarith

private theorem alpha_log_upper : Real.log (1+(1414213562373096 : ℝ)/1000000000000000)<
    (8813736 : ℝ)/10000000 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤8813736/10000000) 24
  norm_num [Finset.sum_range_succ,Nat.factorial] at hs
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ)<1+1414213562373096/1000000000000000)).mpr
  linarith

theorem alpha_bounds : (8813735 : ℝ)/10000000<Real.log (1+Real.sqrt 2) ∧
    Real.log (1+Real.sqrt 2)<(8813736 : ℝ)/10000000 := by
  constructor
  · exact alpha_log_lower.trans (Real.log_lt_log (by norm_num)
      (by linarith [sqrt_two_bounds.1]))
  · exact (Real.log_lt_log (show (0 : ℝ)<1+Real.sqrt 2 by positivity)
      (show 1+Real.sqrt 2<1+(1414213562373096 : ℝ)/1000000000000000 by linarith [sqrt_two_bounds.2])).trans alpha_log_upper

end
end SpanningTreeIsoperimetry.PrintedElementaryConstants
