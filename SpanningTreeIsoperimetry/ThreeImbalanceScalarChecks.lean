module

public import SpanningTreeIsoperimetry.MulticornerEnergyMinimum
public import SpanningTreeIsoperimetry.LargeImbalanceScalarChecks

@[expose] public section

set_option backward.privateInPublic true

/-! The four checked endpoint comparisons covering all multicorner
families with canonical imbalance three. -/
namespace SpanningTreeIsoperimetry.ThreeImbalanceScalarChecks
open Ferrers CornerEnergy RefinedStripEnergy FluxBounds AspectCost
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private theorem pi_upper : Real.pi<(31415927 : ℝ)/10000000 := by linarith [Real.pi_lt_d20]
private theorem pi_cube_upper : Real.pi^3<((31415927 : ℝ)/10000000)^3 := by
  exact pow_lt_pow_left₀ pi_upper Real.pi_pos.le (by decide)

theorem zero_cost : D (6/7)<realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip 4) := by
  have hs := Real.hasSum_log_one_add (a := (3 : ℝ)/7) (by norm_num)
  have hl := sum_le_hasSum (Finset.range 6) (fun n _ => by positivity) hs
  norm_num [D,Finset.sum_range_succ] at hl ⊢
  nlinarith [pi_upper,(strip_energy_bounds_1).1,(strip_energy_bounds_4).1]

theorem one_cost : D (3/4)+fluxBound 8 14 1<realEnergy (horizontalStrip 5) := by
  have hs := Real.hasSum_log_one_add (a := (3 : ℝ)/8) (by norm_num)
  have hl := sum_le_hasSum (Finset.range 6) (fun n _ => by positivity) hs
  norm_num [D,fluxBound,cubic,quadratic,Finset.sum_range_succ] at hl ⊢
  nlinarith [pi_upper,pi_cube_upper,(strip_energy_bounds_5).1]

theorem two_three_cost : realEnergy (horizontalStrip 3)+D (2/3)+fluxBound 10 16 3<
    realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip 6) := by
  have hs := Real.hasSum_log_one_add (a := (1 : ℝ)/3) (by norm_num)
  have hl := sum_le_hasSum (Finset.range 6) (fun n _ => by positivity) hs
  norm_num [D,fluxBound,cubic,quadratic,Finset.sum_range_succ] at hl ⊢
  nlinarith [pi_upper,pi_cube_upper,(strip_energy_bounds_3).2,(strip_energy_bounds_1).1,(strip_energy_bounds_6).1]

theorem long_cost : D (6/11)+fluxBound 13 19 6<realEnergy (horizontalStrip 1) := by
  have hs := Real.hasSum_log_one_add (a := (3 : ℝ)/11) (by norm_num)
  have hl := sum_le_hasSum (Finset.range 6) (fun n _ => by positivity) hs
  norm_num [D,fluxBound,cubic,quadratic,Finset.sum_range_succ] at hl ⊢
  nlinarith [pi_upper,pi_cube_upper,(strip_energy_bounds_1).1]

theorem odd_flux_below_even : fluxBound 17 24 7<fluxBound 13 19 6 := by
  norm_num [fluxBound,cubic,quadratic]
  nlinarith [pow_pos Real.pi_pos 3]

end
end SpanningTreeIsoperimetry.ThreeImbalanceScalarChecks
