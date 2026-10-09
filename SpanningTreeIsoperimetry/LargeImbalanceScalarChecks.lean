import SpanningTreeIsoperimetry.StripSupportingLines
import SpanningTreeIsoperimetry.FluxBounds
import SpanningTreeIsoperimetry.AspectCost
import SpanningTreeIsoperimetry.UniformStripEnergy

/-! Checked scalar majorants for the large-imbalance comparison. These use
actual strip energies and the actual rational flux definition. The hull and
finite-count interfaces are assembled separately. -/
namespace SpanningTreeIsoperimetry.LargeImbalanceScalarChecks
open Ferrers CornerEnergy RefinedStripEnergy StripSupportingLines FluxBounds AspectCost
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def fluxCap (T : ℝ) : ℝ := 8*Real.pi^3/(45*T^4*(T+1))
def upperFour (j : ℕ) : ℝ :=
  if j≤1 then 149681/5000000 else if j≤3 then 18549/400000 else ((j : ℝ)+27)/600
def upperFive (j : ℕ) : ℝ :=
  if j≤3 then 18549/400000 else ((j : ℝ)+27)/600

private theorem pi_upper : Real.pi<(31415927 : ℝ)/10000000 := by
  linarith [Real.pi_lt_d20]

private theorem pi_cube_upper : Real.pi^3<((31415927 : ℝ)/10000000)^3 := by
  have hh := pi_upper
  gcongr

theorem four_cost_checked (j : Fin 10) :
    upperFour j.val+D (8/(13+(j.val : ℝ)))+fluxBound 22 30 9 <
      if j.val≤1 then (7054 : ℝ)/100000 else 7421/100000 := by
  have hs := Real.hasSum_log_one_add (a := 4/(13+(j.val : ℝ))) (by positivity)
  have hl := sum_le_hasSum (Finset.range 6) (fun n _ => by positivity) hs
  fin_cases j <;>
    norm_num [upperFour,D,fluxBound,cubic,quadratic,Finset.sum_range_succ] at hl ⊢ <;>
    nlinarith [pi_upper,pi_cube_upper]

theorem five_cost_checked (j : Fin 12) :
    upperFive j.val+D (10/(21+(j.val : ℝ)))+fluxCap 5 < (7421 : ℝ)/100000 := by
  have hs := Real.hasSum_log_one_add (a := 5/(21+(j.val : ℝ))) (by positivity)
  have hl := sum_le_hasSum (Finset.range 6) (fun n _ => by positivity) hs
  fin_cases j <;>
    norm_num [upperFive,D,fluxCap,Finset.sum_range_succ] at hl ⊢ <;>
    nlinarith [pi_upper,pi_cube_upper]

theorem tail_cost_checked : (81 : ℝ)/1250+D (12/43)+fluxCap 6 < (7421 : ℝ)/100000 := by
  have hs := Real.hasSum_log_one_add (a := (6 : ℝ)/43) (by norm_num)
  have hl := sum_le_hasSum (Finset.range 6) (fun n _ => by positivity) hs
  norm_num [D,fluxCap,Finset.sum_range_succ] at hl ⊢
  nlinarith [pi_upper,pi_cube_upper]

theorem strip_lt_upperFour (j : ℕ) : realEnergy (horizontalStrip j)<upperFour j := by
  unfold upperFour
  split_ifs with h1 h3
  · exact (realEnergy_strip_monotone h1).trans_lt (strip_energy_bounds_1).2
  · exact (realEnergy_strip_monotone h3).trans_lt (strip_energy_bounds_3).2
  · exact strip_supporting_line j

theorem strip_lt_upperFive (j : ℕ) : realEnergy (horizontalStrip j)<upperFive j := by
  unfold upperFive
  split_ifs with h3
  · exact (realEnergy_strip_monotone h3).trans_lt (strip_energy_bounds_3).2
  · exact strip_supporting_line j

theorem actual_four_cost (j : Fin 10) :
    realEnergy (horizontalStrip j.val)+D (8/(13+(j.val : ℝ)))+fluxBound 22 30 9 <
      if j.val≤1 then (7054 : ℝ)/100000 else 7421/100000 := by
  linarith [strip_lt_upperFour j.val,four_cost_checked j]

theorem actual_five_cost (j : Fin 12) :
    realEnergy (horizontalStrip j.val)+D (10/(21+(j.val : ℝ)))+fluxCap 5 <
      (7421 : ℝ)/100000 := by
  linarith [strip_lt_upperFive j.val,five_cost_checked j]

theorem actual_tail_cost (j : ℕ) :
    realEnergy (horizontalStrip j)+D (12/43)+fluxCap 6 < (7421 : ℝ)/100000 := by
  linarith [UniformStripEnergy.realEnergy_strip_lt j,tail_cost_checked]

theorem aspect_ratio_five {T j : ℝ} (hT : 5≤T) (hj : 0≤j) (hj11 : j≤11) :
    2*T/(T^2-T+j+1)≤10/(21+j) := by
  have hden : 0<T^2-T+j+1 := by nlinarith [sq_nonneg (T-1)]
  apply (div_le_div_iff₀ hden (by linarith : 0<21+j)).mpr
  have hp := mul_nonneg (show 0≤T-5 by linarith) (show 0≤5*T-j-1 by linarith)
  nlinarith

theorem aspect_ratio_tail {T j : ℝ} (hT : 6≤T) (hj : 12≤j) :
    2*T/(T^2-T+j+1)≤12/43 := by
  have hden : 0<T^2-T+j+1 := by nlinarith [sq_nonneg (T-1)]
  apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ)<43)).mpr
  have hp := mul_nonneg (show 0≤T-6 by linarith) (show 0≤12*T-26 by linarith)
  nlinarith

theorem fluxCap_antitone {a b : ℝ} (ha : 0<a) (hab : a≤b) : fluxCap b≤fluxCap a := by
  unfold fluxCap
  gcongr

end
end SpanningTreeIsoperimetry.LargeImbalanceScalarChecks
