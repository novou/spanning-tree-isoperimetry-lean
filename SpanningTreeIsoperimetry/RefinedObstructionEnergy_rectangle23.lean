import SpanningTreeIsoperimetry.RefinedObstruction_rectangle23
import SpanningTreeIsoperimetry.RefinedPiBounds
import SpanningTreeIsoperimetry.RefinedEntropyBounds

/-! Actual rectangle23 energy threshold for the refined corner envelope. -/
namespace SpanningTreeIsoperimetry.RefinedObstructionEnergy
open CornerEnergy CornerNumericBounds RefinedPiBounds RefinedEntropyBounds
open RefinedObstructionPolynomials
open scoped BigOperators
noncomputable section
namespace rectangle23
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def centered (u : ℝ) : ℝ := (14676821999570221958716009694408622118775151403723413602172012233347/17136292385089291201438754796981811523437500000000000000000000000000000) + (-1293052913971440671721878027696986483194151461956671/128522192888169684010790660977363586425781250000000)*u^1 + (108367063959536991307030906953594661888/10528538041398860514163970947265625)*u^2 + (-44075101512744322188967936/15771389007568359375)*u^3 + (140737488355328/1157625)*u^4

theorem determinant_centered (t : ℝ) : rectangle23.determinant t=centered (t-center) := by
  unfold rectangle23.determinant SmallGreenPolynomials.rectangleDet centered center
  ring

theorem determinant_upper : rectangle23.determinant (1/Real.pi)<((2141189831171/2500000000000000) : ℝ) := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  obtain ⟨hl3,hu3⟩ := abs_le.mp (power_bounds 3)
  obtain ⟨hl4,hu4⟩ := abs_le.mp (power_bounds 4)
  norm_num [radius] at hl1 hu1 hl2 hu2 hl3 hu3 hl4 hu4
  rw [determinant_centered]
  unfold centered
  simp only [one_div]
  nlinarith only [hl1,hu1,hl2,hu2,hl3,hu3,hl4,hu4]

theorem logarithm_lower : ((35313417/5000000) : ℝ)<Real.log ((2500000000000000/2141189831171) : ℝ) := by
  have hs := Real.hasSum_log_one_add (a := ((2441406250000/2141189831171) : ℝ)-1) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 10) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  have he : Real.log ((2500000000000000/2141189831171) : ℝ)=10*Real.log 2+Real.log ((2441406250000/2141189831171) : ℝ) := by
    rw [show ((2441406250000/2141189831171) : ℝ)=((2500000000000000/2141189831171) : ℝ)/2^10 by norm_num,
      Real.log_div (x := ((2500000000000000/2141189831171) : ℝ)) (y := (2 : ℝ)^10) (by norm_num) (by norm_num),Real.log_pow]
    ring
  rw [he]
  nlinarith [log_two_lower]

theorem energy_lower : ((3261/50000) : ℝ)<realEnergy rectangle23.diagram := by
  rw [rectangle23.energy_exact]
  have hlog := Real.log_lt_log rectangle23.determinant_pos determinant_upper
  have hl := logarithm_lower
  rw [show ((2500000000000000/2141189831171) : ℝ)=((2141189831171/2500000000000000) : ℝ)⁻¹ by norm_num,Real.log_inv] at hl
  nlinarith [entropy_upper]

end rectangle23
end
end SpanningTreeIsoperimetry.RefinedObstructionEnergy
