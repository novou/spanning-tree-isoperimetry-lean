import SpanningTreeIsoperimetry.RefinedObstruction_tier41
import SpanningTreeIsoperimetry.RefinedPiBounds
import SpanningTreeIsoperimetry.RefinedEntropyBounds

/-! Actual tier41 energy threshold for the refined corner envelope. -/
namespace SpanningTreeIsoperimetry.RefinedObstructionEnergy
open CornerEnergy CornerNumericBounds RefinedPiBounds RefinedEntropyBounds
open RefinedObstructionPolynomials
open scoped BigOperators
noncomputable section
namespace tier41
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def centered (u : ℝ) : ℝ := (348373042718827066023544698542737071612728016010192990286466827201069/128522192888169684010790660977363586425781250000000000000000000000000000) + (-1571876975451701894295953201167870112539032601369822361/7711331573290181040647439658641815185546875000000000)*u^1 + (322603657275729550322565776724606616576/5849187800777144730091094970703125)*u^2 + (-670529826928537891254566912/183999538421630859375)*u^3 + (562949953421312/17364375)*u^4

theorem determinant_centered (t : ℝ) : tier41.determinant t=centered (t-center) := by
  unfold tier41.determinant centered center
  ring

theorem determinant_upper : tier41.determinant (1/Real.pi)<((27106061209363/10000000000000000) : ℝ) := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  obtain ⟨hl3,hu3⟩ := abs_le.mp (power_bounds 3)
  obtain ⟨hl4,hu4⟩ := abs_le.mp (power_bounds 4)
  norm_num [radius] at hl1 hu1 hl2 hu2 hl3 hu3 hl4 hu4
  rw [determinant_centered]
  unfold centered
  simp only [one_div]
  nlinarith only [hl1,hu1,hl2,hu2,hl3,hu3,hl4,hu4]

theorem logarithm_lower : ((11810859/2000000) : ℝ)<Real.log ((10000000000000000/27106061209363) : ℝ) := by
  have hs := Real.hasSum_log_one_add (a := ((39062500000000/27106061209363) : ℝ)-1) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 10) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  have he : Real.log ((10000000000000000/27106061209363) : ℝ)=8*Real.log 2+Real.log ((39062500000000/27106061209363) : ℝ) := by
    rw [show ((39062500000000/27106061209363) : ℝ)=((10000000000000000/27106061209363) : ℝ)/2^8 by norm_num,
      Real.log_div (x := ((10000000000000000/27106061209363) : ℝ)) (y := (2 : ℝ)^8) (by norm_num) (by norm_num),Real.log_pow]
    ring
  rw [he]
  nlinarith [log_two_lower]

theorem energy_lower : ((7421/100000) : ℝ)<realEnergy tier41.diagram := by
  rw [tier41.energy_exact]
  have hlog := Real.log_lt_log tier41.determinant_pos determinant_upper
  have hl := logarithm_lower
  rw [show ((10000000000000000/27106061209363) : ℝ)=((27106061209363/10000000000000000) : ℝ)⁻¹ by norm_num,Real.log_inv] at hl
  nlinarith [entropy_upper]

end tier41
end
end SpanningTreeIsoperimetry.RefinedObstructionEnergy
