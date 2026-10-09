import SpanningTreeIsoperimetry.RefinedObstruction_ell
import SpanningTreeIsoperimetry.RefinedPiBounds
import SpanningTreeIsoperimetry.RefinedEntropyBounds

/-! Actual ell energy threshold for the refined corner envelope. -/
namespace SpanningTreeIsoperimetry.RefinedObstructionEnergy
open CornerEnergy CornerNumericBounds RefinedPiBounds RefinedEntropyBounds
open RefinedObstructionPolynomials
open scoped BigOperators
noncomputable section
namespace ell
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def centered (u : ℝ) : ℝ := (97065066770729283075968312810414929/3433227539062500000000000000000000000) + (-344271315810466423/34332275390625000)*u^1 + (32768/45)*u^2

theorem determinant_centered (t : ℝ) : ell.determinant t=centered (t-center) := by
  unfold ell.determinant ThreeCellEnergy.ellDet centered center
  ring

theorem determinant_upper : ell.determinant (1/Real.pi)<((141361249241923/5000000000000000) : ℝ) := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  norm_num [radius] at hl1 hu1 hl2 hu2
  rw [determinant_centered]
  unfold centered
  simp only [one_div]
  nlinarith only [hl1,hu1,hl2,hu2]

theorem logarithm_lower : ((35658717/10000000) : ℝ)<Real.log ((5000000000000000/141361249241923) : ℝ) := by
  have hs := Real.hasSum_log_one_add (a := ((156250000000000/141361249241923) : ℝ)-1) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 10) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  have he : Real.log ((5000000000000000/141361249241923) : ℝ)=5*Real.log 2+Real.log ((156250000000000/141361249241923) : ℝ) := by
    rw [show ((156250000000000/141361249241923) : ℝ)=((5000000000000000/141361249241923) : ℝ)/2^5 by norm_num,
      Real.log_div (x := ((5000000000000000/141361249241923) : ℝ)) (y := (2 : ℝ)^5) (by norm_num) (by norm_num),Real.log_pow]
    ring
  rw [he]
  nlinarith [log_two_lower]

theorem energy_lower : ((3357/50000) : ℝ)<realEnergy ell.diagram := by
  rw [ell.energy_exact]
  have hlog := Real.log_lt_log ell.determinant_pos determinant_upper
  have hl := logarithm_lower
  rw [show ((5000000000000000/141361249241923) : ℝ)=((141361249241923/5000000000000000) : ℝ)⁻¹ by norm_num,Real.log_inv] at hl
  nlinarith [entropy_upper]

end ell
end
end SpanningTreeIsoperimetry.RefinedObstructionEnergy
