module

public import SpanningTreeIsoperimetry.RefinedObstruction_tier311
public import SpanningTreeIsoperimetry.RefinedPiBounds
public import SpanningTreeIsoperimetry.RefinedEntropyBounds

@[expose] public section

/-! Actual tier311 energy threshold for the refined corner envelope. -/
namespace SpanningTreeIsoperimetry.RefinedObstructionEnergy
open CornerEnergy CornerNumericBounds RefinedPiBounds RefinedEntropyBounds
open RefinedObstructionPolynomials
open scoped BigOperators
noncomputable section
namespace tier311
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def centered (u : ℝ) : ℝ := (617674262489238505617988437876894072440701605553967/229192664846777915954589843750000000000000000000000000) + (-80866455234838017939757965774994787/4583853296935558319091796875000000)*u^1 + (3109580265336860401664/107288360595703125)*u^2 + (-4294967296/7875)*u^3

theorem determinant_centered (t : ℝ) : tier311.determinant t=centered (t-center) := by
  unfold tier311.determinant centered center
  ring

theorem determinant_upper : tier311.determinant (1/Real.pi)<((2695000134067/1000000000000000) : ℝ) := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  obtain ⟨hl3,hu3⟩ := abs_le.mp (power_bounds 3)
  obtain ⟨hl4,hu4⟩ := abs_le.mp (power_bounds 4)
  norm_num [radius] at hl1 hu1 hl2 hu2 hl3 hu3 hl4 hu4
  rw [determinant_centered]
  unfold centered
  simp only [one_div]
  nlinarith only [hl1,hu1,hl2,hu2,hl3,hu3,hl4,hu4]

theorem logarithm_lower : ((11810859/2000000) : ℝ)<Real.log ((1000000000000000/2695000134067) : ℝ) := by
  have hs := Real.hasSum_log_one_add (a := ((3906250000000/2695000134067) : ℝ)-1) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 10) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  have he : Real.log ((1000000000000000/2695000134067) : ℝ)=8*Real.log 2+Real.log ((3906250000000/2695000134067) : ℝ) := by
    rw [show ((3906250000000/2695000134067) : ℝ)=((1000000000000000/2695000134067) : ℝ)/2^8 by norm_num,
      Real.log_div (x := ((1000000000000000/2695000134067) : ℝ)) (y := (2 : ℝ)^8) (by norm_num) (by norm_num),Real.log_pow]
    ring
  rw [he]
  nlinarith [log_two_lower]

theorem energy_lower : ((7421/100000) : ℝ)<realEnergy tier311.diagram := by
  rw [tier311.energy_exact]
  have hlog := Real.log_lt_log tier311.determinant_pos determinant_upper
  have hl := logarithm_lower
  rw [show ((1000000000000000/2695000134067) : ℝ)=((2695000134067/1000000000000000) : ℝ)⁻¹ by norm_num,Real.log_inv] at hl
  nlinarith [entropy_upper]

end tier311
end
end SpanningTreeIsoperimetry.RefinedObstructionEnergy
