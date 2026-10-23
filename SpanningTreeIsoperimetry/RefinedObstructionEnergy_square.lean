module

public import SpanningTreeIsoperimetry.RefinedObstruction_square
public import SpanningTreeIsoperimetry.RefinedPiBounds
public import SpanningTreeIsoperimetry.RefinedEntropyBounds

@[expose] public section

/-! Actual square energy threshold for the refined corner envelope. -/
namespace SpanningTreeIsoperimetry.RefinedObstructionEnergy
open CornerEnergy CornerNumericBounds RefinedPiBounds RefinedEntropyBounds
open RefinedObstructionPolynomials
open scoped BigOperators
noncomputable section
namespace square
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def centered (u : ℝ) : ℝ := (5439419883364217322241399054854521986294931134142989/611180439591407775878906250000000000000000000000000000) + (-293535105107081941928100250931244787/36670826375484466552734375000000000)*u^1 + (1295101482169752851456/751018524169921875)*u^2 + (-536870912/7875)*u^3

theorem determinant_centered (t : ℝ) : square.determinant t=centered (t-center) := by
  unfold square.determinant SmallGreenPolynomials.squareDet centered center
  ring

theorem determinant_upper : square.determinant (1/Real.pi)<((3559943696497/400000000000000) : ℝ) := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  obtain ⟨hl3,hu3⟩ := abs_le.mp (power_bounds 3)
  norm_num [radius] at hl1 hu1 hl2 hu2 hl3 hu3
  rw [determinant_centered]
  unfold centered
  simp only [one_div]
  nlinarith only [hl1,hu1,hl2,hu2,hl3,hu3]

theorem logarithm_lower : ((11804289/2500000) : ℝ)<Real.log ((400000000000000/3559943696497) : ℝ) := by
  have hs := Real.hasSum_log_one_add (a := ((6250000000000/3559943696497) : ℝ)-1) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 10) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  have he : Real.log ((400000000000000/3559943696497) : ℝ)=6*Real.log 2+Real.log ((6250000000000/3559943696497) : ℝ) := by
    rw [show ((6250000000000/3559943696497) : ℝ)=((400000000000000/3559943696497) : ℝ)/2^6 by norm_num,
      Real.log_div (x := ((400000000000000/3559943696497) : ℝ)) (y := (2 : ℝ)^6) (by norm_num) (by norm_num),Real.log_pow]
    ring
  rw [he]
  nlinarith [log_two_lower]

theorem energy_lower : ((2837/50000) : ℝ)<realEnergy square.diagram := by
  rw [square.energy_exact]
  have hlog := Real.log_lt_log square.determinant_pos determinant_upper
  have hl := logarithm_lower
  rw [show ((400000000000000/3559943696497) : ℝ)=((3559943696497/400000000000000) : ℝ)⁻¹ by norm_num,Real.log_inv] at hl
  nlinarith [entropy_upper]

end square
end
end SpanningTreeIsoperimetry.RefinedObstructionEnergy
