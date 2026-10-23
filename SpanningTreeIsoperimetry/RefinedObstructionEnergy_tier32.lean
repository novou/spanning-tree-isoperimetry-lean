module

public import SpanningTreeIsoperimetry.RefinedObstruction_tier32
public import SpanningTreeIsoperimetry.RefinedPiBounds
public import SpanningTreeIsoperimetry.RefinedEntropyBounds

@[expose] public section

/-! Actual tier32 energy threshold for the refined corner envelope. -/
namespace SpanningTreeIsoperimetry.RefinedObstructionEnergy
open CornerEnergy CornerNumericBounds RefinedPiBounds RefinedEntropyBounds
open RefinedObstructionPolynomials
open scoped BigOperators
noncomputable section
namespace tier32
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def centered (u : ℝ) : ℝ := (440670459127190196704842779380998121548837384142989/162981450557708740234375000000000000000000000000000000) + (-113210891965928119296264313431244787/9778887033462524414062500000000000)*u^1 + (81883456847479404288/16689300537109375)*u^2 + (-134217728/525)*u^3

theorem determinant_centered (t : ℝ) : tier32.determinant t=centered (t-center) := by
  unfold tier32.determinant centered center
  ring

theorem determinant_upper : tier32.determinant (1/Real.pi)<((844939826011/312500000000000) : ℝ) := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  obtain ⟨hl3,hu3⟩ := abs_le.mp (power_bounds 3)
  norm_num [radius] at hl1 hu1 hl2 hu2 hl3 hu3
  rw [determinant_centered]
  unfold centered
  simp only [one_div]
  nlinarith only [hl1,hu1,hl2,hu2,hl3,hu3]

theorem logarithm_lower : ((11810859/2000000) : ℝ)<Real.log ((312500000000000/844939826011) : ℝ) := by
  have hs := Real.hasSum_log_one_add (a := ((1220703125000/844939826011) : ℝ)-1) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 10) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  have he : Real.log ((312500000000000/844939826011) : ℝ)=8*Real.log 2+Real.log ((1220703125000/844939826011) : ℝ) := by
    rw [show ((1220703125000/844939826011) : ℝ)=((312500000000000/844939826011) : ℝ)/2^8 by norm_num,
      Real.log_div (x := ((312500000000000/844939826011) : ℝ)) (y := (2 : ℝ)^8) (by norm_num) (by norm_num),Real.log_pow]
    ring
  rw [he]
  nlinarith [log_two_lower]

theorem energy_lower : ((7421/100000) : ℝ)<realEnergy tier32.diagram := by
  rw [tier32.energy_exact]
  have hlog := Real.log_lt_log tier32.determinant_pos determinant_upper
  have hl := logarithm_lower
  rw [show ((312500000000000/844939826011) : ℝ)=((844939826011/312500000000000) : ℝ)⁻¹ by norm_num,Real.log_inv] at hl
  nlinarith [entropy_upper]

end tier32
end
end SpanningTreeIsoperimetry.RefinedObstructionEnergy
