module

public import SpanningTreeIsoperimetry.RefinedObstruction_rectangle24
public import SpanningTreeIsoperimetry.RefinedPiBounds
public import SpanningTreeIsoperimetry.RefinedEntropyBounds

@[expose] public section

/-! Actual rectangle24 energy threshold for the refined corner envelope. -/
namespace SpanningTreeIsoperimetry.RefinedObstructionEnergy
open CornerEnergy CornerNumericBounds RefinedPiBounds RefinedEntropyBounds
open RefinedObstructionPolynomials
open scoped BigOperators
noncomputable section
namespace rectangle24
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def centered (u : ℝ) : ℝ := (42326759179037417136559981102345271572914097896040713987010979667692041851213003017/511914225801941104770963544834394554072787286713719367980957031250000000000000000000000) + (-15611914964782722837851282690152704102865153617013551937080161250299/651527196475197769708499057061956705183547455817461013793945312500)*u^1 + (3331556335727595561659958066644162954728581126745356500992/18787333993207366855671125449589453637599945068359375)*u^2 + (-27192489789389217110086935942787835935380733952/196999475292614079080522060394287109375)*u^3 + (4564311901272340162156621931216896/187789928913116455078125)*u^4 + (-75557863725914323419136/108301606875)*u^5

theorem determinant_centered (t : ℝ) : rectangle24.determinant t=centered (t-center) := by
  unfold rectangle24.determinant centered center
  ring

theorem determinant_upper : rectangle24.determinant (1/Real.pi)<((413416516339/5000000000000000) : ℝ) := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  obtain ⟨hl3,hu3⟩ := abs_le.mp (power_bounds 3)
  obtain ⟨hl4,hu4⟩ := abs_le.mp (power_bounds 4)
  obtain ⟨hl5,hu5⟩ := abs_le.mp (power_bounds 5)
  norm_num [radius] at hl1 hu1 hl2 hu2 hl3 hu3 hl4 hu4 hl5 hu5
  rw [determinant_centered]
  unfold centered
  simp only [one_div]
  nlinarith only [hl1,hu1,hl2,hu2,hl3,hu3,hl4,hu4,hl5,hu5]

theorem logarithm_lower : ((5875307/625000) : ℝ)<Real.log ((5000000000000000/413416516339) : ℝ) := by
  have hs := Real.hasSum_log_one_add (a := ((610351562500/413416516339) : ℝ)-1) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 10) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  have he : Real.log ((5000000000000000/413416516339) : ℝ)=13*Real.log 2+Real.log ((610351562500/413416516339) : ℝ) := by
    rw [show ((610351562500/413416516339) : ℝ)=((5000000000000000/413416516339) : ℝ)/2^13 by norm_num,
      Real.log_div (x := ((5000000000000000/413416516339) : ℝ)) (y := (2 : ℝ)^13) (by norm_num) (by norm_num),Real.log_pow]
    ring
  rw [he]
  nlinarith [log_two_lower]

theorem energy_lower : ((3527/50000) : ℝ)<realEnergy rectangle24.diagram := by
  rw [rectangle24.energy_exact]
  have hlog := Real.log_lt_log rectangle24.determinant_pos determinant_upper
  have hl := logarithm_lower
  rw [show ((5000000000000000/413416516339) : ℝ)=((413416516339/5000000000000000) : ℝ)⁻¹ by norm_num,Real.log_inv] at hl
  nlinarith [entropy_upper]

end rectangle24
end
end SpanningTreeIsoperimetry.RefinedObstructionEnergy
