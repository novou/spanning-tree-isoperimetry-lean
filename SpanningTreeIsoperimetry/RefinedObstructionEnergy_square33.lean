import SpanningTreeIsoperimetry.RefinedObstruction_square33
import SpanningTreeIsoperimetry.RefinedPiBounds
import SpanningTreeIsoperimetry.RefinedEntropyBounds

/-! Actual square33 energy threshold for the refined corner envelope. -/
namespace SpanningTreeIsoperimetry.RefinedObstructionEnergy
open CornerEnergy CornerNumericBounds RefinedPiBounds RefinedEntropyBounds
open RefinedObstructionPolynomials
open scoped BigOperators
noncomputable section
namespace square33
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def centered (u : ℝ) : ℝ := (18286486614801716547165126806530353839842618182173356908718172793120383493576371068279/713494672051061024249662967378071698476560413837432861328125000000000000000000000000000000) + (-8495873849794158268719866857208802361621181844694609212021031670424869/8561936064612732290995955608536860381718724966049194335937500000000000)*u^1 + (44712536831239803298022281050733700893782989195486546176/3985192059165199029990844792337156832218170166015625)*u^2 + (-1853874365817285431280926100255854164782874624/51073938038825872354209423065185546875)*u^3 + (130146067423796974269782729947086848/4819941508769989013671875)*u^4 + (-604462909807314587353088/252703749375)*u^5

theorem determinant_centered (t : ℝ) : square33.determinant t=centered (t-center) := by
  unfold square33.determinant centered center
  ring

theorem determinant_upper : square33.determinant (1/Real.pi)<((32036831057/1250000000000000) : ℝ) := by
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

theorem logarithm_lower : ((105704051/10000000) : ℝ)<Real.log ((1250000000000000/32036831057) : ℝ) := by
  have hs := Real.hasSum_log_one_add (a := ((152587890625/128147324228) : ℝ)-1) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 10) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  have he : Real.log ((1250000000000000/32036831057) : ℝ)=15*Real.log 2+Real.log ((152587890625/128147324228) : ℝ) := by
    rw [show ((152587890625/128147324228) : ℝ)=((1250000000000000/32036831057) : ℝ)/2^15 by norm_num,
      Real.log_div (x := ((1250000000000000/32036831057) : ℝ)) (y := (2 : ℝ)^15) (by norm_num) (by norm_num),Real.log_pow]
    ring
  rw [he]
  nlinarith [log_two_lower]

theorem energy_lower : ((7421/100000) : ℝ)<realEnergy square33.diagram := by
  rw [square33.energy_exact]
  have hlog := Real.log_lt_log square33.determinant_pos determinant_upper
  have hl := logarithm_lower
  rw [show ((1250000000000000/32036831057) : ℝ)=((32036831057/1250000000000000) : ℝ)⁻¹ by norm_num,Real.log_inv] at hl
  nlinarith [entropy_upper]

end square33
end
end SpanningTreeIsoperimetry.RefinedObstructionEnergy
