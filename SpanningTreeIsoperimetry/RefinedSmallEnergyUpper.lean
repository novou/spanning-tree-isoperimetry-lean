import SpanningTreeIsoperimetry.RefinedObstructionEnergy_ell
import SpanningTreeIsoperimetry.RefinedObstructionEnergy_square
import SpanningTreeIsoperimetry.RefinedStripEnergy

/-! Modest actual upper bounds needed to select the exact size-three and
size-four nonconcentrated energy baselines. -/
namespace SpanningTreeIsoperimetry.RefinedSmallEnergyUpper
open Ferrers CornerEnergy RefinedPiBounds RefinedEntropyBounds RefinedStripEnergy
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private theorem square_det_lower : (889 : ℝ)/100000<
    RefinedObstructionPolynomials.square.determinant (1/Real.pi) := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  obtain ⟨hl3,hu3⟩ := abs_le.mp (power_bounds 3)
  norm_num [radius] at hl1 hu1 hl2 hu2 hl3 hu3
  rw [RefinedObstructionEnergy.square.determinant_centered]
  unfold RefinedObstructionEnergy.square.centered
  simp only [one_div]
  nlinarith only [hl1,hu1,hl2,hu2,hl3,hu3]

private theorem ell_det_lower : (2827 : ℝ)/100000<
    RefinedObstructionPolynomials.ell.determinant (1/Real.pi) := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  norm_num [radius] at hl1 hu1 hl2 hu2
  rw [RefinedObstructionEnergy.ell.determinant_centered]
  unfold RefinedObstructionEnergy.ell.centered
  simp only [one_div]
  nlinarith only [hl1,hu1,hl2,hu2]

private theorem square_log_upper : Real.log ((100000 : ℝ)/889)<47239/10000 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤47239/10000) 32
  norm_num [Finset.sum_range_succ,Nat.factorial] at hs
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ)<100000/889)).mpr
  linarith

private theorem ell_log_upper : Real.log ((100000 : ℝ)/2827)<3566/1000 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤3566/1000) 32
  norm_num [Finset.sum_range_succ,Nat.factorial] at hs
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ)<100000/2827)).mpr
  linarith

theorem square_energy_upper : realEnergy (faceRectangle 2 2)<(59 : ℝ)/1000 := by
  have he := RefinedObstructionPolynomials.square.energy_exact
  change realEnergy (faceRectangle 2 2)=_ at he
  have hd := Real.log_lt_log (by norm_num : (0 : ℝ)<889/100000) square_det_lower
  have hl := square_log_upper
  rw [show (100000 : ℝ)/889=(889/100000 : ℝ)⁻¹ by norm_num,Real.log_inv] at hl
  linarith [entropy_lower]

theorem ell_energy_upper : realEnergy threeCell<(17 : ℝ)/250 := by
  have he := RefinedObstructionPolynomials.ell.energy_exact
  have hshape : RefinedObstructionPolynomials.ell.diagram=threeCell := by decide +kernel
  rw [hshape] at he
  have hd := Real.log_lt_log (by norm_num : (0 : ℝ)<2827/100000) ell_det_lower
  have hl := ell_log_upper
  rw [show (100000 : ℝ)/2827=(2827/100000 : ℝ)⁻¹ by norm_num,Real.log_inv] at hl
  linarith [entropy_lower]

theorem ell_lt_singleton_pair : realEnergy threeCell<
    realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip 2) := by
  linarith [ell_energy_upper,(strip_energy_bounds_1).1,(strip_energy_bounds_2).1]

end
end SpanningTreeIsoperimetry.RefinedSmallEnergyUpper
