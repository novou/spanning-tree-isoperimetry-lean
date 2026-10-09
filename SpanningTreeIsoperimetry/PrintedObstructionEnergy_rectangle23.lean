import SpanningTreeIsoperimetry.RefinedObstructionEnergy_rectangle23
import SpanningTreeIsoperimetry.NarrowLogCertificates

/-! Literal printed energy interval for rectangle23; every rational certificate is checked. -/
namespace SpanningTreeIsoperimetry.PrintedEnergyBounds.rectangle23
open CornerEnergy RefinedPiBounds NarrowLogCertificates
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private theorem determinant_bounds : (85647593246 : ℝ)/100000000000000<
    RefinedObstructionPolynomials.rectangle23.determinant (1/Real.pi) ∧
    RefinedObstructionPolynomials.rectangle23.determinant (1/Real.pi)<(85647593247 : ℝ)/100000000000000 := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  obtain ⟨hl3,hu3⟩ := abs_le.mp (power_bounds 3)
  obtain ⟨hl4,hu4⟩ := abs_le.mp (power_bounds 4)
  norm_num [radius] at hl1 hu1 hl2 hu2 hl3 hu3 hl4 hu4
  rw [RefinedObstructionEnergy.rectangle23.determinant_centered]
  unfold RefinedObstructionEnergy.rectangle23.centered
  simp only [one_div]
  constructor <;> nlinarith only [hl1,hu1,hl2,hu2,hl3,hu3,hl4,hu4]

private theorem logarithm_lower : (1166243617/1000000000 : ℝ)*6+652221/10000000<
    Real.log (((85647593247 : ℝ)/100000000000000)⁻¹) := by
  apply dyadic_lower 10 (by norm_num) (by norm_num)
  norm_num [logSum,Finset.sum_range_succ]

private theorem logarithm_upper : Real.log (((85647593246 : ℝ)/100000000000000)⁻¹)<
    (1166243615/1000000000 : ℝ)*6+652228/10000000 := by
  apply dyadic_upper 10 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial]

theorem energy_bounds : (652221 : ℝ)/10000000<realEnergy RefinedObstructionPolynomials.rectangle23.diagram ∧
    realEnergy RefinedObstructionPolynomials.rectangle23.diagram<(652228 : ℝ)/10000000 := by
  exact energy_bounds_of_exact (by norm_num : (0 : ℝ)≤6)
    RefinedObstructionPolynomials.rectangle23.energy_exact (by norm_num) determinant_bounds logarithm_lower logarithm_upper

end
end SpanningTreeIsoperimetry.PrintedEnergyBounds.rectangle23
