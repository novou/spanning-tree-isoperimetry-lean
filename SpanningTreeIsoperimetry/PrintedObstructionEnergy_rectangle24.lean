import SpanningTreeIsoperimetry.RefinedObstructionEnergy_rectangle24
import SpanningTreeIsoperimetry.NarrowLogCertificates

/-! Literal printed energy interval for rectangle24; every rational certificate is checked. -/
namespace SpanningTreeIsoperimetry.PrintedEnergyBounds.rectangle24
open CornerEnergy RefinedPiBounds NarrowLogCertificates
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private theorem determinant_bounds : (8268330326 : ℝ)/100000000000000<
    RefinedObstructionPolynomials.rectangle24.determinant (1/Real.pi) ∧
    RefinedObstructionPolynomials.rectangle24.determinant (1/Real.pi)<(8268330327 : ℝ)/100000000000000 := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  obtain ⟨hl3,hu3⟩ := abs_le.mp (power_bounds 3)
  obtain ⟨hl4,hu4⟩ := abs_le.mp (power_bounds 4)
  obtain ⟨hl5,hu5⟩ := abs_le.mp (power_bounds 5)
  norm_num [radius] at hl1 hu1 hl2 hu2 hl3 hu3 hl4 hu4 hl5 hu5
  rw [RefinedObstructionEnergy.rectangle24.determinant_centered]
  unfold RefinedObstructionEnergy.rectangle24.centered
  simp only [one_div]
  constructor <;> nlinarith only [hl1,hu1,hl2,hu2,hl3,hu3,hl4,hu4,hl5,hu5]

private theorem logarithm_lower : (1166243617/1000000000 : ℝ)*8+705432/10000000<
    Real.log (((8268330327 : ℝ)/100000000000000)⁻¹) := by
  apply dyadic_lower 13 (by norm_num) (by norm_num)
  norm_num [logSum,Finset.sum_range_succ]

private theorem logarithm_upper : Real.log (((8268330326 : ℝ)/100000000000000)⁻¹)<
    (1166243615/1000000000 : ℝ)*8+705441/10000000 := by
  apply dyadic_upper 13 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial]

theorem energy_bounds : (705432 : ℝ)/10000000<realEnergy RefinedObstructionPolynomials.rectangle24.diagram ∧
    realEnergy RefinedObstructionPolynomials.rectangle24.diagram<(705441 : ℝ)/10000000 := by
  exact energy_bounds_of_exact (by norm_num : (0 : ℝ)≤8)
    RefinedObstructionPolynomials.rectangle24.energy_exact (by norm_num) determinant_bounds logarithm_lower logarithm_upper

end
end SpanningTreeIsoperimetry.PrintedEnergyBounds.rectangle24
