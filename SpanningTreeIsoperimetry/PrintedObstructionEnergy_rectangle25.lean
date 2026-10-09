import SpanningTreeIsoperimetry.RefinedObstructionEnergy_rectangle25
import SpanningTreeIsoperimetry.NarrowLogCertificates

/-! Literal printed energy interval for rectangle25; every rational certificate is checked. -/
namespace SpanningTreeIsoperimetry.PrintedEnergyBounds.rectangle25
open CornerEnergy RefinedPiBounds NarrowLogCertificates
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private theorem determinant_bounds : (799530479 : ℝ)/100000000000000<
    RefinedObstructionPolynomials.rectangle25.determinant (1/Real.pi) ∧
    RefinedObstructionPolynomials.rectangle25.determinant (1/Real.pi)<(799530480 : ℝ)/100000000000000 := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  obtain ⟨hl3,hu3⟩ := abs_le.mp (power_bounds 3)
  obtain ⟨hl4,hu4⟩ := abs_le.mp (power_bounds 4)
  obtain ⟨hl5,hu5⟩ := abs_le.mp (power_bounds 5)
  obtain ⟨hl6,hu6⟩ := abs_le.mp (power_bounds 6)
  norm_num [radius] at hl1 hu1 hl2 hu2 hl3 hu3 hl4 hu4 hl5 hu5 hl6 hu6
  rw [RefinedObstructionEnergy.rectangle25.determinant_centered]
  unfold RefinedObstructionEnergy.rectangle25.centered
  simp only [one_div]
  constructor <;> nlinarith only [hl1,hu1,hl2,hu2,hl3,hu3,hl4,hu4,hl5,hu5,hl6,hu6]

private theorem logarithm_lower : (1166243617/1000000000 : ℝ)*10+742190/10000000<
    Real.log (((799530480 : ℝ)/100000000000000)⁻¹) := by
  apply dyadic_lower 16 (by norm_num) (by norm_num)
  norm_num [logSum,Finset.sum_range_succ]

private theorem logarithm_upper : Real.log (((799530479 : ℝ)/100000000000000)⁻¹)<
    (1166243615/1000000000 : ℝ)*10+742201/10000000 := by
  apply dyadic_upper 16 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial]

theorem energy_bounds : (742190 : ℝ)/10000000<realEnergy RefinedObstructionPolynomials.rectangle25.diagram ∧
    realEnergy RefinedObstructionPolynomials.rectangle25.diagram<(742201 : ℝ)/10000000 := by
  exact energy_bounds_of_exact (by norm_num : (0 : ℝ)≤10)
    RefinedObstructionPolynomials.rectangle25.energy_exact (by norm_num) determinant_bounds logarithm_lower logarithm_upper

end
end SpanningTreeIsoperimetry.PrintedEnergyBounds.rectangle25
