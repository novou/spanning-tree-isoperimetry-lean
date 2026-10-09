import SpanningTreeIsoperimetry.RefinedObstructionEnergy_tier311
import SpanningTreeIsoperimetry.NarrowLogCertificates

/-! Literal printed energy interval for tier311; every rational certificate is checked. -/
namespace SpanningTreeIsoperimetry.PrintedEnergyBounds.tier311
open CornerEnergy RefinedPiBounds NarrowLogCertificates
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private theorem determinant_bounds : (269500013406 : ℝ)/100000000000000<
    RefinedObstructionPolynomials.tier311.determinant (1/Real.pi) ∧
    RefinedObstructionPolynomials.tier311.determinant (1/Real.pi)<(269500013407 : ℝ)/100000000000000 := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  obtain ⟨hl3,hu3⟩ := abs_le.mp (power_bounds 3)
  norm_num [radius] at hl1 hu1 hl2 hu2 hl3 hu3
  rw [RefinedObstructionEnergy.tier311.determinant_centered]
  unfold RefinedObstructionEnergy.tier311.centered
  simp only [one_div]
  constructor <;> nlinarith only [hl1,hu1,hl2,hu2,hl3,hu3]

private theorem logarithm_lower : (1166243617/1000000000 : ℝ)*5+851385/10000000<
    Real.log (((269500013407 : ℝ)/100000000000000)⁻¹) := by
  apply dyadic_lower 8 (by norm_num) (by norm_num)
  norm_num [logSum,Finset.sum_range_succ]

private theorem logarithm_upper : Real.log (((269500013406 : ℝ)/100000000000000)⁻¹)<
    (1166243615/1000000000 : ℝ)*5+851391/10000000 := by
  apply dyadic_upper 8 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial]

theorem energy_bounds : (851385 : ℝ)/10000000<realEnergy RefinedObstructionPolynomials.tier311.diagram ∧
    realEnergy RefinedObstructionPolynomials.tier311.diagram<(851391 : ℝ)/10000000 := by
  exact energy_bounds_of_exact (by norm_num : (0 : ℝ)≤5)
    RefinedObstructionPolynomials.tier311.energy_exact (by norm_num) determinant_bounds logarithm_lower logarithm_upper

end
end SpanningTreeIsoperimetry.PrintedEnergyBounds.tier311
