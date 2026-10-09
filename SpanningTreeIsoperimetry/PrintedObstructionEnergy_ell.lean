import SpanningTreeIsoperimetry.RefinedObstructionEnergy_ell
import SpanningTreeIsoperimetry.NarrowLogCertificates

/-! Literal printed energy interval for ell; every rational certificate is checked. -/
namespace SpanningTreeIsoperimetry.PrintedEnergyBounds.ell
open CornerEnergy RefinedPiBounds NarrowLogCertificates
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private theorem determinant_bounds : (2827224984838 : ℝ)/100000000000000<
    RefinedObstructionPolynomials.ell.determinant (1/Real.pi) ∧
    RefinedObstructionPolynomials.ell.determinant (1/Real.pi)<(2827224984839 : ℝ)/100000000000000 := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  norm_num [radius] at hl1 hu1 hl2 hu2
  rw [RefinedObstructionEnergy.ell.determinant_centered]
  unfold RefinedObstructionEnergy.ell.centered
  simp only [one_div]
  constructor <;> nlinarith only [hl1,hu1,hl2,hu2]

private theorem logarithm_lower : (1166243617/1000000000 : ℝ)*3+671434/10000000<
    Real.log (((2827224984839 : ℝ)/100000000000000)⁻¹) := by
  apply dyadic_lower 5 (by norm_num) (by norm_num)
  norm_num [logSum,Finset.sum_range_succ]

private theorem logarithm_upper : Real.log (((2827224984838 : ℝ)/100000000000000)⁻¹)<
    (1166243615/1000000000 : ℝ)*3+671438/10000000 := by
  apply dyadic_upper 5 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial]

theorem energy_bounds : (671434 : ℝ)/10000000<realEnergy RefinedObstructionPolynomials.ell.diagram ∧
    realEnergy RefinedObstructionPolynomials.ell.diagram<(671438 : ℝ)/10000000 := by
  exact energy_bounds_of_exact (by norm_num : (0 : ℝ)≤3)
    RefinedObstructionPolynomials.ell.energy_exact (by norm_num) determinant_bounds logarithm_lower logarithm_upper

end
end SpanningTreeIsoperimetry.PrintedEnergyBounds.ell
