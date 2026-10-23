module

public import SpanningTreeIsoperimetry.RefinedObstructionEnergy_square
public import SpanningTreeIsoperimetry.NarrowLogCertificates

@[expose] public section

set_option backward.privateInPublic true

/-! Literal printed energy interval for square; every rational certificate is checked. -/
namespace SpanningTreeIsoperimetry.PrintedEnergyBounds.square
open CornerEnergy RefinedPiBounds NarrowLogCertificates
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private theorem determinant_bounds : (889985924124 : ℝ)/100000000000000<
    RefinedObstructionPolynomials.square.determinant (1/Real.pi) ∧
    RefinedObstructionPolynomials.square.determinant (1/Real.pi)<(889985924125 : ℝ)/100000000000000 := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  obtain ⟨hl3,hu3⟩ := abs_le.mp (power_bounds 3)
  norm_num [radius] at hl1 hu1 hl2 hu2 hl3 hu3
  rw [RefinedObstructionEnergy.square.determinant_centered]
  unfold RefinedObstructionEnergy.square.centered
  simp only [one_div]
  constructor <;> nlinarith only [hl1,hu1,hl2,hu2,hl3,hu3]

private theorem logarithm_lower : (1166243617/1000000000 : ℝ)*4+567450/10000000<
    Real.log (((889985924125 : ℝ)/100000000000000)⁻¹) := by
  apply dyadic_lower 6 (by norm_num) (by norm_num)
  norm_num [logSum,Finset.sum_range_succ]

private theorem logarithm_upper : Real.log (((889985924124 : ℝ)/100000000000000)⁻¹)<
    (1166243615/1000000000 : ℝ)*4+567455/10000000 := by
  apply dyadic_upper 6 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial]

theorem energy_bounds : (567450 : ℝ)/10000000<realEnergy RefinedObstructionPolynomials.square.diagram ∧
    realEnergy RefinedObstructionPolynomials.square.diagram<(567455 : ℝ)/10000000 := by
  exact energy_bounds_of_exact (by norm_num : (0 : ℝ)≤4)
    RefinedObstructionPolynomials.square.energy_exact (by norm_num) determinant_bounds logarithm_lower logarithm_upper

end
end SpanningTreeIsoperimetry.PrintedEnergyBounds.square
