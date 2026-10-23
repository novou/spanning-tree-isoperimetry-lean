module

public import SpanningTreeIsoperimetry.RefinedObstructionEnergy_tier41
public import SpanningTreeIsoperimetry.NarrowLogCertificates

@[expose] public section

set_option backward.privateInPublic true

/-! Literal printed energy interval for tier41; every rational certificate is checked. -/
namespace SpanningTreeIsoperimetry.PrintedEnergyBounds.tier41
open CornerEnergy RefinedPiBounds NarrowLogCertificates
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private theorem determinant_bounds : (271060612093 : ℝ)/100000000000000<
    RefinedObstructionPolynomials.tier41.determinant (1/Real.pi) ∧
    RefinedObstructionPolynomials.tier41.determinant (1/Real.pi)<(271060612094 : ℝ)/100000000000000 := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  obtain ⟨hl3,hu3⟩ := abs_le.mp (power_bounds 3)
  obtain ⟨hl4,hu4⟩ := abs_le.mp (power_bounds 4)
  norm_num [radius] at hl1 hu1 hl2 hu2 hl3 hu3 hl4 hu4
  rw [RefinedObstructionEnergy.tier41.determinant_centered]
  unfold RefinedObstructionEnergy.tier41.centered
  simp only [one_div]
  constructor <;> nlinarith only [hl1,hu1,hl2,hu2,hl3,hu3,hl4,hu4]

private theorem logarithm_lower : (1166243617/1000000000 : ℝ)*5+793645/10000000<
    Real.log (((271060612094 : ℝ)/100000000000000)⁻¹) := by
  apply dyadic_lower 8 (by norm_num) (by norm_num)
  norm_num [logSum,Finset.sum_range_succ]

private theorem logarithm_upper : Real.log (((271060612093 : ℝ)/100000000000000)⁻¹)<
    (1166243615/1000000000 : ℝ)*5+793651/10000000 := by
  apply dyadic_upper 8 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial]

theorem energy_bounds : (793645 : ℝ)/10000000<realEnergy RefinedObstructionPolynomials.tier41.diagram ∧
    realEnergy RefinedObstructionPolynomials.tier41.diagram<(793651 : ℝ)/10000000 := by
  exact energy_bounds_of_exact (by norm_num : (0 : ℝ)≤5)
    RefinedObstructionPolynomials.tier41.energy_exact (by norm_num) determinant_bounds logarithm_lower logarithm_upper

end
end SpanningTreeIsoperimetry.PrintedEnergyBounds.tier41
