module

public import SpanningTreeIsoperimetry.RefinedStripEnclosures
public import SpanningTreeIsoperimetry.NarrowLogCertificates

@[expose] public section

set_option backward.privateInPublic true

/-! Literal printed interval for the actual strip of length3. -/
namespace SpanningTreeIsoperimetry.PrintedEnergyBounds.strip3
open Ferrers CornerEnergy RefinedQuadrantBoundary RefinedStripPolynomials RefinedStripEnclosures
open NarrowLogCertificates
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private theorem logarithm_lower : (1166243617/1000000000 : ℝ)*3+463698/10000000<
    Real.log (((288657089 : ℝ)/10000000000)⁻¹) := by
  apply dyadic_lower 5 (by norm_num) (by norm_num)
  norm_num [logSum,Finset.sum_range_succ]

private theorem logarithm_upper : Real.log (((288657088 : ℝ)/10000000000)⁻¹)<
    (1166243615/1000000000 : ℝ)*3+463702/10000000 := by
  apply dyadic_upper 5 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial]

theorem energy_bounds : (463698 : ℝ)/10000000<realEnergy (horizontalStrip 3) ∧
    realEnergy (horizontalStrip 3)<(463702 : ℝ)/10000000 := by
  have he := strip_energy_exact (by decide : 3≤6)
  rw [stripMatrix_det_3] at he
  have he' : realEnergy (horizontalStrip 3)= -Real.log (stripDet3 (1/Real.pi))-
      3*SquareMaximality.squareLatticeEntropy := by
    simpa only [Nat.cast_ofNat,Nat.cast_one,mul_comm] using he
  exact energy_bounds_of_exact (by norm_num : (0 : ℝ)≤3) he'
    (by norm_num) stripDet3_bounds logarithm_lower logarithm_upper

end
end SpanningTreeIsoperimetry.PrintedEnergyBounds.strip3
