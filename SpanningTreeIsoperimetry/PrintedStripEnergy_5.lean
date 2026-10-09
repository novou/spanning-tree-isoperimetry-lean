import SpanningTreeIsoperimetry.RefinedStripEnclosures
import SpanningTreeIsoperimetry.NarrowLogCertificates

/-! Literal printed interval for the actual strip of length5. -/
namespace SpanningTreeIsoperimetry.PrintedEnergyBounds.strip5
open Ferrers CornerEnergy RefinedQuadrantBoundary RefinedStripPolynomials RefinedStripEnclosures
open NarrowLogCertificates
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

private theorem logarithm_lower : (1166243617/1000000000 : ℝ)*5+520012/10000000<
    Real.log (((27858012 : ℝ)/10000000000)⁻¹) := by
  apply dyadic_lower 8 (by norm_num) (by norm_num)
  norm_num [logSum,Finset.sum_range_succ]

private theorem logarithm_upper : Real.log (((27858011 : ℝ)/10000000000)⁻¹)<
    (1166243615/1000000000 : ℝ)*5+520018/10000000 := by
  apply dyadic_upper 8 (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ,Nat.factorial]

theorem energy_bounds : (520012 : ℝ)/10000000<realEnergy (horizontalStrip 5) ∧
    realEnergy (horizontalStrip 5)<(520018 : ℝ)/10000000 := by
  have he := strip_energy_exact (by decide : 5≤6)
  rw [stripMatrix_det_5] at he
  have he' : realEnergy (horizontalStrip 5)= -Real.log (stripDet5 (1/Real.pi))-
      5*SquareMaximality.squareLatticeEntropy := by
    simpa only [Nat.cast_ofNat,Nat.cast_one,mul_comm] using he
  exact energy_bounds_of_exact (by norm_num : (0 : ℝ)≤5) he'
    (by norm_num) stripDet5_bounds logarithm_lower logarithm_upper

end
end SpanningTreeIsoperimetry.PrintedEnergyBounds.strip5
