module

public import SpanningTreeIsoperimetry.ThreeCellEnergy
public import SpanningTreeIsoperimetry.TwoTierFerrers

@[expose] public section

/-! Reuse the already checked actual small-corner determinant formula. -/
namespace SpanningTreeIsoperimetry.RefinedObstructionPolynomials.ell
open Ferrers CornerEnergy TwoTierFerrers
noncomputable section

def diagram : Diagram := twoTier 1 1 1 1
def determinant (t : ℝ) : ℝ := ThreeCellEnergy.ellDet t

theorem energy_exact : realEnergy diagram = -Real.log (determinant (1/Real.pi))-
    3*SquareMaximality.squareLatticeEntropy := by
  have he : diagram=threeCell := by decide +kernel
  simpa only [he,determinant] using ThreeCellEnergy.realEnergy_ell_exact

theorem determinant_pos : 0<determinant (1/Real.pi) := ThreeCellEnergy.ellDet_pos

end
end SpanningTreeIsoperimetry.RefinedObstructionPolynomials.ell
