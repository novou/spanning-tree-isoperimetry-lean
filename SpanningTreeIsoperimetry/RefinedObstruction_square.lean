module

public import SpanningTreeIsoperimetry.RectangleEnergyBounds
public import SpanningTreeIsoperimetry.TwoTierFerrers

@[expose] public section

/-! Reuse the already checked actual small-corner determinant formula. -/
namespace SpanningTreeIsoperimetry.RefinedObstructionPolynomials.square
open Ferrers CornerEnergy TwoTierFerrers
noncomputable section

def diagram : Diagram := faceRectangle 2 2
def determinant (t : ℝ) : ℝ := SmallGreenPolynomials.squareDet t

theorem energy_exact : realEnergy diagram = -Real.log (determinant (1/Real.pi))-
    4*SquareMaximality.squareLatticeEntropy := by
  have he : diagram=faceRectangle 2 2 := by decide +kernel
  simpa only [he,determinant] using SmallCornerEnergies.square_energy_exact

theorem determinant_pos : 0<determinant (1/Real.pi) := RectangleEnergyBounds.squareDet_pos

end
end SpanningTreeIsoperimetry.RefinedObstructionPolynomials.square
