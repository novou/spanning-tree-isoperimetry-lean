import SpanningTreeIsoperimetry.RectangleEnergyBounds
import SpanningTreeIsoperimetry.TwoTierFerrers

/-! Reuse the already checked actual small-corner determinant formula. -/
namespace SpanningTreeIsoperimetry.RefinedObstructionPolynomials.rectangle23
open Ferrers CornerEnergy TwoTierFerrers
noncomputable section

def diagram : Diagram := faceRectangle 3 2
def determinant (t : ℝ) : ℝ := SmallGreenPolynomials.rectangleDet t

theorem energy_exact : realEnergy diagram = -Real.log (determinant (1/Real.pi))-
    6*SquareMaximality.squareLatticeEntropy := by
  have he : diagram=faceRectangle 3 2 := by decide +kernel
  simpa only [he,determinant] using SmallCornerEnergies.rectangle_energy_exact

theorem determinant_pos : 0<determinant (1/Real.pi) := RectangleEnergyBounds.rectangleDet_pos

end
end SpanningTreeIsoperimetry.RefinedObstructionPolynomials.rectangle23
