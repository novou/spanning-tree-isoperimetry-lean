import SquareMaximality.ClosedWalk.Counts
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity

/-! Stable open-word interface for half-plane Green coefficients. -/
namespace SpanningTreeIsoperimetry.BoundaryGreen
open SquareMaximality.ClosedWalk

/-- A boundary-to-boundary path in the half-plane x≥0. Coordinate swap sends
this to a bottom-boundary path in the rectangles used by the strip comparison. -/
abbrev HalfPlaneWord (n j : ℕ) :=
  {w : Word n // total w = (0,(j : ℤ)) ∧ ∀ x ∈ visitedX w, 0 ≤ x}

noncomputable instance halfPlaneWordFintype (n j : ℕ) : Fintype (HalfPlaneWord n j) :=
  Fintype.ofFinite _

/-- The actual half-plane path coefficient in the Green series. -/
noncomputable def halfPlaneCoefficient (n j : ℕ) : ℝ :=
  (Fintype.card (HalfPlaneWord n j) : ℝ) / (4 : ℝ)^(n+1)

theorem halfPlaneCoefficient_nonneg (n j : ℕ) : 0 ≤ halfPlaneCoefficient n j := by
  unfold halfPlaneCoefficient
  positivity

end SpanningTreeIsoperimetry.BoundaryGreen
