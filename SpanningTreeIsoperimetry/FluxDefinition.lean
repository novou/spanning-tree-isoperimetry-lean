module

public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-! Stable exact boundary-flux data. Scalar estimates are in FluxBounds. -/
namespace SpanningTreeIsoperimetry.FluxBounds
noncomputable section

def cubic (k : ℝ) : ℝ := k*(k+1)*(2*k+1)
def quadratic (k : ℝ) : ℝ := k*(k+1)

/-- Right side of the manuscript's finite long-side strip error, including k=0. -/
def fluxBound (r s k : ℝ) : ℝ :=
  Real.pi^3/60 * ((cubic k/3) * (1/(r^2-4)^2 + 1/(s^2-k^2)^2) +
    quadratic k * (1/(r^2-1)^2 + 1/(s^2-(k+1)^2)^2))

end
end SpanningTreeIsoperimetry.FluxBounds
