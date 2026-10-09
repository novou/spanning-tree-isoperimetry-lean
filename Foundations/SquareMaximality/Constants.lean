import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

/-!
# Constants used by the manuscript

The final cancellation theorem is parameterized by an arbitrary real constant, so it does not
need the analytic evaluation below.  We nevertheless record the manuscript's definitions here
to keep the formal vocabulary aligned with `general.tex`.
-/

namespace SquareMaximality

/-- Catalan's constant, as defined by the alternating odd reciprocal-square series. -/
noncomputable def catalanConstant : ℝ :=
  ∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2

/-- The square-lattice tree entropy appearing in both penalty estimates. -/
noncomputable def squareLatticeEntropy : ℝ :=
  4 * catalanConstant / Real.pi

end SquareMaximality
