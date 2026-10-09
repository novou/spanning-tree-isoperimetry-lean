import SquareMaximality.Dual.Rectangle
import SquareMaximality.Multigraph.TransferCurrentConstruction

set_option autoImplicit false

/-!
# Transfer current for rectangular duals

This module handles the degenerate positive-side rectangles omitted by the
geometric connectivity statement in `Dual.Rectangle`: if either side has one
vertex, there are no bounded faces and the dual vertex type is a singleton.
It then specializes the generic Matrix--Tree construction of the transfer-
current determinant interface.
-/

namespace SquareMaximality
namespace Dual

open Multigraph

/-- The rectangular dual is connected for all positive side lengths,
including the one-row and one-column degeneracies. -/
theorem rectangleDual_connected_pos
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    (rectangleDual r s).Connected := by
  by_cases hr2 : 2 ≤ r
  · by_cases hs2 : 2 ≤ s
    · exact rectangleDual_connected hr2 hs2
    · have hs1 : s = 1 := by omega
      subst s
      letI : Subsingleton (RectangleDualVertex r 1) := by
        constructor
        intro a b
        cases a with
        | none =>
            cases b with
            | none => rfl
            | some y => exact Fin.elim0 y.2
        | some x => exact Fin.elim0 x.2
      rw [LabeledMultigraph.connected_iff_toSimpleGraph_connected]
      apply SimpleGraph.Connected.of_subsingleton
  · have hr1 : r = 1 := by omega
    subst r
    letI : Subsingleton (RectangleDualVertex 1 s) := by
      constructor
      intro a b
      cases a with
      | none =>
          cases b with
          | none => rfl
          | some y => exact Fin.elim0 y.1
      | some x => exact Fin.elim0 x.1
    rw [LabeledMultigraph.connected_iff_toSimpleGraph_connected]
    apply SimpleGraph.Connected.of_subsingleton

/-- Matrix--Tree constructs the transfer-current determinant interface for
every positive rectangular dual. -/
noncomputable def rectangleDualTransferCurrentDeterminantInput
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    (rectangleDual r s).TransferCurrentDeterminantInput :=
  LabeledMultigraph.transferCurrentDeterminantInputOfConnectedMatrixTreeSameUniverse
    (rectangleDual r s) hMatrixTree (rectangleDual_connected_pos hr hs) none

/-- The exact all-indices form needed by the hull completion, whose dual
rectangle has side lengths `R + 1` and `S + 1`. -/
noncomputable def rectangleDualSuccTransferCurrentDeterminantInput
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    (R S : ℕ) :
    (rectangleDual (R + 1) (S + 1)).TransferCurrentDeterminantInput :=
  rectangleDualTransferCurrentDeterminantInput hMatrixTree (R + 1) (S + 1)
    (by omega) (by omega)

end Dual
end SquareMaximality
