import SquareMaximality.Boundary.Completion
import SquareMaximality.Dual.ForestEventsConstruction
import SquareMaximality.Dual.PlanarComplement
import SquareMaximality.Dual.CanonicalVacancyDeletion
import SquareMaximality.Dual.TappRayleigh
import SquareMaximality.ClosedWalk.EntropySeries

/-!
# Hull completion from Matrix--Tree and planar deletion

This module assembles all proved boundary, interior, transfer-current, and
Tapp estimates. It first exposes the exact planar deletion family as a
factored interface, then discharges it with the explicit generic planar-minor
construction.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Boundary

/-- A constructor for the exact three deletion/contraction equivalences
used by a normalized hull.  This proposition contains no determinant,
probability, or analytic assertion. -/
def CanonicalVacancyDeletionInput : Prop :=
  ∀ {A : Finset Point} {R S : ℕ},
    1 ≤ R → 1 ≤ S →
    (inducedGrid A).Connected →
    IsRectHull A 0 0 (R + 1) (S + 1) →
    Nonempty (Dual.CanonicalVacancyDeletionTreeEquivs A R S)

/-- The generic planar-minor theorem constructs the required canonical
deletion family; no geometric input remains. -/
theorem canonicalVacancyDeletionInput : CanonicalVacancyDeletionInput := by
  intro A R S hR hS hconn hHull
  exact ⟨Dual.canonicalVacancyDeletionTreeEquivs hR hS hHull hconn⟩

/-- Once the explicit planar deletion equivalences are available, the
generic labelled Matrix--Tree theorem supplies every factor estimate in the
normalized hull argument. -/
theorem canonicalHullInputs_of_matrixTree_and_deletion
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    (hDeletion : CanonicalVacancyDeletionInput) :
    CanonicalHullInputs squareLatticeEntropy := by
  intro A R S hR hS hconn hHull
  let d := Classical.choice (hDeletion hR hS hconn hHull)
  let events := d.canonicalForestEvents hR hS
  let dualDeterminants :=
    Dual.boundaryDualDeterminantIdentities_of_planarTreeComplement
      hMatrixTree R S A
        (Dual.canonicalBoundaryPlanarTreeComplement hR hS hHull hconn)
  let series := SpectralBound.toBoundaryDeterminantSeriesInputs
    dualDeterminants ClosedWalk.hasSum_evenClosedWordTerm
  let boundary := series.log_boundaryFactor hHull hconn
  let tapp : Dual.TappSquareFamilyLowerBound squareLatticeEntropy :=
    Dual.tappSquareFamilyLowerBound_of_halfPlaneTwoForestResistance
    (Dual.halfPlaneTwoForestResistanceBound_squareLatticeEntropy hMatrixTree)
  let factors := Dual.canonicalFactorBounds_of_interiorEvents boundary
    (fun i => Dual.canonicalInteriorEventCertificate_of_tapp i tapp
      (Dual.interiorDeletionConnected_of_hull hHull hconn i)
      (d.interiorPlanarDuality hR hS i))
  let transferCurrent :=
    Dual.rectangleDualSuccTransferCurrentDeterminantInput hMatrixTree R S
  exact ⟨Dual.canonicalFactorEstimates_of_forestEvents hconn events
    transferCurrent.forestBlockNegativeCorrelation factors⟩

/-- Complete normalized-hull estimate parameterized by the Matrix--Tree
interface.  `Paper.lean` supplies its proved implementation; all planar,
Tapp, determinant-series, and correlation inputs are constructed here. -/
theorem canonicalHullInputs_of_matrixTree
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0}) :
    CanonicalHullInputs squareLatticeEntropy :=
  canonicalHullInputs_of_matrixTree_and_deletion
    hMatrixTree canonicalVacancyDeletionInput

end Boundary
end SquareMaximality
