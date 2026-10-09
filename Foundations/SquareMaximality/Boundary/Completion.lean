import SquareMaximality.Boundary.SpectralBound
import SquareMaximality.Dual.TappSeries
import SquareMaximality.Dual.BoundaryDeterminants
import SquareMaximality.Dual.RectangleTransferCurrent

/-!
# Manuscript-facing hull completion

This module replaces the coarse `CanonicalHullInputs` assumption by the
upstream objects that remain in the manuscript proof: planar forest-event
identifications, explicit planar tree-complement/contraction geometry, Tapp's
graph-level lower bound, and the separate interior planar-duality identities.  All
assembly from those objects to the normalized hull penalty is proved here.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Boundary

/-- Exact outstanding inputs for the nondegenerate normalized-hull argument.
Each field is stated before the already formalized probability, series, and
component assembly steps. -/
structure ManuscriptHullInputs (κ : ℝ) : Type where
  forestEvents : ∀ {A : Finset Point} {R S : ℕ},
    (inducedGrid A).Connected → IsRectHull A 0 0 (R + 1) (S + 1) →
      Dual.CanonicalForestEvents A R S
  boundaryPlanarTreeComplement : ∀ {A : Finset Point} {R S : ℕ},
    (inducedGrid A).Connected → IsRectHull A 0 0 (R + 1) (S + 1) →
      Dual.BoundaryPlanarTreeComplement R S A
  halfPlaneTwoForestResistance : Dual.HalfPlaneTwoForestResistanceBound κ
  interiorPlanarDuality : ∀ {A : Finset Point} {R S : ℕ},
    (inducedGrid A).Connected → IsRectHull A 0 0 (R + 1) (S + 1) →
      ∀ i, Dual.InteriorPlanarDualityInput A R S i

namespace ManuscriptHullInputs

variable {κ : ℝ}

/-- The precise manuscript-facing inputs construct the canonical hull
package used by the end-to-end theorem. -/
theorem toCanonicalHullInputs
    (h : ManuscriptHullInputs κ)
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    (walkEntropy : HasSum evenClosedWordTerm (Real.log 4 - κ)) :
    CanonicalHullInputs κ := by
  intro A R S _hR _hS hconn hHull
  let events := h.forestEvents hconn hHull
  let dualDeterminants :=
    Dual.boundaryDualDeterminantIdentities_of_planarTreeComplement
      hMatrixTree R S A (h.boundaryPlanarTreeComplement hconn hHull)
  let series := SpectralBound.toBoundaryDeterminantSeriesInputs
    dualDeterminants walkEntropy
  let boundary := series.log_boundaryFactor hHull hconn
  let factors := Dual.canonicalFactorBounds_of_interiorEvents boundary
    (fun i => Dual.canonicalInteriorEventCertificate_of_tapp i
      (Dual.tappSquareFamilyLowerBound_of_halfPlaneTwoForestResistance
        h.halfPlaneTwoForestResistance)
      (Dual.interiorDeletionConnected_of_hull hHull hconn i)
      (h.interiorPlanarDuality hconn hHull i))
  let transferCurrent :=
    Dual.rectangleDualSuccTransferCurrentDeterminantInput hMatrixTree R S
  exact ⟨Dual.canonicalFactorEstimates_of_forestEvents hconn events
    transferCurrent.forestBlockNegativeCorrelation factors⟩

end ManuscriptHullInputs

end Boundary
end SquareMaximality
