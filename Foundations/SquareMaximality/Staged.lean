module

public import SquareMaximality.Main
public import SquareMaximality.Rectangle.Kernel
public import SquareMaximality.Rectangle.Entropy
public import SquareMaximality.Rectangle.SharpTrapezoid
public import SquareMaximality.Rectangle.Spectral
public import SquareMaximality.ClosedWalk.EntropySeries
public import SquareMaximality.Boundary.Completion

@[expose] public section

set_option autoImplicit false

/-!
# Staged end-to-end theorem

This module replaces the two coarse penalty interfaces in `Main.lean` by the
lower-level rectangular analytic package and the componentwise hull package.
It is a modular assembly layer: `Paper.lean` constructs all of these objects
before exporting the final results.
-/

namespace SquareMaximality

/-- Low-level modular inputs for the complete theorem. -/
structure StagedEqualityInputs (κ : ℝ) : Type where
  rectangle : Rectangle.Kernel.Inputs κ
  hull : Boundary.CanonicalHullInputs κ

namespace StagedEqualityInputs

variable {κ : ℝ}

theorem toEqualityInputs (h : StagedEqualityInputs κ) : EqualityInputs κ where
  rectangularPenalty := Rectangle.Kernel.Inputs.rectangularAreaPenalty
    (StagedEqualityInputs.rectangle h)
  hullPenalty := Boundary.normalizedHullPenalty_of_componentwise
    (Boundary.componentwiseHullInputs_of_canonical (StagedEqualityInputs.hull h))
  strictRectangularPenalty := Rectangle.Kernel.Inputs.strictRectangularAreaPenalty
    (StagedEqualityInputs.rectangle h)

theorem squareMaximality
    (h : StagedEqualityInputs κ)
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2) :
    tau S ≤ tauRect n n :=
  squareMaximality_of_inputs
    (EqualityInputs.toMaximalityInputs (StagedEqualityInputs.toEqualityInputs h)) hn S hcard

theorem equality_iff_latticeSquare
    (h : StagedEqualityInputs κ)
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2) :
    tau S = tauRect n n ↔ IsLatticeSquare S n :=
  equality_iff_latticeSquare_of_inputs (StagedEqualityInputs.toEqualityInputs h) hn S hcard

end StagedEqualityInputs

/-- Manuscript-specific modular inputs.  Matrix--Tree is kept as a field here
to separate assembly layers; `Paper.lean` fills it with the proved cofactor
theorem.  Finite cosine diagonalization, the product reduction, entropy
integral, and sharp trapezoid identity are also proved in the development. -/
structure PaperStagedInputs : Type where
  rectangleMatrixTree : RectangleCofactorInput
  multigraphMatrixTree : LabeledMultigraphCofactorInput.{0, 0}
  hull : Boundary.ManuscriptHullInputs squareLatticeEntropy

namespace PaperStagedInputs

/-- Convert the manuscript-facing staged inputs to the generic end-to-end
package. -/
noncomputable def toStagedEqualityInputs (h : PaperStagedInputs) :
    StagedEqualityInputs squareLatticeEntropy where
  rectangle := Rectangle.Trapezoid.DeterminantalInputs.toSquareLatticeEntropyInputs
    (Rectangle.ProductInputs.determinantalInputs h.rectangleMatrixTree
      (Rectangle.Spectral.rectangularSpectralCofactor h.rectangleMatrixTree))
      Rectangle.Entropy.kernelIntegral_eq_squareLatticeEntropy
      Rectangle.SharpTrapezoid.sharpTrapezoidFormula
  hull := h.hull.toCanonicalHullInputs h.multigraphMatrixTree
    ClosedWalk.hasSum_evenClosedWordTerm

theorem squareMaximality
    (h : PaperStagedInputs)
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2) :
    tau S ≤ tauRect n n :=
  StagedEqualityInputs.squareMaximality h.toStagedEqualityInputs hn S hcard

theorem equality_iff_latticeSquare
    (h : PaperStagedInputs)
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2) :
    tau S = tauRect n n ↔ IsLatticeSquare S n :=
  StagedEqualityInputs.equality_iff_latticeSquare
    h.toStagedEqualityInputs hn S hcard

end PaperStagedInputs

end SquareMaximality
