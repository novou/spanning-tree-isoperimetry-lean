module

public import SquareMaximality.Rectangle.Product
public import SquareMaximality.Rectangle.Trapezoid
public import SquareMaximality.Inputs.MatrixTree

@[expose] public section

set_option autoImplicit false

/-!
# Feeding the proved rectangular product into the penalty pipeline

Matrix--Tree and cosine diagonalization are kept separate.  Given the
rectangular Matrix--Tree interface, the remaining proposition at this layer is
the exact evaluation of one rectangular cofactor by the standard nonzero
Laplacian eigenvalue product.  The Chebyshev and logarithmic reduction from
that product to `Concrete.logProduct` is proved in `Rectangle.Product`.
-/

namespace SquareMaximality.Rectangle.ProductInputs

open Product

noncomputable section

/-- Canonical corner used for the rectangular reduced Laplacian. -/
def cornerRoot (a t : ℕ) (ha : 0 < a) (ht : 0 < t) : Fin a × Fin t :=
  (⟨0, ha⟩, ⟨0, ht⟩)

/-- The exact residual finite-linear-algebra statement: cosine
diagonalization evaluates the corner cofactor as the product of all nonzero
path-product eigenvalues divided by the number of vertices.

Unlike `RectangleCofactorInput`, this contains no spanning-tree assertion. -/
def RectangularSpectralCofactorInput : Prop :=
  ∀ (a t : ℕ) (ha : 0 < a) (ht : 0 < t),
    ((Matrix.det
      (rectangleReducedLapMatrix a t (cornerRoot a t ha ht)) : ℤ) : ℝ) =
      fullSpectralTreeProduct a t

theorem log_tauRect_eq_spectral
    (hMatrixTree : RectangleCofactorInput)
    (hSpectral : RectangularSpectralCofactorInput)
    {a t : ℕ} (ha : 0 < a) (ht : 0 < t) :
    Real.log (tauRect a t : ℝ) =
      Real.log (rectangularSpectralProduct a t) := by
  let root := cornerRoot a t ha ht
  have hcofactor := hMatrixTree a t ha ht root
  have hcast : (tauRect a t : ℝ) =
      ((Matrix.det (rectangleReducedLapMatrix a t root) : ℤ) : ℝ) := by
    exact_mod_cast hcofactor
  rw [hcast]
  change Real.log
      ((Matrix.det (rectangleReducedLapMatrix a t
        (cornerRoot a t ha ht)) : ℤ) : ℝ) = _
  rw [hSpectral a t ha ht, fullSpectralTreeProduct_eq ha ht]

/-- Existing `DeterminantalInputs` with `rectangularProductLog` discharged.
The two remaining interface arguments are proved and supplied by downstream
modules before reaching the final public theorem. -/
noncomputable def determinantalInputs
    (hMatrixTree : RectangleCofactorInput)
    (hSpectral : RectangularSpectralCofactorInput) :
    Trapezoid.DeterminantalInputs where
  logDeterminant a t := Real.log (rectangularSpectralProduct a t)
  base := spectralBase
  matrixTreeLog := fun ha ht =>
    log_tauRect_eq_spectral hMatrixTree hSpectral ha ht
  rectangularProductLog := fun ha ht =>
    log_rectangularSpectralProduct ha ht

end

end SquareMaximality.Rectangle.ProductInputs
