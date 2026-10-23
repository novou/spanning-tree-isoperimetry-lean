module

public import SquareMaximality.Staged
public import SquareMaximality.Subgraphs
public import SquareMaximality.Boundary.MatrixTreeCompletion
public import SquareMaximality.Inputs.MatrixTreeBridge
public import SquareMaximality.Inputs.MatrixTreeTheorem

@[expose] public section

/-!
# Fully formalized manuscript theorem

The parameterized assembly theorems below expose the Matrix--Tree interface
used by the rest of the development.  The final declarations instantiate
that interface with the proved labelled-multigraph Matrix--Tree theorem.
-/

set_option autoImplicit false

namespace SquareMaximality

/-- Assemble the complete rectangular and hull estimates from one generic
Matrix--Tree theorem and the explicit planar deletion equivalences. -/
noncomputable def stagedEqualityInputs_of_matrixTree_and_deletion
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    (hDeletion : Boundary.CanonicalVacancyDeletionInput) :
    StagedEqualityInputs squareLatticeEntropy := by
  let hRectangle := rectangleCofactorInput_of_labeledMatrixTree hMatrixTree
  exact
    { rectangle :=
        Rectangle.Trapezoid.DeterminantalInputs.toSquareLatticeEntropyInputs
          (Rectangle.ProductInputs.determinantalInputs hRectangle
            (Rectangle.Spectral.rectangularSpectralCofactor hRectangle))
          Rectangle.Entropy.kernelIntegral_eq_squareLatticeEntropy
          Rectangle.SharpTrapezoid.sharpTrapezoidFormula
      hull := Boundary.canonicalHullInputs_of_matrixTree_and_deletion
        hMatrixTree hDeletion }

/-- Modular square-maximality theorem from explicit Matrix--Tree and planar
deletion inputs.  Both inputs are constructed later in this module. -/
theorem paper_squareMaximality_of_matrixTree_and_deletion
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    (hDeletion : Boundary.CanonicalVacancyDeletionInput)
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2) :
    tau S ≤ tauRect n n :=
  StagedEqualityInputs.squareMaximality
    (stagedEqualityInputs_of_matrixTree_and_deletion hMatrixTree hDeletion)
    hn S hcard

/-- Modular equality theorem from explicit Matrix--Tree and planar deletion
inputs.  Both inputs are constructed later in this module. -/
theorem paper_equality_iff_latticeSquare_of_matrixTree_and_deletion
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    (hDeletion : Boundary.CanonicalVacancyDeletionInput)
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2) :
    tau S = tauRect n n ↔ IsLatticeSquare S n :=
  StagedEqualityInputs.equality_iff_latticeSquare
    (stagedEqualityInputs_of_matrixTree_and_deletion hMatrixTree hDeletion)
    hn S hcard

/-- Assemble every analytic, planar, correlation, and equality input from
the single generic Matrix--Tree hypothesis. -/
noncomputable def stagedEqualityInputs_of_matrixTree
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0}) :
    StagedEqualityInputs squareLatticeEntropy := by
  let hRectangle := rectangleCofactorInput_of_labeledMatrixTree hMatrixTree
  exact
    { rectangle :=
        Rectangle.Trapezoid.DeterminantalInputs.toSquareLatticeEntropyInputs
          (Rectangle.ProductInputs.determinantalInputs hRectangle
            (Rectangle.Spectral.rectangularSpectralCofactor hRectangle))
          Rectangle.Entropy.kernelIntegral_eq_squareLatticeEntropy
          Rectangle.SharpTrapezoid.sharpTrapezoidFormula
      hull := Boundary.canonicalHullInputs_of_matrixTree hMatrixTree }

/-- Reusable assembly theorem parameterized by the Matrix--Tree interface.
The public theorem supplies its proved implementation. -/
theorem paper_squareMaximality_of_matrixTree
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2) :
    tau S ≤ tauRect n n :=
  StagedEqualityInputs.squareMaximality
    (stagedEqualityInputs_of_matrixTree hMatrixTree) hn S hcard

/-- Reusable equality theorem parameterized by the Matrix--Tree interface.
The public theorem supplies its proved implementation. -/
theorem paper_equality_iff_latticeSquare_of_matrixTree
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2) :
    tau S = tauRect n n ↔ IsLatticeSquare S n :=
  StagedEqualityInputs.equality_iff_latticeSquare
    (stagedEqualityInputs_of_matrixTree hMatrixTree) hn S hcard

/-- The introductory formulation for an arbitrary spanning subgraph of the
square lattice. Adding all available lattice edges can only increase its
tree count. -/
theorem paper_spanningSubgraph_squareMaximality_of_matrixTree
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2)
    (G : SimpleGraph {p : Point // p ∈ S}) (hG : G ≤ inducedGrid S) :
    treeCount G ≤ tauRect n n :=
  spanningSubgraph_squareMaximality_of_inputs
    (EqualityInputs.toMaximalityInputs
      (StagedEqualityInputs.toEqualityInputs
        (stagedEqualityInputs_of_matrixTree hMatrixTree)))
    hn S hcard G hG

/-- A proper connected spanning subgraph is strictly below the square. -/
theorem paper_spanningSubgraph_lt_square_of_matrixTree
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2)
    (G : SimpleGraph {p : Point // p ∈ S}) (hconn : G.Connected)
    (hproper : G < inducedGrid S) :
    treeCount G < tauRect n n :=
  spanningSubgraph_lt_square_of_inputs
    (EqualityInputs.toMaximalityInputs
      (StagedEqualityInputs.toEqualityInputs
        (stagedEqualityInputs_of_matrixTree hMatrixTree)))
    hn S hcard G hconn hproper

/-- Equality for an arbitrary square-lattice spanning subgraph occurs
exactly when every induced lattice edge is present and the vertex set is a
translated `n × n` square. -/
theorem paper_spanningSubgraph_equality_iff_of_matrixTree
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2)
    (G : SimpleGraph {p : Point // p ∈ S}) (hG : G ≤ inducedGrid S) :
    treeCount G = tauRect n n ↔
      G = inducedGrid S ∧ IsLatticeSquare S n := by
  constructor
  · intro heq
    have hconn : G.Connected := by
      apply (treeCount_pos_iff_connected G).mp
      rw [heq]
      exact tauRect_pos hn hn
    have hfull : G = inducedGrid S := by
      by_contra hne
      have hproper : G < inducedGrid S :=
        ⟨hG, fun hreverse => hne (le_antisymm hG hreverse)⟩
      have hlt := paper_spanningSubgraph_lt_square_of_matrixTree
        hMatrixTree hn S hcard G hconn hproper
      exact (Nat.ne_of_lt hlt) heq
    refine ⟨hfull, ?_⟩
    apply (paper_equality_iff_latticeSquare_of_matrixTree
      hMatrixTree hn S hcard).mp
    rw [← heq, hfull]
    rfl
  · rintro ⟨rfl, hsquare⟩
    change tau S = tauRect n n
    exact (paper_equality_iff_latticeSquare_of_matrixTree
      hMatrixTree hn S hcard).mpr hsquare

/-- All rectangular, analytic, planar, correlation, and equality inputs,
with Kirchhoff's Matrix--Tree theorem discharged internally. -/
noncomputable def fullyFormalizedStagedEqualityInputs :
    StagedEqualityInputs squareLatticeEntropy :=
  stagedEqualityInputs_of_matrixTree labeledMultigraphCofactorInput

/-- The manuscript's square-maximality theorem, with no manuscript-specific
or external mathematical hypotheses. -/
theorem paper_squareMaximality
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2) :
    tau S ≤ tauRect n n :=
  paper_squareMaximality_of_matrixTree labeledMultigraphCofactorInput
    hn S hcard

/-- Equality holds exactly for translated axis-aligned lattice squares,
with no manuscript-specific or external mathematical hypotheses. -/
theorem paper_equality_iff_latticeSquare
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2) :
    tau S = tauRect n n ↔ IsLatticeSquare S n :=
  paper_equality_iff_latticeSquare_of_matrixTree
    labeledMultigraphCofactorInput hn S hcard

/-- Square maximality for an arbitrary spanning subgraph, with Matrix--Tree
discharged internally. -/
theorem paper_spanningSubgraph_squareMaximality
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2)
    (G : SimpleGraph {p : Point // p ∈ S}) (hG : G ≤ inducedGrid S) :
    treeCount G ≤ tauRect n n :=
  paper_spanningSubgraph_squareMaximality_of_matrixTree
    labeledMultigraphCofactorInput hn S hcard G hG

/-- A proper connected spanning subgraph is strictly below the square, with
Matrix--Tree discharged internally. -/
theorem paper_spanningSubgraph_lt_square
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2)
    (G : SimpleGraph {p : Point // p ∈ S}) (hconn : G.Connected)
    (hproper : G < inducedGrid S) :
    treeCount G < tauRect n n :=
  paper_spanningSubgraph_lt_square_of_matrixTree
    labeledMultigraphCofactorInput hn S hcard G hconn hproper

/-- Equality for an arbitrary square-lattice spanning subgraph, with
Matrix--Tree discharged internally. -/
theorem paper_spanningSubgraph_equality_iff
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2)
    (G : SimpleGraph {p : Point // p ∈ S}) (hG : G ≤ inducedGrid S) :
    treeCount G = tauRect n n ↔
      G = inducedGrid S ∧ IsLatticeSquare S n :=
  paper_spanningSubgraph_equality_iff_of_matrixTree
    labeledMultigraphCofactorInput hn S hcard G hG

end SquareMaximality
