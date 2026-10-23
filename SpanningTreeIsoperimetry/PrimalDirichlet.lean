module

public import SpanningTreeIsoperimetry.CornerDeterminant
public import SpanningTreeIsoperimetry.GapConvexity
public import SquareMaximality.Dual.PlanarComplement
public import SquareMaximality.Dual.BoundaryDeterminants
public import SquareMaximality.Inputs.MatrixTreeTheorem

@[expose] public section

/-! Actual primal tree counts and the finite face Dirichlet matrix when
every vacancy component meets the rectangular boundary. -/
namespace SpanningTreeIsoperimetry.PrimalDirichlet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open SquareMaximality.Boundary
open CornerEnergy Ferrers

noncomputable def remainingFaces (R S : ℕ) (A : Domain) : Diagram :=
  faceIndices R S \ markedFaces R S (encodedVacancies R S A)

theorem canonicalBoundary_eq_vacancies {R S : ℕ} {A : Domain}
    (hc : canonicalInteriorCount R S A=0) :
    canonicalBoundary R S A=SquareMaximality.rectangle 0 0 (R+1) (S+1) \ A := by
  unfold canonicalBoundary
  rw [boundaryVacancies_eq_all_of_no_interior hc,image_encodedVacancies]

theorem boundary_deletion_eq {R S : ℕ} {A : Domain}
    (hsub : A ⊆ SquareMaximality.rectangle 0 0 (R+1) (S+1))
    (hc : canonicalInteriorCount R S A=0) :
    SquareMaximality.rectangle 0 0 (R+1) (S+1) \ canonicalBoundary R S A=A := by
  rw [canonicalBoundary_eq_vacancies hc]
  ext p
  simp only [Finset.mem_sdiff]
  constructor
  · tauto
  · intro hp
    exact ⟨hsub hp,by tauto⟩

/-- Both primal counts are identified with the exact finite face determinants;
all Matrix–Tree and planar deletion inputs are constructed locally. -/
theorem treeCount_pair_eq_dirichlet {R S : ℕ} {A : Domain}
    (hR : 1≤R) (hS : 1≤S)
    (hHull : SquareMaximality.IsRectHull A 0 0 (R+1) (S+1))
    (hconn : (domainGraph A).Connected) (hc : canonicalInteriorCount R S A=0) :
    (treeCount (rectangle (R+1) (S+1)) : ℝ)=
        Matrix.det (fourIminusAdjacency (faceRectangle R S)) ∧
      (treeCount A : ℝ)=Matrix.det (fourIminusAdjacency (remainingFaces R S A)) := by
  have hfconn : (SquareMaximality.inducedGrid A).Connected := by
    simpa only [← domainGraph_eq_foundation] using hconn
  let p := SquareMaximality.Dual.canonicalBoundaryPlanarTreeComplement hR hS hHull hfconn
  have d := SquareMaximality.Dual.boundaryDualDeterminantIdentities_of_planarTreeComplement
    SquareMaximality.labeledMultigraphCofactorInput R S A p
  constructor
  · rw [rectangle_treeCount_eq_foundation]
    exact d.rectangleDet.trans
      (congrArg (fun U : Diagram => Matrix.det (fourIminusAdjacency U))
        (foundation_faceIndices R S))
  · have h := d.vacancyDet
    rw [boundary_deletion_eq hHull.2.2.1 hc,
      boundaryVacancies_eq_all_of_no_interior hc] at h
    rw [treeCount_eq_foundation]
    exact h

theorem markedFaces_subset_rectangle (R S : ℕ) (A : Domain) :
    markedFaces R S (encodedVacancies R S A) ⊆ faceRectangle R S := by
  intro p hp
  have hm := mem_markedFaces.mp hp
  exact mem_faceRectangle.mpr ⟨hm.1,hm.2.1⟩

/-- Jacobi's formula as an exact identity of actual primal tree counts. -/
theorem treeCount_eq_rectangle_mul_greenMinor {R S : ℕ} {A : Domain}
    (hR : 1≤R) (hS : 1≤S)
    (hHull : SquareMaximality.IsRectHull A 0 0 (R+1) (S+1))
    (hconn : (domainGraph A).Connected) (hc : canonicalInteriorCount R S A=0) :
    (treeCount A : ℝ)=(treeCount (rectangle (R+1) (S+1)) : ℝ)*
      Matrix.det (greenMinor (markedFaces_subset_rectangle R S A)) := by
  obtain ⟨hfull,hremaining⟩ := treeCount_pair_eq_dirichlet hR hS hHull hconn hc
  have hid := greenMinor_det_identity (Finset.Subset.refl (faceRectangle R S))
    (markedFaces_subset_rectangle R S A)
  rw [hfull,hremaining]
  have heq := congrArg (fun U : Diagram => U \ markedFaces R S (encodedVacancies R S A))
    (foundation_faceIndices R S)
  exact (congrArg (fun U : Diagram => Matrix.det (fourIminusAdjacency U)) heq).trans hid

end SpanningTreeIsoperimetry.PrimalDirichlet
