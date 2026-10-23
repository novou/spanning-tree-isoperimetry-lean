module

public import SpanningTreeIsoperimetry.ConcreteCounts
public import SpanningTreeIsoperimetry.FiniteFaceCountBridge

@[expose] public section

/-! Literal variable-parameter face polynomials at N=14. Both coordinate
matrices are identified with the actual bounded faces of the already defined
primal domains. The 3t difference is an identity of actual characteristic
polynomials, not merely their evaluations at four. -/
namespace SpanningTreeIsoperimetry.FourteenFacePolynomials
open SmallCases ConcreteCounts FiniteFaceCountBridge
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Two four-cycles meeting at the central face (1,1). -/
def oppositePoints : Fin 7 → Vertex := ![(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1)]
/-- The 2 by 4 face ladder with its lower-left corner deleted. -/
def canonicalPoints : Fin 7 → Vertex := ![(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)]

theorem oppositePoints_injective : Function.Injective oppositePoints := by decide +kernel
theorem canonicalPoints_injective : Function.Injective canonicalPoints := by decide +kernel

theorem opposite_face_set : boundedFaces 4 4 winner14Domain=Finset.univ.image oppositePoints := by
  decide +kernel

theorem canonical_face_set : boundedFaces 3 5 canonical14Domain=Finset.univ.image canonicalPoints := by
  decide +kernel

section Matrix
variable {R : Type*} [CommRing R]

set_option maxHeartbeats 2000000 in
 theorem oppositePoints_det (t : R) : Matrix.det (pointMatrix oppositePoints t)=opposite14 t := by
  have hm : pointMatrix oppositePoints t= !![
    t,-1,0,-1,0,0,0;
    -1,t,0,0,-1,0,0;
    0,0,t,-1,0,-1,0;
    -1,0,-1,t,-1,0,-1;
    0,-1,0,-1,t,0,0;
    0,0,-1,0,0,t,-1;
    0,0,0,-1,0,-1,t] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [pointMatrix,oppositePoints]
  rw [hm]
  simp (config := { maxSteps := 1000000 }) [Matrix.det_succ_row_zero,Fin.sum_univ_succ,
    Matrix.submatrix,Fin.succAbove,opposite14,continuant,cycle]
  ring

set_option maxHeartbeats 2000000 in
 theorem canonicalPoints_det (t : R) : Matrix.det (pointMatrix canonicalPoints t)=cornerLadder t 4 := by
  have hm : pointMatrix canonicalPoints t= !![
    t,-1,0,0,-1,0,0;
    -1,t,-1,0,0,-1,0;
    0,-1,t,0,0,0,-1;
    0,0,0,t,-1,0,0;
    -1,0,0,-1,t,-1,0;
    0,-1,0,0,-1,t,-1;
    0,0,-1,0,0,-1,t] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [pointMatrix,canonicalPoints]
  rw [hm]
  simp (config := { maxSteps := 1000000 }) [Matrix.det_succ_row_zero,Fin.sum_univ_succ,
    Matrix.submatrix,Fin.succAbove,cornerLadder,ladder,continuant]
  ring

end Matrix

theorem pointGraph_characteristic_polynomials :
    ((pointGraph oppositePoints).adjMatrix ℤ).charpoly=opposite14 Polynomial.X ∧
      ((pointGraph canonicalPoints).adjMatrix ℤ).charpoly=cornerLadder Polynomial.X 4 := by
  simp only [pointGraph_charpoly,oppositePoints_det,canonicalPoints_det,and_self]

/-- Reindexing the coordinate graph retains the actual characteristic polynomial. -/
theorem image_characteristic_polynomial {n : ℕ} (p : Fin n → Vertex) (hinj : Function.Injective p) :
    ((domainGraph (Finset.univ.image p)).adjMatrix ℤ).charpoly=
      Matrix.det (pointMatrix p Polynomial.X) := by
  let e := pointGraphIso p hinj
  rw [← e.reindex_adjMatrix ℤ,Matrix.charpoly_reindex,pointGraph_charpoly]

/-- The manuscript's 2cf3-tf3² polynomial for the actual N=14 opposite face graph. -/
theorem opposite_face_charpoly :
    ((domainGraph (boundedFaces 4 4 winner14Domain)).adjMatrix ℤ).charpoly=
      2*cycle Polynomial.X*continuant Polynomial.X 3-
        Polynomial.X*continuant Polynomial.X 3^2 := by
  rw [opposite_face_set,image_characteristic_polynomial oppositePoints oppositePoints_injective,
    oppositePoints_det]
  rfl

theorem canonical_face_charpoly :
    ((domainGraph (boundedFaces 3 5 canonical14Domain)).adjMatrix ℤ).charpoly=
      cornerLadder Polynomial.X 4 := by
  rw [canonical_face_set,image_characteristic_polynomial canonicalPoints canonicalPoints_injective,
    canonicalPoints_det]

/-- Exact difference of the two actual adjacency characteristic polynomials. -/
theorem face_charpoly_difference :
    ((domainGraph (boundedFaces 4 4 winner14Domain)).adjMatrix ℤ).charpoly-
      ((domainGraph (boundedFaces 3 5 canonical14Domain)).adjMatrix ℤ).charpoly=
        3*Polynomial.X := by
  rw [opposite_face_charpoly,canonical_face_charpoly]
  exact opposite14_sub_canonical (Polynomial.X : Polynomial ℤ)

/-- The actual finite face determinants at every real spectral parameter. -/
theorem faceDeterminant_opposite (t : ℝ) :
    StripPolarization.faceDeterminant (boundedFaces 4 4 winner14Domain) t=opposite14 t := by
  rw [opposite_face_set,faceDeterminant_points oppositePoints oppositePoints_injective,oppositePoints_det]

theorem faceDeterminant_canonical (t : ℝ) :
    StripPolarization.faceDeterminant (boundedFaces 3 5 canonical14Domain) t=cornerLadder t 4 := by
  rw [canonical_face_set,faceDeterminant_points canonicalPoints canonicalPoints_injective,canonicalPoints_det]

theorem faceDeterminant_difference (t : ℝ) :
    StripPolarization.faceDeterminant (boundedFaces 4 4 winner14Domain) t-
      StripPolarization.faceDeterminant (boundedFaces 3 5 canonical14Domain) t=3*t := by
  rw [faceDeterminant_opposite,faceDeterminant_canonical]
  exact opposite14_sub_canonical t

end
end SpanningTreeIsoperimetry.FourteenFacePolynomials
