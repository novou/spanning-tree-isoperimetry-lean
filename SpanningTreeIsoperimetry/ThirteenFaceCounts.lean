module

public import SpanningTreeIsoperimetry.FiniteFaceCountBridge

@[expose] public section

/-! The exact face comparisons on the three-vacancy square hull at N=13. -/
namespace SpanningTreeIsoperimetry.ThirteenFaceCounts
open SmallCases FiniteFaceCountBridge
open scoped Classical
variable {R : Type*} [CommRing R]

def oppositePoints : Fin 6 → Vertex := ![(2,0),(0,1),(1,1),(2,1),(0,2),(1,2)]

theorem oppositePoints_injective : Function.Injective oppositePoints := by decide +kernel

set_option maxHeartbeats 2000000 in
 theorem oppositePoints_det (t : R) : Matrix.det (pointMatrix oppositePoints t)=opposite13 t := by
  have hm : pointMatrix oppositePoints t= !![t, 0, 0, -1, 0, 0;
    0, t, -1, 0, -1, 0;
    0, -1, t, -1, 0, -1;
    -1, 0, -1, t, 0, 0;
    0, -1, 0, 0, t, -1;
    0, 0, -1, 0, -1, t] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [pointMatrix,oppositePoints]
  rw [hm]
  simp (config := { maxSteps := 1000000 }) [Matrix.det_succ_row_zero,Fin.sum_univ_succ,
    Matrix.submatrix,Fin.succAbove,opposite13,continuant,cycle]
  ring

theorem oppositeFace_count : StripPolarization.faceDeterminant (Finset.univ.image oppositePoints) 4=
    opposite13 (4 : ℝ) := by
  rw [faceDeterminant_points oppositePoints oppositePoints_injective,oppositePoints_det]

def ellPoints : Fin 6 → Vertex := ![(2,0),(1,1),(2,1),(0,2),(1,2),(2,2)]

theorem ellPoints_injective : Function.Injective ellPoints := by decide +kernel

set_option maxHeartbeats 2000000 in
 theorem ellPoints_det (t : R) : Matrix.det (pointMatrix ellPoints t)=ell13 t := by
  have hm : pointMatrix ellPoints t= !![t, 0, -1, 0, 0, 0;
    0, t, -1, 0, -1, 0;
    -1, -1, t, 0, 0, -1;
    0, 0, 0, t, -1, 0;
    0, -1, 0, -1, t, -1;
    0, 0, -1, 0, -1, t] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [pointMatrix,ellPoints]
  rw [hm]
  simp (config := { maxSteps := 1000000 }) [Matrix.det_succ_row_zero,Fin.sum_univ_succ,
    Matrix.submatrix,Fin.succAbove,ell13,continuant,cycle]
  ring

theorem ellFace_count : StripPolarization.faceDeterminant (Finset.univ.image ellPoints) 4=
    ell13 (4 : ℝ) := by
  rw [faceDeterminant_points ellPoints ellPoints_injective,ellPoints_det]

def triplePoints : Fin 6 → Vertex := ![(1,0),(0,1),(1,1),(2,1),(0,2),(1,2)]

theorem triplePoints_injective : Function.Injective triplePoints := by decide +kernel

set_option maxHeartbeats 2000000 in
 theorem triplePoints_det (t : R) : Matrix.det (pointMatrix triplePoints t)=triple13 t := by
  have hm : pointMatrix triplePoints t= !![t, 0, -1, 0, 0, 0;
    0, t, -1, 0, -1, 0;
    -1, -1, t, -1, 0, -1;
    0, 0, -1, t, 0, 0;
    0, -1, 0, 0, t, -1;
    0, 0, -1, 0, -1, t] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [pointMatrix,triplePoints]
  rw [hm]
  simp (config := { maxSteps := 1000000 }) [Matrix.det_succ_row_zero,Fin.sum_univ_succ,
    Matrix.submatrix,Fin.succAbove,triple13,continuant,cycle]
  ring

theorem tripleFace_count : StripPolarization.faceDeterminant (Finset.univ.image triplePoints) 4=
    triple13 (4 : ℝ) := by
  rw [faceDeterminant_points triplePoints triplePoints_injective,triplePoints_det]

theorem opposite_count : StripPolarization.faceDeterminant (Finset.univ.image oppositePoints) 4=2656 := by
  rw [oppositeFace_count]
  norm_num [opposite13,continuant,cycle]

theorem ell_count : StripPolarization.faceDeterminant (Finset.univ.image ellPoints) 4=2640 := by
  rw [ellFace_count]
  norm_num [ell13,continuant,cycle]

theorem triple_count : StripPolarization.faceDeterminant (Finset.univ.image triplePoints) 4=2624 := by
  rw [tripleFace_count]
  norm_num [triple13,continuant,cycle]

end SpanningTreeIsoperimetry.ThirteenFaceCounts
