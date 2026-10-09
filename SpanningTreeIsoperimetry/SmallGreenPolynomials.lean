import SpanningTreeIsoperimetry.BoundaryLayerGreen

/-! Checked determinant polynomials for the square, 3-by-2 rectangle,
and length-four boundary strip. Every candidate is verified as an identity. -/
namespace SpanningTreeIsoperimetry.SmallGreenPolynomials
open BoundaryLayerGreen BoundaryGreenPolynomials
open scoped Classical
noncomputable section

def squarePoints : Fin 4 → Fin 3 × Fin 2 := ![(0,0),(0,1),(1,0),(1,1)]

def squareMatrix (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (twoRowValue t).submatrix squarePoints squarePoints

def squareLiteral (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2 + (-16/3)*t, (7/2) + (-32/3)*t, (7/2) + (-32/3)*t, -4 + (64/5)*t;
    (7/2) + (-32/3)*t, 18 + (-832/15)*t, -4 + (64/5)*t, -8 + (128/5)*t;
    (7/2) + (-32/3)*t, -4 + (64/5)*t, 18 + (-832/15)*t, -8 + (128/5)*t;
    -4 + (64/5)*t, -8 + (128/5)*t, -8 + (128/5)*t, 40 + (-4352/35)*t]

def squareDet (t : ℝ) : ℝ := 2376 + (-327424/15)*t^1 + (105250816/1575)*t^2 + (-536870912/7875)*t^3

set_option maxHeartbeats 1000000 in
theorem squareMatrix_eq (t : ℝ) : squareMatrix t=squareLiteral t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [squareMatrix,squareLiteral,squarePoints,twoRowValue,crossValue,upperValue,
      cornerEntry,planeEntry,lowerIndex,nextIndex,prevIndex,Nat.dist,Matrix.submatrix] <;> ring

set_option maxHeartbeats 4000000 in
 theorem squareMatrix_det (t : ℝ) : Matrix.det (squareMatrix t)=squareDet t := by
  rw [squareMatrix_eq]
  simp (config := { maxSteps := 1000000 }) [Matrix.det_succ_row_zero,Fin.sum_univ_succ,
    Matrix.submatrix,Fin.succAbove,squareLiteral,squareDet]
  ring

def rectanglePoints : Fin 6 → Fin 3 × Fin 2 := ![(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)]

def rectangleMatrix (t : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  (twoRowValue t).submatrix rectanglePoints rectanglePoints

def rectangleLiteral (t : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![2 + (-16/3)*t, (7/2) + (-32/3)*t, (7/2) + (-32/3)*t, -4 + (64/5)*t, 16 + (-752/15)*t, (-23/2) + (544/15)*t;
    (7/2) + (-32/3)*t, 18 + (-832/15)*t, -4 + (64/5)*t, -8 + (128/5)*t, (-23/2) + (544/15)*t, 22 + (-7232/105)*t;
    (7/2) + (-32/3)*t, -4 + (64/5)*t, 18 + (-832/15)*t, -8 + (128/5)*t, (151/2) + (-1184/5)*t, -68 + (7488/35)*t;
    -4 + (64/5)*t, -8 + (128/5)*t, -8 + (128/5)*t, 40 + (-4352/35)*t, -68 + (7488/35)*t, (175/2) + (-1920/7)*t;
    16 + (-752/15)*t, (-23/2) + (544/15)*t, (151/2) + (-1184/5)*t, -68 + (7488/35)*t, 354 + (-116656/105)*t, -348 + (114848/105)*t;
    (-23/2) + (544/15)*t, 22 + (-7232/105)*t, -68 + (7488/35)*t, (175/2) + (-1920/7)*t, -348 + (114848/105)*t, 536 + (-75712/45)*t]

def rectangleDet (t : ℝ) : ℝ := (21428111/16) + (-744293776/45)*t^1 + (361874966528/4725)*t^2 + (-60809220718592/385875)*t^3 + (140737488355328/1157625)*t^4

set_option maxHeartbeats 1000000 in
theorem rectangleMatrix_eq (t : ℝ) : rectangleMatrix t=rectangleLiteral t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rectangleMatrix,rectangleLiteral,rectanglePoints,twoRowValue,crossValue,upperValue,
      cornerEntry,planeEntry,lowerIndex,nextIndex,prevIndex,Nat.dist,Matrix.submatrix] <;> ring

set_option maxHeartbeats 4000000 in
 theorem rectangleMatrix_det (t : ℝ) : Matrix.det (rectangleMatrix t)=rectangleDet t := by
  rw [rectangleMatrix_eq]
  simp (config := { maxSteps := 1000000 }) [Matrix.det_succ_row_zero,Fin.sum_univ_succ,
    Matrix.submatrix,Fin.succAbove,rectangleLiteral,rectangleDet]
  ring

def stripMatrix (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := fun i j => cornerEntry t i j

def stripLiteral (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2 + (-16/3)*t, (7/2) + (-32/3)*t, 16 + (-752/15)*t, 72 + (-3392/15)*t;
    (7/2) + (-32/3)*t, 18 + (-832/15)*t, (151/2) + (-1184/5)*t, 352 + (-116096/105)*t;
    16 + (-752/15)*t, (151/2) + (-1184/5)*t, 354 + (-116656/105)*t, (3375/2) + (-185536/35)*t;
    72 + (-3392/15)*t, 352 + (-116096/105)*t, (3375/2) + (-185536/35)*t, 8258 + (-8171776/315)*t]

def stripDet (t : ℝ) : ℝ := (2309953/16) + (-55871504/35)*t^1 + (217589008384/33075)*t^2 + (-41565619748864/3472875)*t^3 + (140737488355328/17364375)*t^4

theorem stripMatrix_eq (t : ℝ) : stripMatrix t=stripLiteral t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stripMatrix,stripLiteral,twoRowValue,crossValue,upperValue,
      cornerEntry,planeEntry,lowerIndex,nextIndex,prevIndex,Nat.dist,Matrix.submatrix] <;> ring

set_option maxHeartbeats 4000000 in
 theorem stripMatrix_det (t : ℝ) : Matrix.det (stripMatrix t)=stripDet t := by
  rw [stripMatrix_eq]
  simp (config := { maxSteps := 1000000 }) [Matrix.det_succ_row_zero,Fin.sum_univ_succ,
    Matrix.submatrix,Fin.succAbove,stripLiteral,stripDet]
  ring

end
end SpanningTreeIsoperimetry.SmallGreenPolynomials
