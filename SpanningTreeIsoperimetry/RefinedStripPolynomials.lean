import SpanningTreeIsoperimetry.RefinedQuadrantBoundary

/-! Exact determinant polynomials of the actual quadrant boundary strips.
Every interpolation candidate below is checked as a matrix identity. -/
namespace SpanningTreeIsoperimetry.RefinedStripPolynomials
open RefinedQuadrantBoundary BoundaryGreenRefined BoundaryGreenExtension BoundaryGreenPolynomials
open scoped Classical
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def stripLiteral1 (t : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  !![2 + (-16/3)*t]

def stripDet1 (t : ℝ) : ℝ := 2 + (-16/3)*t^1

set_option maxHeartbeats 4000000 in
theorem stripMatrix_eq_1 (t : ℝ) : stripMatrix t 1 (by decide) = stripLiteral1 t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stripMatrix,stripLiteral1,RefinedQuadrantBoundary.cornerEntry,planeEntry13,
      planeEntry,refinedLimit,refinedInitial,Nat.dist] <;> ring

set_option maxHeartbeats 40000000 in
theorem stripMatrix_det_1 (t : ℝ) : (stripMatrix t 1 (by decide)).det = stripDet1 t := by
  rw [stripMatrix_eq_1]
  simp (config := { maxSteps := 2000000 }) [Matrix.det_succ_row_zero,Fin.sum_univ_succ,
    Matrix.submatrix,Fin.succAbove,stripLiteral1,stripDet1]

def stripLiteral2 (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 + (-16/3)*t, (7/2) + (-32/3)*t;
    (7/2) + (-32/3)*t, 18 + (-832/15)*t]

def stripDet2 (t : ℝ) : ℝ := (95/4) + (-1984/15)*t^1 + (8192/45)*t^2

set_option maxHeartbeats 4000000 in
theorem stripMatrix_eq_2 (t : ℝ) : stripMatrix t 2 (by decide) = stripLiteral2 t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stripMatrix,stripLiteral2,RefinedQuadrantBoundary.cornerEntry,planeEntry13,
      planeEntry,refinedLimit,refinedInitial,Nat.dist] <;> ring

set_option maxHeartbeats 40000000 in
theorem stripMatrix_det_2 (t : ℝ) : (stripMatrix t 2 (by decide)).det = stripDet2 t := by
  rw [stripMatrix_eq_2]
  simp (config := { maxSteps := 2000000 }) [Matrix.det_succ_row_zero,Fin.sum_univ_succ,
    Matrix.submatrix,Fin.succAbove,stripLiteral2,stripDet2]
  ring

def stripLiteral3 (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2 + (-16/3)*t, (7/2) + (-32/3)*t, 16 + (-752/15)*t;
    (7/2) + (-32/3)*t, 18 + (-832/15)*t, (151/2) + (-1184/5)*t;
    16 + (-752/15)*t, (151/2) + (-1184/5)*t, 354 + (-116656/105)*t]

def stripDet3 (t : ℝ) : ℝ := 855 + (-735568/105)*t^1 + (29917184/1575)*t^2 + (-134217728/7875)*t^3

set_option maxHeartbeats 4000000 in
theorem stripMatrix_eq_3 (t : ℝ) : stripMatrix t 3 (by decide) = stripLiteral3 t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stripMatrix,stripLiteral3,RefinedQuadrantBoundary.cornerEntry,planeEntry13,
      planeEntry,refinedLimit,refinedInitial,Nat.dist] <;> ring

set_option maxHeartbeats 40000000 in
theorem stripMatrix_det_3 (t : ℝ) : (stripMatrix t 3 (by decide)).det = stripDet3 t := by
  rw [stripMatrix_eq_3]
  simp (config := { maxSteps := 2000000 }) [Matrix.det_succ_row_zero,Fin.sum_univ_succ,
    Matrix.submatrix,Fin.succAbove,stripLiteral3,stripDet3]
  ring

def stripLiteral4 (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2 + (-16/3)*t, (7/2) + (-32/3)*t, 16 + (-752/15)*t, 72 + (-3392/15)*t;
    (7/2) + (-32/3)*t, 18 + (-832/15)*t, (151/2) + (-1184/5)*t, 352 + (-116096/105)*t;
    16 + (-752/15)*t, (151/2) + (-1184/5)*t, 354 + (-116656/105)*t, (3375/2) + (-185536/35)*t;
    72 + (-3392/15)*t, 352 + (-116096/105)*t, (3375/2) + (-185536/35)*t, 8258 + (-8171776/315)*t]

def stripDet4 (t : ℝ) : ℝ := (2309953/16) + (-55871504/35)*t^1 + (217589008384/33075)*t^2 + (-41565619748864/3472875)*t^3 + (140737488355328/17364375)*t^4

set_option maxHeartbeats 4000000 in
theorem stripMatrix_eq_4 (t : ℝ) : stripMatrix t 4 (by decide) = stripLiteral4 t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stripMatrix,stripLiteral4,RefinedQuadrantBoundary.cornerEntry,planeEntry13,
      planeEntry,refinedLimit,refinedInitial,Nat.dist] <;> ring

set_option maxHeartbeats 40000000 in
theorem stripMatrix_det_4 (t : ℝ) : (stripMatrix t 4 (by decide)).det = stripDet4 t := by
  rw [stripMatrix_eq_4]
  simp (config := { maxSteps := 2000000 }) [Matrix.det_succ_row_zero,Fin.sum_univ_succ,
    Matrix.submatrix,Fin.succAbove,stripLiteral4,stripDet4]
  ring

def stripLiteral5 (t : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![2 + (-16/3)*t, (7/2) + (-32/3)*t, 16 + (-752/15)*t, 72 + (-3392/15)*t, 336 + (-36944/35)*t;
    (7/2) + (-32/3)*t, 18 + (-832/15)*t, (151/2) + (-1184/5)*t, 352 + (-116096/105)*t, 1684 + (-555488/105)*t;
    16 + (-752/15)*t, (151/2) + (-1184/5)*t, 354 + (-116656/105)*t, (3375/2) + (-185536/35)*t, 8256 + (-8170096/315)*t;
    72 + (-3392/15)*t, 352 + (-116096/105)*t, (3375/2) + (-185536/35)*t, 8258 + (-8171776/315)*t, (82255/2) + (-40699712/315)*t;
    336 + (-36944/35)*t, 1684 + (-555488/105)*t, 8256 + (-8170096/315)*t, (82255/2) + (-40699712/315)*t, 207906 + (-2263181488/3465)*t]

def stripDet5 (t : ℝ) : ℝ := (686248835/8) + (-813533911007/693)*t^1 + (2325815184105472/363825)*t^2 + (-77286472041889792/4465125)*t^3 + (840901426373504008192/36100535625)*t^4 + (-9444732965739290427392/758111248125)*t^5

set_option maxHeartbeats 4000000 in
theorem stripMatrix_eq_5 (t : ℝ) : stripMatrix t 5 (by decide) = stripLiteral5 t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stripMatrix,stripLiteral5,RefinedQuadrantBoundary.cornerEntry,planeEntry13,
      planeEntry,refinedLimit,refinedInitial,Nat.dist] <;> ring

set_option maxHeartbeats 40000000 in
theorem stripMatrix_det_5 (t : ℝ) : (stripMatrix t 5 (by decide)).det = stripDet5 t := by
  rw [stripMatrix_eq_5]
  simp (config := { maxSteps := 2000000 }) [Matrix.det_succ_row_zero,Fin.sum_univ_succ,
    Matrix.submatrix,Fin.succAbove,stripLiteral5,stripDet5]
  ring

def stripLiteral6 (t : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![2 + (-16/3)*t, (7/2) + (-32/3)*t, 16 + (-752/15)*t, 72 + (-3392/15)*t, 336 + (-36944/35)*t, 1612 + (-177248/35)*t;
    (7/2) + (-32/3)*t, 18 + (-832/15)*t, (151/2) + (-1184/5)*t, 352 + (-116096/105)*t, 1684 + (-555488/105)*t, 8240 + (-8154304/315)*t;
    16 + (-752/15)*t, (151/2) + (-1184/5)*t, 354 + (-116656/105)*t, (3375/2) + (-185536/35)*t, 8256 + (-8170096/315)*t, 41124 + (-40696352/315)*t;
    72 + (-3392/15)*t, 352 + (-116096/105)*t, (3375/2) + (-185536/35)*t, 8258 + (-8171776/315)*t, (82255/2) + (-40699712/315)*t, 207904 + (-2263163008/3465)*t;
    336 + (-36944/35)*t, 1684 + (-555488/105)*t, 8256 + (-8170096/315)*t, (82255/2) + (-40699712/315)*t, 207906 + (-2263181488/3465)*t, (2127863/2) + (-11581551008/3465)*t;
    1612 + (-177248/35)*t, 8240 + (-8154304/315)*t, 41124 + (-40696352/315)*t, 207904 + (-2263163008/3465)*t, (2127863/2) + (-11581551008/3465)*t, 5501074 + (-155694731968/9009)*t]

def stripDet6 (t : ℝ) : ℝ := (14221617122623/64) + (-165487567525737752/45045)*t^1 + (3931985867347893192704/156080925)*t^2 + (-2360880258143105981612032/25753352625)*t^3 + (10597972217734911254060859392/56786142538125)*t^4 + (-3573358049189666097461198848/17739803206125)*t^5 + (20282409603651670423947251286016/225384199733818125)*t^6

set_option maxHeartbeats 4000000 in
theorem stripMatrix_eq_6 (t : ℝ) : stripMatrix t 6 (by decide) = stripLiteral6 t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stripMatrix,stripLiteral6,RefinedQuadrantBoundary.cornerEntry,planeEntry13,
      planeEntry,refinedLimit,refinedInitial,Nat.dist] <;> ring

set_option maxHeartbeats 40000000 in
theorem stripMatrix_det_6 (t : ℝ) : (stripMatrix t 6 (by decide)).det = stripDet6 t := by
  rw [stripMatrix_eq_6]
  simp (config := { maxSteps := 2000000 }) [Matrix.det_succ_row_zero,Fin.sum_univ_succ,
    Matrix.submatrix,Fin.succAbove,stripLiteral6,stripDet6]
  ring

end
end SpanningTreeIsoperimetry.RefinedStripPolynomials
