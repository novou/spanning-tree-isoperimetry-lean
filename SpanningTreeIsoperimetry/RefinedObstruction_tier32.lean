module

public import SpanningTreeIsoperimetry.RefinedQuadrantKernel
public import SpanningTreeIsoperimetry.QuadrantMinorReduction
public import SpanningTreeIsoperimetry.TwoTierFerrers

@[expose] public section

/-! Actual small-corner Green determinants, reduced by certified interior
Dirichlet rows. Every displayed affine entry and polynomial is proved below. -/
namespace SpanningTreeIsoperimetry.RefinedObstructionPolynomials
open Ferrers CornerEnergy TwoTierFerrers RefinedQuadrantKernel
open BoundaryGreenRefined BoundaryGreenExtension BoundaryGreenPolynomials RefinedQuadrantBoundary
open QuadrantMinorEnergy QuadrantMinorReduction Matrix
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace tier32

def diagram : Diagram := twoTier 2 1 1 1

def points : Fin 2 ⊕ Fin 3 → Point :=
  Sum.elim ![(0,0),(1,0)] ![(2,0),(0,1),(1,1)]

theorem points_mem (i) : points i∈diagram := by
  rcases i with i|i <;> fin_cases i <;> decide

theorem points_small (i) : (points i).1+(points i).2<6 := by
  rcases i with i|i <;> fin_cases i <;> decide

def pointEquiv : Fin 2 ⊕ Fin 3 ≃ {p // p∈diagram} :=
  Equiv.ofBijective (fun i => ⟨points i,points_mem i⟩) (by decide +kernel)

def G11 (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 + (-16/3)*t, (7/2) + (-32/3)*t;
    (7/2) + (-32/3)*t, 18 + (-832/15)*t]

def G12 (t : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  !![16 + (-752/15)*t, (7/2) + (-32/3)*t, -4 + (64/5)*t;
    (151/2) + (-1184/5)*t, -4 + (64/5)*t, -8 + (128/5)*t]

def G21 (t : ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  !![16 + (-752/15)*t, (151/2) + (-1184/5)*t;
    (7/2) + (-32/3)*t, -4 + (64/5)*t;
    -4 + (64/5)*t, -8 + (128/5)*t]

def G22 (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![354 + (-116656/105)*t, (-23/2) + (544/15)*t, -68 + (7488/35)*t;
    (-23/2) + (544/15)*t, 18 + (-832/15)*t, -8 + (128/5)*t;
    -68 + (7488/35)*t, -8 + (128/5)*t, 40 + (-4352/35)*t]

def A : Matrix (Fin 2) (Fin 2) ℝ :=
  !![4, -1;
    -1, 4]

def B : Matrix (Fin 2) (Fin 3) ℝ :=
  !![0, -1, 0;
    -1, 0, -1]

theorem actual_matrix : quadrantMinor (fun i => (pointEquiv i).val)=
    fromBlocks (G11 (1/Real.pi)) (G12 (1/Real.pi)) (G21 (1/Real.pi)) (G22 (1/Real.pi)) := by
  ext i j
  change BoundaryGreenBounds.quadrantGreen (points i) (points j)=_
  rw [← kernelValue_eq (points i).1 (points i).2 (points j).1 (points j).2
    (points_small i) (points_small j)]
  rcases i with i|i <;> rcases j with j|j <;> fin_cases i <;> fin_cases j <;>
    norm_num [points,G11,G12,G21,G22,Matrix.fromBlocks,kernelValue,lowerKernel,
      RefinedQuadrantKernel.boundaryValue,RefinedQuadrantBoundary.cornerEntry,
      planeEntry13,planeEntry,refinedLimit,refinedInitial,Nat.dist] <;> ring

theorem interior_identity (t : ℝ) : A*G11 t+B*G21 t=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A,B,G11,G21,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

theorem interior_boundary (t : ℝ) : A*G12 t+B*G22 t=0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A,B,G12,G22,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

def determinant (t : ℝ) : ℝ := 8746 + (-1697728/21)*t^1 + (1245184/5)*t^2 + (-134217728/525)*t^3

theorem interior_det : A.det=15 := by
  norm_num [A,Matrix.det_succ_row_zero,Fin.sum_univ_succ,Matrix.submatrix,Fin.succAbove]

set_option maxHeartbeats 40000000 in
theorem boundary_det (t : ℝ) : (G22 t).det=15*determinant t := by
  simp (config := {maxSteps := 2000000}) [G22,determinant,Matrix.det_succ_row_zero,
    Fin.sum_univ_succ,Matrix.submatrix,Fin.succAbove]
  ring

theorem full_det (t : ℝ) : (fromBlocks (G11 t) (G12 t) (G21 t) (G22 t)).det=determinant t := by
  rw [det_eq_boundary_div A B (G11 t) (G12 t) (G21 t) (G22 t)
    (by rw [interior_det]; norm_num) (interior_identity t) (interior_boundary t),
    boundary_det,interior_det]
  ring

theorem energy_exact : realEnergy diagram = -Real.log (determinant (1/Real.pi))-
    5*SquareMaximality.squareLatticeEntropy := by
  have h := energy_eq_log_det (M := diagram) (twoTier_isFerrers 2 1 1 1) pointEquiv
  rw [actual_matrix,full_det] at h
  have hc : diagram.card=5 := by decide +kernel
  rw [hc] at h
  norm_num at h
  simpa only [mul_comm,one_div] using h

theorem determinant_pos : 0<determinant (1/Real.pi) := by
  have h := quadrantMinor_det_pos (M := diagram) (twoTier_isFerrers 2 1 1 1) pointEquiv
  simpa only [actual_matrix,full_det] using h

end tier32
end
end SpanningTreeIsoperimetry.RefinedObstructionPolynomials
