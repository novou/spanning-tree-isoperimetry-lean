import SpanningTreeIsoperimetry.RefinedQuadrantKernel
import SpanningTreeIsoperimetry.QuadrantMinorReduction
import SpanningTreeIsoperimetry.TwoTierFerrers

/-! Actual small-corner Green determinants, reduced by certified interior
Dirichlet rows. Every displayed affine entry and polynomial is proved below. -/
namespace SpanningTreeIsoperimetry.RefinedObstructionPolynomials
open Ferrers CornerEnergy TwoTierFerrers RefinedQuadrantKernel
open BoundaryGreenRefined BoundaryGreenExtension BoundaryGreenPolynomials RefinedQuadrantBoundary
open QuadrantMinorEnergy QuadrantMinorReduction Matrix
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace rectangle25

def diagram : Diagram := faceRectangle 5 2

def points : Fin 4 ⊕ Fin 6 → Point :=
  Sum.elim ![(0,0),(1,0),(2,0),(3,0)] ![(4,0),(0,1),(1,1),(2,1),(3,1),(4,1)]

theorem points_mem (i) : points i∈diagram := by
  rcases i with i|i <;> fin_cases i <;> decide

theorem points_small (i) : (points i).1+(points i).2<6 := by
  rcases i with i|i <;> fin_cases i <;> decide

def pointEquiv : Fin 4 ⊕ Fin 6 ≃ {p // p∈diagram} :=
  Equiv.ofBijective (fun i => ⟨points i,points_mem i⟩) (by decide +kernel)

def G11 (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![2 + (-16/3)*t, (7/2) + (-32/3)*t, 16 + (-752/15)*t, 72 + (-3392/15)*t;
    (7/2) + (-32/3)*t, 18 + (-832/15)*t, (151/2) + (-1184/5)*t, 352 + (-116096/105)*t;
    16 + (-752/15)*t, (151/2) + (-1184/5)*t, 354 + (-116656/105)*t, (3375/2) + (-185536/35)*t;
    72 + (-3392/15)*t, 352 + (-116096/105)*t, (3375/2) + (-185536/35)*t, 8258 + (-8171776/315)*t]

def G12 (t : ℝ) : Matrix (Fin 4) (Fin 6) ℝ :=
  !![336 + (-36944/35)*t, (7/2) + (-32/3)*t, -4 + (64/5)*t, (-23/2) + (544/15)*t, -64 + (1408/7)*t, -340 + (22432/21)*t;
    1684 + (-555488/105)*t, -4 + (64/5)*t, -8 + (128/5)*t, -68 + (7488/35)*t, (-703/2) + (38656/35)*t, -1856 + (1836736/315)*t;
    8256 + (-8170096/315)*t, (-23/2) + (544/15)*t, -68 + (7488/35)*t, -348 + (114848/105)*t, -1860 + (1840768/315)*t, (-19575/2) + (9685792/315)*t;
    (82255/2) + (-40699712/315)*t, -64 + (1408/7)*t, (-703/2) + (38656/35)*t, -1860 + (1840768/315)*t, -9784 + (9682432/315)*t, -51652 + (562265216/3465)*t]

def G21 (t : ℝ) : Matrix (Fin 6) (Fin 4) ℝ :=
  !![336 + (-36944/35)*t, 1684 + (-555488/105)*t, 8256 + (-8170096/315)*t, (82255/2) + (-40699712/315)*t;
    (7/2) + (-32/3)*t, -4 + (64/5)*t, (-23/2) + (544/15)*t, -64 + (1408/7)*t;
    -4 + (64/5)*t, -8 + (128/5)*t, -68 + (7488/35)*t, (-703/2) + (38656/35)*t;
    (-23/2) + (544/15)*t, -68 + (7488/35)*t, -348 + (114848/105)*t, -1860 + (1840768/315)*t;
    -64 + (1408/7)*t, (-703/2) + (38656/35)*t, -1860 + (1840768/315)*t, -9784 + (9682432/315)*t;
    -340 + (22432/21)*t, -1856 + (1836736/315)*t, (-19575/2) + (9685792/315)*t, -51652 + (562265216/3465)*t]

def G22 (t : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![207906 + (-2263181488/3465)*t, -340 + (22432/21)*t, -1856 + (1836736/315)*t, (-19575/2) + (9685792/315)*t, -51652 + (562265216/3465)*t, -273436 + (2976521888/3465)*t;
    -340 + (22432/21)*t, 18 + (-832/15)*t, -8 + (128/5)*t, 22 + (-7232/105)*t, (191/2) + (-10496/35)*t, 496 + (-490816/315)*t;
    -1856 + (1836736/315)*t, -8 + (128/5)*t, 40 + (-4352/35)*t, (175/2) + (-1920/7)*t, 518 + (-73216/45)*t, (5407/2) + (-891776/105)*t;
    (-19575/2) + (9685792/315)*t, 22 + (-7232/105)*t, (175/2) + (-1920/7)*t, 536 + (-75712/45)*t, (5391/2) + (-889088/105)*t, 14358 + (-156294464/3465)*t;
    -51652 + (562265216/3465)*t, (191/2) + (-10496/35)*t, 518 + (-73216/45)*t, (5391/2) + (-889088/105)*t, 14376 + (-156486656/3465)*t, (153231/2) + (-834004736/3465)*t;
    -273436 + (2976521888/3465)*t, 496 + (-490816/315)*t, (5407/2) + (-891776/105)*t, 14358 + (-156294464/3465)*t, (153231/2) + (-834004736/3465)*t, 411160 + (-11636887232/9009)*t]

def A : Matrix (Fin 4) (Fin 4) ℝ :=
  !![4, -1, 0, 0;
    -1, 4, -1, 0;
    0, -1, 4, -1;
    0, 0, -1, 4]

def B : Matrix (Fin 4) (Fin 6) ℝ :=
  !![0, -1, 0, 0, 0, 0;
    0, 0, -1, 0, 0, 0;
    0, 0, 0, -1, 0, 0;
    -1, 0, 0, 0, -1, 0]

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

def determinant (t : ℝ) : ℝ := (1411614608049967/64) + (-18367200896065910744/45045)*t^1 + (490119859147038501013504/156080925)*t^2 + (-18596600946583709302128640/1442187747)*t^3 + (5072931155628255330336388415488/170358427614375)*t^4 + (-8031277373626935719107185606656/219032264075625)*t^5 + (385365782469381738054997774434304/20489472703074375)*t^6

theorem interior_det : A.det=209 := by
  norm_num [A,Matrix.det_succ_row_zero,Fin.sum_univ_succ,Matrix.submatrix,Fin.succAbove]

set_option maxHeartbeats 40000000 in
theorem boundary_det (t : ℝ) : (G22 t).det=209*determinant t := by
  simp (config := {maxSteps := 2000000}) [G22,determinant,Matrix.det_succ_row_zero,
    Fin.sum_univ_succ,Matrix.submatrix,Fin.succAbove]
  ring

theorem full_det (t : ℝ) : (fromBlocks (G11 t) (G12 t) (G21 t) (G22 t)).det=determinant t := by
  rw [det_eq_boundary_div A B (G11 t) (G12 t) (G21 t) (G22 t)
    (by rw [interior_det]; norm_num) (interior_identity t) (interior_boundary t),
    boundary_det,interior_det]
  ring

theorem energy_exact : realEnergy diagram = -Real.log (determinant (1/Real.pi))-
    10*SquareMaximality.squareLatticeEntropy := by
  have h := energy_eq_log_det (M := diagram) (faceRectangle_isFerrers 5 2) pointEquiv
  rw [actual_matrix,full_det] at h
  have hc : diagram.card=10 := by decide +kernel
  rw [hc] at h
  norm_num at h
  simpa only [mul_comm,one_div] using h

theorem determinant_pos : 0<determinant (1/Real.pi) := by
  have h := quadrantMinor_det_pos (M := diagram) (faceRectangle_isFerrers 5 2) pointEquiv
  simpa only [actual_matrix,full_det] using h

end rectangle25
end
end SpanningTreeIsoperimetry.RefinedObstructionPolynomials
