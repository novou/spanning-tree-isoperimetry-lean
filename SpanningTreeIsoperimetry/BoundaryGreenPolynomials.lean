import SpanningTreeIsoperimetry.BoundaryGreenExtension
import Mathlib.Data.Nat.Dist

/-! Affine polynomials for the checked half-plane and quadrant boundary sums. -/
namespace SpanningTreeIsoperimetry.BoundaryGreenPolynomials
open BoundaryGreen BoundaryGreenExtension
noncomputable section

def planeEntry (t : ℝ) (j : Fin 9) : ℝ :=
  ![1-2*t,-1/2+2*t,-1+(10/3)*t,-4+(38/3)*t,-17+(802/15)*t,
    -76+(1194/5)*t,-353+(116446/105)*t,-1688+(185606/35)*t,-8257+(8171146/315)*t] j

theorem boundaryValueNine_eq (j : Fin 9) : boundaryValueNine j=planeEntry (1/Real.pi) j := by
  fin_cases j <;> norm_num [boundaryValueNine,planeEntry,extraValue,extraLimit,extraInitial,
    boundaryValue,limitSix,initialSix] <;> ring

def cornerEntry (t : ℝ) (i j : Fin 4) : ℝ :=
  planeEntry t ⟨Nat.dist i.val j.val,by have hi:=i.isLt; have hj:=j.isLt; unfold Nat.dist; omega⟩-
    planeEntry t ⟨i.val+j.val+2,by have hi:=i.isLt; have hj:=j.isLt; omega⟩

end
end SpanningTreeIsoperimetry.BoundaryGreenPolynomials
