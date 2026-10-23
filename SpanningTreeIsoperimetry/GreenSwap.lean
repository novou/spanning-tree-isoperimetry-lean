module

public import SpanningTreeIsoperimetry.GreenStripLimits

@[expose] public section

/-! Coordinate exchange for actual finite, strip and quadrant Green kernels. -/
namespace SpanningTreeIsoperimetry.GreenStripLimits
open Ferrers CornerEnergy BoundaryGreenLoss BoundaryGreenBounds SquareMaximality.Boundary
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem swap_mem_rectangle (R S : ℕ) (p : Point) : p.swap∈faceRectangle S R ↔ p∈faceRectangle R S := by
  simp only [mem_faceRectangle,Prod.fst_swap,Prod.snd_swap,and_comm]

def rectangleTranspose (R S : ℕ) : {p // p∈faceRectangle R S} ≃ {p // p∈faceRectangle S R} where
  toFun p := ⟨p.val.swap,(swap_mem_rectangle R S p.val).mpr p.property⟩
  invFun p := ⟨p.val.swap,(swap_mem_rectangle S R p.val).mpr p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rectangle_dirichlet_swap (R S : ℕ) :
    (fourIminusAdjacency (faceRectangle S R)).submatrix (rectangleTranspose R S) (rectangleTranspose R S)=
      fourIminusAdjacency (faceRectangle R S) := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp [Matrix.submatrix_apply,fourIminusAdjacency_apply,natManhattanDist]
  · simp [Matrix.submatrix_apply,fourIminusAdjacency_apply,hij,rectangleTranspose,
      natManhattanDist,add_comm]

theorem rectangle_green_swap (R S : ℕ) (p q : Point) :
    green (faceRectangle R S) p q=green (faceRectangle S R) p.swap q.swap := by
  by_cases hp : p∈faceRectangle R S
  · have hp' := (swap_mem_rectangle R S p).mpr hp
    by_cases hq : q∈faceRectangle R S
    · have hq' := (swap_mem_rectangle R S q).mpr hq
      rw [green_mem hp hq,green_mem hp' hq']
      have hi := congrArg (fun A => A⁻¹) (rectangle_dirichlet_swap R S)
      rw [Matrix.inv_submatrix_equiv] at hi
      exact (congrArg (fun A => A ⟨p,hp⟩ ⟨q,hq⟩) hi).symm
    · have hq' : q.swap∉faceRectangle S R := (swap_mem_rectangle R S q).not.mpr hq
      simp [green,hp,hp',hq,hq']
  · have hp' : p.swap∉faceRectangle S R := (swap_mem_rectangle R S p).not.mpr hp
    simp [green,hp,hp']

theorem stripY_swap (S : ℕ) (p q : Point) : stripY S p q=stripX S p.swap q.swap := by
  unfold stripY stripX
  exact congrArg (fun f : ℕ→ℝ => ⨆ R, f R)
    (funext (fun R => rectangle_green_swap R S p q))

theorem stripX_swap (R : ℕ) (p q : Point) : stripX R p q=stripY R p.swap q.swap := by
  rw [stripY_swap,Prod.swap_swap,Prod.swap_swap]

theorem quadrant_green_swap (p q : Point) : quadrantGreen p q=quadrantGreen p.swap q.swap := by
  unfold quadrantGreen
  exact congrArg (fun f : ℕ→ℝ => ⨆ N, f N)
    (funext (fun N => rectangle_green_swap (N+1) (N+1) p q))

theorem quadrant_loss_swap (R S : ℕ) (p q : Point) :
    quadrantLoss (faceRectangle R S) p q=quadrantLoss (faceRectangle S R) p.swap q.swap := by
  unfold quadrantLoss
  rw [quadrant_green_swap p q,rectangle_green_swap R S p q]

end
end SpanningTreeIsoperimetry.GreenStripLimits
