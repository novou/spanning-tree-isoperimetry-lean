module

public import SpanningTreeIsoperimetry.RefinedQuadrantBoundary

@[expose] public section

/-! Exact affine kernels for the small triangular coordinate region needed
by all refined corner obstructions. The recurrence is the actual quadrant
Dirichlet equation, with both killing boundaries retained. -/
namespace SpanningTreeIsoperimetry.RefinedQuadrantKernel
open Ferrers BoundaryGreenBounds BoundaryGreenLoss RefinedQuadrantBoundary
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def boundaryValue (t : ℝ) (x u : ℕ) : ℝ :=
  if h : x<6 ∧ u<6 then cornerEntry t ⟨x,h.1⟩ ⟨u,h.2⟩ else 0

def lowerKernel (t : ℝ) (x y u : ℕ) : ℝ :=
  if hy : y=0 then boundaryValue t x u else
    4*lowerKernel t x (y-1) u-lowerKernel t (x+1) (y-1) u-
      (if x=0 then 0 else lowerKernel t (x-1) (y-1) u)-
      (if y-1=0 then 0 else lowerKernel t x ((y-1)-1) u)-
      (if (x,y-1)=(u,0) then 1 else 0)
termination_by y
decreasing_by all_goals omega

theorem lowerKernel_eq (x y u : ℕ) (hxy : x+y<6) (hu : u<6) :
    lowerKernel (1/Real.pi) x y u=quadrantGreen (x,y) (u,0) := by
  induction y using Nat.strong_induction_on generalizing x u with
  | h y ih =>
    by_cases hy : y=0
    · subst y
      rw [lowerKernel,dif_pos rfl,boundaryValue,dif_pos (show x<6 ∧ u<6 by omega)]
      exact (quadrantGreen_boundary ⟨x,by omega⟩ ⟨u,hu⟩).symm
    · rw [lowerKernel,dif_neg hy]
      rw [ih (y-1) (by omega) x u (by omega) hu,
        ih (y-1) (by omega) (x+1) u (by omega) hu,
        ih (y-1) (by omega) (x-1) u (by omega) hu,
        ih ((y-1)-1) (by omega) x u (by omega) hu]
      have h := quadrantGreen_equation (x,y-1) (u,0)
      simp only [laplacian,Prod.fst,Prod.snd,show y-1+1=y by omega] at h
      linarith

def kernelValue (t : ℝ) (x y u v : ℕ) : ℝ :=
  if hv : v=0 then lowerKernel t x y u else
    4*kernelValue t x y u (v-1)-kernelValue t x y (u+1) (v-1)-
      (if u=0 then 0 else kernelValue t x y (u-1) (v-1))-
      (if v-1=0 then 0 else kernelValue t x y u ((v-1)-1))-
      (if (x,y)=(u,v-1) then 1 else 0)
termination_by v
decreasing_by all_goals omega

theorem kernelValue_eq (x y u v : ℕ) (hxy : x+y<6) (huv : u+v<6) :
    kernelValue (1/Real.pi) x y u v=quadrantGreen (x,y) (u,v) := by
  induction v using Nat.strong_induction_on generalizing u with
  | h v ih =>
    by_cases hv : v=0
    · subst v
      rw [kernelValue,dif_pos rfl]
      exact lowerKernel_eq x y u hxy (by omega)
    · rw [kernelValue,dif_neg hv]
      rw [ih (v-1) (by omega) u (by omega),
        ih (v-1) (by omega) (u+1) (by omega),
        ih (v-1) (by omega) (u-1) (by omega),
        ih ((v-1)-1) (by omega) u (by omega)]
      have h := quadrantGreen_equation (u,v-1) (x,y)
      simp only [laplacian,Prod.fst,Prod.snd,show v-1+1=v by omega] at h
      rw [quadrantGreen_symm (u,v-1) (x,y),quadrantGreen_symm (u+1,v-1) (x,y),
        quadrantGreen_symm (u-1,v-1) (x,y),quadrantGreen_symm (u,v) (x,y),
        quadrantGreen_symm (u,(v-1)-1) (x,y)] at h
      have he : (u,v-1)=(x,y) ↔ (x,y)=(u,v-1) := eq_comm
      simp only [he] at h
      linarith

end
end SpanningTreeIsoperimetry.RefinedQuadrantKernel
