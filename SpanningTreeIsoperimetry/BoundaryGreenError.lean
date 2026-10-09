import SpanningTreeIsoperimetry.BoundaryLossKernel

/-! The actual two-boundary fourth-order Green loss, combining the proved
one-boundary integral bounds with finite-word inclusion/exclusion. -/
namespace SpanningTreeIsoperimetry.BoundaryGreenError
open Ferrers CornerEnergy BoundaryGreenLoss BoundaryGreenBounds GreenStripLimits BoundaryLossKernel
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def entryBound (R S : ℕ) (p q : Point) : ℝ :=
  Real.pi^3*((p.1 : ℝ)+1)*((q.1 : ℝ)+1)*((p.2 : ℝ)+1)*((q.2 : ℝ)+1)/60*
    (1/(((R : ℝ)+1)^2-(((max p.1 q.1 : ℕ) : ℝ)+1)^2)^2+
     1/(((S : ℝ)+1)^2-(((max p.2 q.2 : ℕ) : ℝ)+1)^2)^2)

/-- Every quantity here is an actual finite inverse or its constructed
quadrant limit. The two boundary events are joined by the checked walk bound. -/
theorem quadrantLoss_le_entryBound {R S : ℕ} {p q : Point}
    (hp : p∈faceRectangle R S) (hq : q∈faceRectangle R S) :
    quadrantLoss (faceRectangle R S) p q≤entryBound R S p q := by
  have hp' := mem_faceRectangle.mp hp
  have hq' := mem_faceRectangle.mp hq
  have hx := stripX_loss_le R ⟨p.1,hp'.1⟩ ⟨q.1,hq'.1⟩ p.2 q.2
  have hy := stripX_loss_le S ⟨p.2,hp'.2⟩ ⟨q.2,hq'.2⟩ p.1 q.1
  change quadrantGreen p q-stripX R p q≤_ at hx
  change quadrantGreen p.swap q.swap-stripX S p.swap q.swap≤_ at hy
  rw [← quadrant_green_swap p q,← stripY_swap S p q] at hy
  have h := (quadrant_loss_le_strip_losses hp hq).trans (add_le_add hx hy)
  change quadrantLoss (faceRectangle R S) p q≤_ at h
  unfold entryBound
  convert h using 1
  simp only [div_mul_eq_div_div]
  ring

end
end SpanningTreeIsoperimetry.BoundaryGreenError
