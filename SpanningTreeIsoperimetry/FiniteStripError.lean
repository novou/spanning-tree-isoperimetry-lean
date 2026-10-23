module

public import SpanningTreeIsoperimetry.GreenLogDetComparison
public import SpanningTreeIsoperimetry.BoundaryFlux
public import SpanningTreeIsoperimetry.CornerLimit
public import SpanningTreeIsoperimetry.CornerEnergySymmetry

@[expose] public section

/-! Actual finite strip-energy correction bounded by the constructed quadrant
boundary flux. The explicit fourth-order kernel estimate is a later step. -/
namespace SpanningTreeIsoperimetry.FiniteStripError
open Ferrers CornerEnergy CornerStripBridge BoundaryGreenLoss BoundaryGreenBounds BoundaryFlux Filter
open scoped BigOperators Topology Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def stripFlux (U : Diagram) (k : ℕ) : ℝ :=
  (∑ a : Fin (k+1), quadrantLoss U (1,a.val) (0,a.val))+quadrantLoss U (0,k+1) (0,k)

theorem verticalDiagram_transpose (k : ℕ) : verticalDiagram k=transpose (horizontalStrip k) := by
  ext p
  simp only [mem_verticalDiagram,mem_transpose,mem_horizontalStrip,Prod.fst_swap,Prod.snd_swap]
  tauto

theorem verticalDiagram_energy (k : ℕ) : realEnergy (verticalDiagram k)=realEnergy (horizontalStrip k) := by
  rw [verticalDiagram_transpose,realEnergy_transpose]

/-- Exact finite-volume energy drop is bounded by the side/top flux of the
actual finite inverse difference; all logdet and Schur premises are discharged. -/
theorem finite_energy_drop_le_flux {R S T W : ℕ} {U V : Diagram}
    (hU : U⊆faceRectangle R S) (hV : V⊆faceRectangle T W) (hUV : U⊆V)
    (k : ℕ) (hstrip : verticalDiagram (k+1)⊆U) :
    dirichletEnergy hstrip-dirichletEnergy (Finset.Subset.trans hstrip hUV)≤
      (∑ a : Fin (k+1), loss U V (1,a.val) (0,a.val))+loss U V (0,k+1) (0,k) := by
  have h := GreenLogDetComparison.finite_green_logdet_bound hU hV hUV hstrip
  rw [← stripKernel_loss k hstrip (Finset.Subset.trans hstrip hUV),
    finite_green_loss_flux hU hV hUV k hstrip] at h
  unfold dirichletEnergy
  linarith only [h]

/-- Passage to actual quadrant entries and the already proved corner-energy
limit gives a finite strip-error bound with no infinite Green premise. -/
theorem energy_correction_le_flux {R S : ℕ} (k : ℕ)
    (hstrip : verticalDiagram (k+1)⊆faceRectangle R S) :
    dirichletEnergy hstrip-realEnergy (horizontalStrip (k+1))≤stripFlux (faceRectangle R S) k := by
  let V (N : ℕ) := box (N+(R+S))
  have hUV (N : ℕ) : faceRectangle R S⊆V N :=
    FiniteGreenMonotonicity.rectangle_subset (by omega) (by omega)
  let hfit (N : ℕ) : verticalDiagram (k+1)⊆V N := Finset.Subset.trans hstrip (hUV N)
  have hside : Tendsto (fun N : ℕ => N+(R+S)+1) atTop atTop := by
    apply tendsto_atTop_mono (fun N => show N≤N+(R+S)+1 by omega) tendsto_id
  have he : Tendsto (fun N => dirichletEnergy (hfit N)) atTop (𝓝 (realEnergy (verticalDiagram (k+1)))) :=
    dirichletEnergy_tendsto (verticalDiagram_ferrers (k+1)) hfit hside hside
  rw [verticalDiagram_energy] at he
  have hl (p q : Point) : Tendsto (fun N => loss (faceRectangle R S) (V N) p q) atTop
      (𝓝 (quadrantLoss (faceRectangle R S) p q)) := by
    have h := (green_tendsto_quadrant p q).comp (tendsto_add_atTop_nat (R+S))
    simpa only [Function.comp_def,loss,quadrantLoss,V] using h.sub_const (green (faceRectangle R S) p q)
  have hf : Tendsto (fun N =>
      (∑ a : Fin (k+1), loss (faceRectangle R S) (V N) (1,a.val) (0,a.val))+
        loss (faceRectangle R S) (V N) (0,k+1) (0,k)) atTop
      (𝓝 (stripFlux (faceRectangle R S) k)) :=
    (tendsto_finsetSum (Finset.univ : Finset (Fin (k+1))) (fun (a : Fin (k+1)) _ => hl (1,a.val) (0,a.val))).add (hl (0,k+1) (0,k))
  apply le_of_tendsto_of_tendsto' (tendsto_const_nhds.sub he) hf
  intro N
  exact finite_energy_drop_le_flux (Finset.Subset.refl (faceRectangle R S))
    (Finset.Subset.refl (V N)) (hUV N) k hstrip

theorem energy_correction_nonneg {R S : ℕ} (k : ℕ)
    (hstrip : verticalDiagram (k+1)⊆faceRectangle R S) :
    0≤dirichletEnergy hstrip-realEnergy (horizontalStrip (k+1)) := by
  rw [dirichletEnergy_eq (verticalDiagram_ferrers (k+1)),verticalDiagram_energy]
  linarith [correction_nonneg (faceRectangle R S) (verticalDiagram (k+1))]

end
end SpanningTreeIsoperimetry.FiniteStripError
