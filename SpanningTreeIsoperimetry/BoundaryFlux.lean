import SpanningTreeIsoperimetry.BoundaryGreenBounds
import SpanningTreeIsoperimetry.CornerStripBridge

/-! Cancellation along an actual finite corner strip leaves exactly the side
and top boundary flux. All finite Green functions are actual matrix inverses. -/
namespace SpanningTreeIsoperimetry.BoundaryFlux

open Ferrers CornerEnergy CornerStripBridge BoundaryGreenLoss SquareMaximality.Boundary
open scoped BigOperators Classical Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

abbrev StripSite (k : ℕ) := {p // p∈verticalDiagram (k+1)}

def stripSiteEquiv (k : ℕ) : StripSite k ≃ Fin (k+1) where
  toFun p := ⟨p.val.2,(mem_verticalDiagram.mp p.property).2⟩
  invFun a := ⟨(0,a.val),mem_verticalDiagram.mpr ⟨rfl,a.isLt⟩⟩
  left_inv p := by apply Subtype.ext; apply Prod.ext; exact (mem_verticalDiagram.mp p.property).1.symm; rfl
  right_inv _ := rfl

/-- Restrict a two-point kernel to the actual strip face set. -/
def stripKernel (F : Point → Point → ℝ) (k : ℕ) : Matrix (StripSite k) (StripSite k) ℝ :=
  fun p q => F p.val q.val

theorem stripKernel_green {U : Diagram} (k : ℕ) (hstrip : verticalDiagram (k+1)⊆U) :
    stripKernel (green U) k=greenMinor hstrip := by
  ext p q
  exact green_mem (hstrip p.property) (hstrip q.property)

theorem stripKernel_loss {U V : Diagram} (k : ℕ)
    (hstripU : verticalDiagram (k+1)⊆U) (hstripV : verticalDiagram (k+1)⊆V) :
    stripKernel (loss U V) k=greenMinor hstripV-greenMinor hstripU := by
  ext p q
  simp only [stripKernel,loss,Matrix.sub_apply,green_mem (hstripU p.property) (hstripU q.property),
    green_mem (hstripV p.property) (hstripV q.property),greenMinor,Matrix.submatrix_apply]

/-- A row of the path Dirichlet matrix cancels the internal neighbors of a
harmonic kernel, leaving the perpendicular neighbor and possibly the top one. -/
theorem strip_row_flux (F : Point → Point → ℝ) (k : ℕ)
    (hh : ∀ a b : StripSite k, laplacian (fun t => F t b.val) a.val=0)
    (a b : StripSite k) :
    (fourIminusAdjacency (verticalDiagram (k+1))*stripKernel F k) a b=
      F (1,a.val.2) b.val+(if a.val.2=k then F (0,k+1) b.val else 0) := by
  change (fourIminusAdjacency (verticalDiagram (k+1)) *ᵥ
    (fun p => F p.val b.val)) a = _
  rw [dirichlet_mulVec]
  obtain ⟨⟨x,y⟩,ha⟩ := a
  have hap := mem_verticalDiagram.mp ha
  dsimp only at hap
  have hx : x=0 := hap.1
  subst x
  have h := hh ⟨(0,y),ha⟩ b
  dsimp only at h ⊢
  have hside : (1,y)∉verticalDiagram (k+1) := by simp [mem_verticalDiagram]
  simp only [laplacian,Prod.fst,Prod.snd,zero_add,ite_true,sub_zero] at h ⊢
  rw [extend_mem _ ha,extend_not_mem _ hside]
  by_cases hy : y=k
  · subst y
    have htop : (0,k+1)∉verticalDiagram (k+1) := by simp [mem_verticalDiagram]
    rw [extend_not_mem _ htop]
    by_cases hk : k=0
    · simp only [hk,ite_true,sub_zero] at h ⊢
      linarith
    · have hprev : (0,k-1)∈verticalDiagram (k+1) := mem_verticalDiagram.mpr ⟨rfl,by omega⟩
      simp only [hk,ite_false,ite_true,extend_mem _ hprev] at h ⊢
      linarith
  · have hnext : (0,y+1)∈verticalDiagram (k+1) := mem_verticalDiagram.mpr ⟨rfl,by omega⟩
    rw [extend_mem _ hnext]
    by_cases hy0 : y=0
    · have hne : 0≠k := by omega
      simp only [hy0,ite_true,sub_zero,hne,ite_false,add_zero] at h ⊢
      linarith
    · have hprev : (0,y-1)∈verticalDiagram (k+1) := mem_verticalDiagram.mpr ⟨rfl,by omega⟩
      simp only [hy0,ite_false,hy,extend_mem _ hprev,add_zero] at h ⊢
      linarith

/-- The exact boundary-flux identity for any kernel harmonic in its first
variable on the strip. The next theorem instantiates it with actual Green loss. -/
theorem trace_flux (F : Point → Point → ℝ) (k : ℕ)
    (hh : ∀ a b : StripSite k, laplacian (fun t => F t b.val) a.val=0) :
    Matrix.trace (fourIminusAdjacency (verticalDiagram (k+1))*stripKernel F k)=
      (∑ a : Fin (k+1), F (1,a.val) (0,a.val))+F (0,k+1) (0,k) := by
  change (∑ a : StripSite k, (fourIminusAdjacency (verticalDiagram (k+1))*stripKernel F k) a a)=_
  simp_rw [strip_row_flux F k hh]
  rw [Finset.sum_add_distrib]
  have hside : (∑ a : StripSite k, F (1,a.val.2) a.val)=
      ∑ a : Fin (k+1), F (1,a.val) (0,a.val) := by
    calc
      _ = ∑ a : StripSite k, F (1,(stripSiteEquiv k a).val) (0,(stripSiteEquiv k a).val) := by
        apply Finset.sum_congr rfl
        intro a _
        dsimp only [stripSiteEquiv,Equiv.coe_fn_mk]
        congr 1
        exact Prod.ext (mem_verticalDiagram.mp a.property).1 rfl
      _ = _ := (stripSiteEquiv k).sum_comp (fun a : Fin (k+1) => F (1,a.val) (0,a.val))
  rw [hside]
  congr 1
  have hl : (0,k)∈verticalDiagram (k+1) := mem_verticalDiagram.mpr ⟨rfl,by omega⟩
  have he (a : StripSite k) : a.val.2=k ↔ a.val=(0,k) := by
    have hx := (mem_verticalDiagram.mp a.property).1
    simp only [Prod.ext_iff]
    simp [hx]
  simp only [he]
  have hs := sum_delta_extend (verticalDiagram (k+1)) (fun a => F (0,k+1) a.val) (0,k)
  simpa only [ite_mul,one_mul,zero_mul,extend_mem _ hl] using hs

/-- Appendix A's Green-flux equality before the quadrant limit: it already
holds for every pair of containing finite domains. -/
theorem finite_green_loss_flux {R S T W : ℕ} {U V : Diagram}
    (hU : U⊆faceRectangle R S) (hV : V⊆faceRectangle T W) (hUV : U⊆V)
    (k : ℕ) (hstrip : verticalDiagram (k+1)⊆U) :
    Matrix.trace (fourIminusAdjacency (verticalDiagram (k+1))*stripKernel (loss U V) k)=
      (∑ a : Fin (k+1), loss U V (1,a.val) (0,a.val))+loss U V (0,k+1) (0,k) := by
  apply trace_flux
  intro a b
  exact loss_harmonic hU hV hUV (hstrip a.property) (hstrip b.property)

/-- The actual quadrant-minus-finite Green loss satisfies the paper's exact
boundary flux identity, with the quadrant kernel constructed by finite limits. -/
theorem quadrant_green_loss_flux {R S : ℕ} {U : Diagram}
    (hU : U⊆faceRectangle R S) (k : ℕ) (hstrip : verticalDiagram (k+1)⊆U) :
    Matrix.trace (fourIminusAdjacency (verticalDiagram (k+1))*
      stripKernel (BoundaryGreenBounds.quadrantLoss U) k)=
      (∑ a : Fin (k+1), BoundaryGreenBounds.quadrantLoss U (1,a.val) (0,a.val))+
        BoundaryGreenBounds.quadrantLoss U (0,k+1) (0,k) := by
  apply trace_flux
  intro a b
  exact BoundaryGreenBounds.quadrantLoss_harmonic hU (hstrip a.property) (hstrip b.property)

end
end SpanningTreeIsoperimetry.BoundaryFlux
