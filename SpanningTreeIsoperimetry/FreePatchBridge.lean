module

public import SpanningTreeIsoperimetry.AvoidanceDeterminant
public import SpanningTreeIsoperimetry.InteriorSurcharge
public import SquareMaximality.Dual.Rectangle

@[expose] public section

/-! The labelled five-by-five primal patch has exactly the already checked
free-patch avoidance probability. The cofactor entries are identified
exactly; the determinant evaluations are reused, not assumed. -/
namespace SpanningTreeIsoperimetry.FreePatchBridge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open SquareMaximality.Multigraph SquareMaximality.Multigraph.LabeledMultigraph
open SquareMaximality.Dual
open scoped BigOperators

def patchVertexEquiv : Fin 25 ≃ Fin 5 × Fin 5 :=
  (finProdFinEquiv (m := 5) (n := 5)).symm

def centralLabels : Finset (RectangleEdge 5 5) :=
  {.horizontal ⟨2,2⟩, .vertical ⟨2,2⟩}

def cutEnds (e : RectangleEdge 5 5) : Sym2 (Fin 5 × Fin 5) :=
  if e ∈ centralLabels then s((0,0),(0,0)) else (rectanglePrimal 5 5).ends e

/-- A computable entry formula for a labelled graph's integer Laplacian. -/
def explicitLaplacian {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (ends : E → Sym2 V) : Matrix V V ℤ :=
  let a : V → V → ℕ := fun u v => if u=v then 0 else
    (Finset.univ.filter (fun e => ends e=s(u,v))).card
  fun u v => if u=v then ∑ w, (a u w : ℤ) else -(a u v : ℤ)

theorem explicitLaplacian_eq {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : LabeledMultigraph V E) : explicitLaplacian G.ends = G.laplacian ℤ := by
  classical
  ext u v
  simp [explicitLaplacian,laplacian,degree,adjacencyMultiplicity,edgeMultiplicity,
    Nat.card_eq_fintype_card,Fintype.card_subtype,IsLink] <;> rfl

def patchCofactorEquiv : Fin 24 ≃ AwayFrom ((0,0) : Fin 5 × Fin 5) :=
  (finSuccAboveEquiv (0 : Fin 25)).trans
    (patchVertexEquiv.subtypeEquiv (fun i => by
      have hz : patchVertexEquiv 0 = (0,0) := by decide
      rw [← hz,patchVertexEquiv.injective.ne_iff]))

theorem patchCofactorEquiv_val (i : Fin 24) :
    (patchCofactorEquiv i).val = patchVertexEquiv i.succ := rfl

def patchCofactor : Matrix (Fin 24) (Fin 24) ℤ :=
  (explicitLaplacian (rectanglePrimal 5 5).ends).submatrix
    (fun i => patchVertexEquiv i.succ) (fun i => patchVertexEquiv i.succ)

def deletedPatchCofactor : Matrix (Fin 24) (Fin 24) ℤ :=
  (explicitLaplacian cutEnds).submatrix
    (fun i => patchVertexEquiv i.succ) (fun i => patchVertexEquiv i.succ)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem patchCofactor_eq : patchCofactor = InteriorSurcharge.freePatchCofactor := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 64000000 in
theorem deletedPatchCofactor_eq : deletedPatchCofactor = InteriorSurcharge.cutPatchCofactor := by
  decide +kernel

theorem reindexed_cofactor (G : LabeledMultigraph (Fin 5 × Fin 5) (RectangleEdge 5 5)) :
    ((G.reducedLaplacian ℤ (0,0)).submatrix patchCofactorEquiv patchCofactorEquiv) =
      (explicitLaplacian G.ends).submatrix
        (fun i => patchVertexEquiv i.succ) (fun i => patchVertexEquiv i.succ) := by
  rw [explicitLaplacian_eq]
  rfl

theorem labelledPatch_treeCount : (rectanglePrimal 5 5).spanningTreeCount = 557568000 := by
  have h := SquareMaximality.labeledMultigraphCofactorInput _ _ (rectanglePrimal 5 5) (0,0)
  rw [← Matrix.det_submatrix_equiv_self patchCofactorEquiv,reindexed_cofactor] at h
  change ((rectanglePrimal 5 5).spanningTreeCount : ℤ) = patchCofactor.det at h
  rw [patchCofactor_eq,InteriorSurcharge.freePatchCofactor_det] at h
  exact_mod_cast h

theorem labelledPatch_avoidanceCount : (rectanglePrimal 5 5).avoidanceCount centralLabels = 107976960 := by
  have h := SquareMaximality.labeledMultigraphCofactorInput _ _
    ((rectanglePrimal 5 5).loopDelete (0,0) centralLabels) (0,0)
  rw [loopDelete_treeCount,← Matrix.det_submatrix_equiv_self patchCofactorEquiv,
    reindexed_cofactor] at h
  have he : ((rectanglePrimal 5 5).loopDelete (0,0) centralLabels).ends = cutEnds := by
    funext e
    by_cases he : e ∈ centralLabels <;> simp [loopDelete,cutEnds,he]
  rw [he] at h
  change ((rectanglePrimal 5 5).avoidanceCount centralLabels : ℤ) = deletedPatchCofactor.det at h
  rw [deletedPatchCofactor_eq,InteriorSurcharge.cutPatchCofactor_det] at h
  exact_mod_cast h

theorem labelledPatch_avoidanceRatio :
    (rectanglePrimal 5 5).avoidanceRatio centralLabels = (9373 : ℝ)/48400 := by
  unfold avoidanceRatio
  rw [labelledPatch_treeCount,labelledPatch_avoidanceCount]
  norm_num

theorem labelledPatch_avoidanceRatio_gt :
    (3 : ℝ)/16 < (rectanglePrimal 5 5).avoidanceRatio centralLabels := by
  rw [labelledPatch_avoidanceRatio]
  norm_num

end SpanningTreeIsoperimetry.FreePatchBridge
