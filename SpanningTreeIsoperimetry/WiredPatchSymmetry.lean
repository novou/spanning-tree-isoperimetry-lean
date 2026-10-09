import SpanningTreeIsoperimetry.WiredRayleigh
import SpanningTreeIsoperimetry.FreePatchBridge

/-! The south/west free-patch margin follows by a finite half-turn wiring. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SpanningTreeIsoperimetry.WiredPatchSymmetry

open SquareMaximality SquareMaximality.Dual SquareMaximality.Multigraph
open WiredRayleigh

noncomputable section

/-- Half-turn of the free five-by-five patch. -/
def halfTurnVertex (v : Fin 5 × Fin 5) : Fin 5 × Fin 5 := (v.1.rev, v.2.rev)

def halfTurnEdge : RectangleEdge 5 5 → RectangleEdge 5 5
  | .horizontal e => .horizontal ⟨e.x.rev, e.y.rev⟩
  | .vertical e => .vertical ⟨e.x.rev, e.y.rev⟩

theorem halfTurnEdge_involutive : Function.Involutive halfTurnEdge := by
  unfold Function.Involutive
  decide +kernel

theorem halfTurn_ends : ∀ e : RectangleEdge 5 5,
    (rectanglePrimal 5 5).ends (halfTurnEdge e) =
      Sym2.map halfTurnVertex ((rectanglePrimal 5 5).ends e) := by
  decide +kernel

theorem halfTurn_active : ∀ e : RectangleEdge 5 5,
    ¬(Sym2.map halfTurnVertex ((rectanglePrimal 5 5).ends e)).IsDiag := by
  decide +kernel

def halfTurnWiring : Wiring (rectanglePrimal 5 5) (rectanglePrimal 5 5) where
  vertexMap := halfTurnVertex
  edgeMap :=
    { toFun := fun e => halfTurnEdge e.1
      inj' := fun e f h => Subtype.ext (halfTurnEdge_involutive.injective h) }
  map_ends e := halfTurn_ends e.1

def southWestLabels : Finset (RectangleEdge 5 5) :=
  {.horizontal ⟨1,2⟩, .vertical ⟨2,1⟩}

theorem mem_selectedLabels_iff {V W E F : Type*}
    [Fintype V] [Fintype W] [Fintype E] [Fintype F]
    {G : LabeledMultigraph V E} {H : LabeledMultigraph W F}
    (d : Wiring G H) (A : Finset E)
    (hA : ∀ e ∈ A, ¬(Sym2.map d.vertexMap (G.ends e)).IsDiag) (f : F) :
    f ∈ d.selectedLabels A hA ↔ ∃ e : A, d.selectedLabelMap A hA e = f := by
  classical
  simp only [Wiring.selectedLabels, Finset.mem_image, Finset.mem_attach, true_and]

theorem halfTurn_selectedLabels :
    halfTurnWiring.selectedLabels FreePatchBridge.centralLabels
      (fun e _ => halfTurn_active e) = southWestLabels := by
  classical
  let A := FreePatchBridge.centralLabels
  let hA := fun e (_ : e ∈ A) => halfTurn_active e
  let se : RectangleEdge 5 5 := .horizontal ⟨2,2⟩
  let sf : RectangleEdge 5 5 := .vertical ⟨2,2⟩
  have heA : se ∈ A := by simp [se,A,FreePatchBridge.centralLabels]
  have hfA : sf ∈ A := by simp [sf,A,FreePatchBridge.centralLabels]
  have hmapE : halfTurnWiring.selectedLabelMap A hA ⟨se,heA⟩ = .horizontal ⟨1,2⟩ := rfl
  have hmapF : halfTurnWiring.selectedLabelMap A hA ⟨sf,hfA⟩ = .vertical ⟨2,1⟩ := rfl
  change halfTurnWiring.selectedLabels A hA = southWestLabels
  ext e
  constructor
  · intro he
    obtain ⟨u,hu⟩ := (mem_selectedLabels_iff halfTurnWiring A hA e).mp he
    have huA : u.1 = se ∨ u.1 = sf := by simpa only [A,FreePatchBridge.centralLabels,se,sf,Finset.mem_insert,Finset.mem_singleton] using u.2
    rcases huA with hus | huf
    · have hu' : u = ⟨se,heA⟩ := Subtype.ext hus
      rw [hu',hmapE] at hu
      simp [southWestLabels,← hu]
    · have hu' : u = ⟨sf,hfA⟩ := Subtype.ext huf
      rw [hu',hmapF] at hu
      simp [southWestLabels,← hu]
  · intro he
    have he' : e = RectangleEdge.horizontal ⟨1,2⟩ ∨ e = RectangleEdge.vertical ⟨2,1⟩ := by
      simpa [southWestLabels] using he
    rcases he' with rfl | rfl
    · exact (mem_selectedLabels_iff halfTurnWiring A hA _).mpr ⟨⟨se,heA⟩,hmapE⟩
    · exact (mem_selectedLabels_iff halfTurnWiring A hA _).mpr ⟨⟨sf,hfA⟩,hmapF⟩

/-- The same strict avoidance margin holds for the opposite corner directions. -/
theorem southWest_avoidanceRatio_gt :
    (3 : ℝ) / 16 < (rectanglePrimal 5 5).avoidanceRatio southWestLabels := by
  have hCount : 0 < (rectanglePrimal 5 5).spanningTreeCount := by
    rw [FreePatchBridge.labelledPatch_treeCount]
    norm_num
  have h := halfTurnWiring.avoidanceRatio_le (0,0) (0,0) FreePatchBridge.centralLabels
    (fun e _ => halfTurn_active e) hCount hCount
  rw [halfTurn_selectedLabels] at h
  exact FreePatchBridge.labelledPatch_avoidanceRatio_gt.trans_le h

end
end SpanningTreeIsoperimetry.WiredPatchSymmetry
