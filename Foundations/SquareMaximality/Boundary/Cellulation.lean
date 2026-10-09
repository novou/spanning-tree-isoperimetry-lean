import SquareMaximality.Boundary.MarkedCount
import Mathlib.Data.Int.NatAbs

set_option autoImplicit false

/-!
# Constructing the finite cellulation certificate

`GridCellulationCertificate` asks for two pieces of data: a labelled spanning
tree and a bijection between its complementary labels and the unmarked unit
faces.  The first part is not an additional planar assumption.  This file
constructs it from ordinary connectivity, including the bookkeeping needed to
choose one multigraph label above every edge of a simple spanning tree.

Consequently the certificate follows from connectivity and the numerical
Euler identity.  This isolates the remaining planar obligation as an equality
of finite cardinalities rather than a bundled choice of a tree and a
bijection.
-/

namespace SquareMaximality

namespace Multigraph

namespace LabeledMultigraph

variable {V E : Type*} (G : LabeledMultigraph V E)

section SpanningTreeExistence

variable [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
private theorem exists_labelAbove
    (T : SimpleGraph V) (hTG : T ≤ G.toSimpleGraph)
    (p : T.edgeSet) : ∃ e : E, G.ends e = p.1 := by
  induction h : p.1 using Sym2.inductionOn with
  | _ u v =>
      have huv : T.Adj u v := by
        rw [← SimpleGraph.mem_edgeSet, ← h]
        exact p.2
      exact (hTG huv).2

private noncomputable def labelAbove
    (T : SimpleGraph V) (hTG : T ≤ G.toSimpleGraph)
    (p : T.edgeSet) : E :=
  Classical.choose (G.exists_labelAbove T hTG p)

omit [Fintype V] [Fintype E] in
private theorem labelAbove_ends
    (T : SimpleGraph V) (hTG : T ≤ G.toSimpleGraph)
    (p : T.edgeSet) : G.ends (G.labelAbove T hTG p) = p.1 := by
  exact Classical.choose_spec (G.exists_labelAbove T hTG p)

omit [Fintype V] [Fintype E] in
private theorem labelAbove_injective
    (T : SimpleGraph V) (hTG : T ≤ G.toSimpleGraph) :
    Function.Injective (G.labelAbove T hTG) := by
  intro p q hpq
  apply Subtype.ext
  rw [← G.labelAbove_ends T hTG p, ← G.labelAbove_ends T hTG q, hpq]

private noncomputable def labelsOfSimpleTree
    (T : SimpleGraph V) (hTG : T ≤ G.toSimpleGraph) : Finset E := by
  classical
  letI := Fintype.ofFinite T.edgeSet
  exact Finset.univ.image (G.labelAbove T hTG)

omit [Fintype E] in
private theorem mem_labelsOfSimpleTree_iff
    (T : SimpleGraph V) (hTG : T ≤ G.toSimpleGraph) (e : E) :
    e ∈ G.labelsOfSimpleTree T hTG ↔
      ∃ p : T.edgeSet, G.labelAbove T hTG p = e := by
  classical
  simp [labelsOfSimpleTree]

omit [Fintype E] in
private theorem simpleGraphOn_labelsOfSimpleTree
    (T : SimpleGraph V) (hTG : T ≤ G.toSimpleGraph) :
    G.simpleGraphOn (G.labelsOfSimpleTree T hTG : Set E) = T := by
  classical
  ext u v
  constructor
  · rintro ⟨huv, e, he, hlink⟩
    change e ∈ G.labelsOfSimpleTree T hTG at he
    rw [mem_labelsOfSimpleTree_iff (G := G) T hTG] at he
    obtain ⟨p, rfl⟩ := he
    have hends := G.labelAbove_ends T hTG p
    have hp : p.1 = s(u, v) := hends.symm.trans hlink
    have hpAdj : p.1 ∈ T.edgeSet := p.2
    rwa [hp] at hpAdj
  · intro huv
    let p : T.edgeSet := ⟨s(u, v), huv⟩
    refine ⟨huv.ne, G.labelAbove T hTG p, ?_, ?_⟩
    · exact mem_labelsOfSimpleTree_iff (G := G) T hTG _ |>.mpr ⟨p, rfl⟩
    · exact G.labelAbove_ends T hTG p

omit [Fintype E] in
private theorem card_labelsOfSimpleTree
    (T : SimpleGraph V) (hTG : T ≤ G.toSimpleGraph) :
    (G.labelsOfSimpleTree T hTG).card = Nat.card T.edgeSet := by
  classical
  letI := Fintype.ofFinite T.edgeSet
  rw [labelsOfSimpleTree, Finset.card_image_of_injective]
  · simp
  · exact G.labelAbove_injective T hTG

omit [Fintype E] in
/-- Connectivity of a finite edge-labelled multigraph supplies an actual
labelled spanning tree.  Parallel labels cause no ambiguity: one label is
chosen over each edge of a simple spanning tree. -/
theorem exists_isSpanningTree (hG : G.Connected) :
    ∃ tree : Finset E, G.IsSpanningTree tree := by
  classical
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  refine ⟨G.labelsOfSimpleTree T hTG, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro e he hloop
    rw [mem_labelsOfSimpleTree_iff (G := G) T hTG] at he
    obtain ⟨p, rfl⟩ := he
    have hpdiag : p.1.IsDiag := by
      rw [← G.labelAbove_ends T hTG p]
      exact hloop
    exact (T.not_isDiag_of_mem_edgeSet p.2) hpdiag
  · rw [G.simpleGraphOn_labelsOfSimpleTree T hTG]
    exact hT.connected
  · rw [G.card_labelsOfSimpleTree T hTG]
    letI := Fintype.ofFinite T.edgeSet
    have hedge : Nat.card T.edgeSet + 1 = Fintype.card V := by
      rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
      exact hT.card_edgeFinset
    exact hedge

end SpanningTreeExistence

end LabeledMultigraph

end Multigraph

namespace Boundary

open Multigraph

/-! ## The underlying occupied simple grid -/

/-- Every labelled occupied-grid edge is a unit Manhattan edge.  This is the
easy half of identifying `occupiedGridMultigraph` with the square grid induced
on its occupied vertices. -/
theorem occupiedGrid_toSimpleGraph_le_faceLattice
    (R S : ℕ) (V : Finset LatticePoint) :
    (occupiedGridMultigraph R S V).toSimpleGraph ≤
      faceLattice.comap (fun p : OccupiedVertex R S V => p.1) := by
  intro p q hpq
  rcases hpq with ⟨_, e, hlink⟩
  cases e with
  | inl e =>
      have hval := congrArg (Sym2.map (fun z : OccupiedVertex R S V => z.1)) hlink
      change s((e.1.2, e.1.1), (e.1.2 + 1, e.1.1)) = s(p.1, q.1) at hval
      rcases Sym2.eq_iff.mp hval with h | h
      · change natManhattanDist p.1 q.1 = 1
        rw [← h.1, ← h.2]
        simp [natManhattanDist, Nat.dist]
      · change natManhattanDist p.1 q.1 = 1
        rw [← h.1, ← h.2]
        simp [natManhattanDist, Nat.dist]
  | inr e =>
      have hval := congrArg (Sym2.map (fun z : OccupiedVertex R S V => z.1)) hlink
      change s((e.1.1, e.1.2), (e.1.1, e.1.2 + 1)) = s(p.1, q.1) at hval
      rcases Sym2.eq_iff.mp hval with h | h
      · change natManhattanDist p.1 q.1 = 1
        rw [← h.1, ← h.2]
        simp [natManhattanDist, Nat.dist]
      · change natManhattanDist p.1 q.1 = 1
        rw [← h.1, ← h.2]
        simp [natManhattanDist, Nat.dist]

private theorem natManhattanDist_eq_one_cases {p q : LatticePoint}
    (h : natManhattanDist p q = 1) :
    (q.1 = p.1 + 1 ∧ q.2 = p.2) ∨
    (p.1 = q.1 + 1 ∧ p.2 = q.2) ∨
    (q.2 = p.2 + 1 ∧ q.1 = p.1) ∨
    (p.2 = q.2 + 1 ∧ p.1 = q.1) := by
  have hsplit :
      (Nat.dist p.1 q.1 = 1 ∧ Nat.dist p.2 q.2 = 0) ∨
      (Nat.dist p.1 q.1 = 0 ∧ Nat.dist p.2 q.2 = 1) := by
    simp only [natManhattanDist] at h
    omega
  rcases hsplit with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hyeq : p.2 = q.2 := Nat.eq_of_dist_eq_zero hy
    rcases le_total p.1 q.1 with hpq | hqp
    · left
      rw [Nat.dist_eq_sub_of_le hpq] at hx
      exact ⟨by omega, hyeq.symm⟩
    · right; left
      rw [Nat.dist_eq_sub_of_le_right hqp] at hx
      exact ⟨by omega, hyeq⟩
  · have hxeq : p.1 = q.1 := Nat.eq_of_dist_eq_zero hx
    rcases le_total p.2 q.2 with hpq | hqp
    · right; right; left
      rw [Nat.dist_eq_sub_of_le hpq] at hy
      exact ⟨by omega, hxeq.symm⟩
    · right; right; right
      rw [Nat.dist_eq_sub_of_le_right hqp] at hy
      exact ⟨by omega, hxeq⟩

private theorem occupiedGrid_adj_of_right
    {R S : ℕ} {V : Finset LatticePoint}
    {p q : OccupiedVertex R S V}
    (hx : q.1.1 = p.1.1 + 1) (hy : q.1.2 = p.1.2) :
    (occupiedGridMultigraph R S V).toSimpleGraph.Adj p q := by
  have hpOcc := Finset.mem_sdiff.mp p.2
  have hqOcc := Finset.mem_sdiff.mp q.2
  let a : Σ _y : ℕ, ℕ := ⟨p.1.2, p.1.1⟩
  have ha : a ∈ horizontalOccupiedEdges R S V := by
    simp only [horizontalOccupiedEdges, Finset.mem_sigma]
    refine ⟨Windows.mem_line.mpr (mem_grid.mp hpOcc.1).2, ?_⟩
    simp only [occupiedLineEdgeStarts, Finset.mem_filter, Finset.mem_range]
    dsimp [a]
    refine ⟨by have := (mem_grid.mp hqOcc.1).1; omega, ?_, ?_⟩
    · intro hpRow
      exact hpOcc.2 (mem_row.mp hpRow).2
    · intro hqRow
      apply hqOcc.2
      have := (mem_row.mp hqRow).2
      change (q.1.1, q.1.2) ∈ V
      simpa [hx, hy] using this
  let e : ↑(horizontalOccupiedEdges R S V) := ⟨a, ha⟩
  refine ⟨?_, Sum.inl e, ?_⟩
  · intro hpq
    have := congrArg (fun z : OccupiedVertex R S V => z.1.1) hpq
    omega
  · change (occupiedGridMultigraph R S V).ends (Sum.inl e) = s(p, q)
    apply Sym2.eq_iff.mpr
    left
    constructor
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      exact Prod.ext hx.symm hy.symm

private theorem occupiedGrid_adj_of_up
    {R S : ℕ} {V : Finset LatticePoint}
    {p q : OccupiedVertex R S V}
    (hy : q.1.2 = p.1.2 + 1) (hx : q.1.1 = p.1.1) :
    (occupiedGridMultigraph R S V).toSimpleGraph.Adj p q := by
  have hpOcc := Finset.mem_sdiff.mp p.2
  have hqOcc := Finset.mem_sdiff.mp q.2
  let a : Σ _x : ℕ, ℕ := ⟨p.1.1, p.1.2⟩
  have ha : a ∈ verticalOccupiedEdges R S V := by
    simp only [verticalOccupiedEdges, Finset.mem_sigma]
    refine ⟨Windows.mem_line.mpr (mem_grid.mp hpOcc.1).1, ?_⟩
    simp only [occupiedLineEdgeStarts, Finset.mem_filter, Finset.mem_range]
    dsimp [a]
    refine ⟨by have := (mem_grid.mp hqOcc.1).2; omega, ?_, ?_⟩
    · intro hpCol
      exact hpOcc.2 (mem_column.mp hpCol).2
    · intro hqCol
      apply hqOcc.2
      have := (mem_column.mp hqCol).2
      change (q.1.1, q.1.2) ∈ V
      simpa [hx, hy] using this
  let e : ↑(verticalOccupiedEdges R S V) := ⟨a, ha⟩
  refine ⟨?_, Sum.inr e, ?_⟩
  · intro hpq
    have := congrArg (fun z : OccupiedVertex R S V => z.1.2) hpq
    omega
  · change (occupiedGridMultigraph R S V).ends (Sum.inr e) = s(p, q)
    apply Sym2.eq_iff.mpr
    left
    constructor
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      exact Prod.ext hx.symm hy.symm

/-- Forgetting occupied-grid labels gives exactly the square lattice induced
on the occupied natural-coordinate vertices. -/
theorem occupiedGrid_toSimpleGraph_eq_faceLattice
    (R S : ℕ) (V : Finset LatticePoint) :
    (occupiedGridMultigraph R S V).toSimpleGraph =
      faceLattice.comap (fun p : OccupiedVertex R S V => p.1) := by
  apply le_antisymm (occupiedGrid_toSimpleGraph_le_faceLattice R S V)
  intro p q hpq
  change natManhattanDist p.1 q.1 = 1 at hpq
  rcases natManhattanDist_eq_one_cases hpq with h | h | h | h
  · exact occupiedGrid_adj_of_right h.1 h.2
  · exact (occupiedGrid_adj_of_right h.1 h.2).symm
  · exact occupiedGrid_adj_of_up h.1 h.2
  · exact (occupiedGrid_adj_of_up h.1 h.2).symm

/-! ## The connected occupied core -/

/-- Natural-coordinate vertices which are genuinely in `A` (as opposed to
interior vacancies retained after deleting only boundary vacancies). -/
def encodedOccupiedCore (R S : ℕ) (A : Finset Point) : Finset LatticePoint :=
  grid R S \ encodedVacancies R S A

@[simp] theorem mem_encodedOccupiedCore
    {R S : ℕ} {A : Finset Point} {z : LatticePoint} :
    z ∈ encodedOccupiedCore R S A ↔
      z.1 ≤ R ∧ z.2 ≤ S ∧ ofNatPoint z ∈ A := by
  classical
  simp only [encodedOccupiedCore, Finset.mem_sdiff, mem_grid,
    mem_encodedVacancies]
  tauto

private theorem natAbs_natCast_sub_eq_dist (a b : ℕ) :
    ((a : ℤ) - (b : ℤ)).natAbs = Nat.dist a b := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    exact Int.natAbs_natCast_sub_natCast_of_le hab
  · rw [Nat.dist_eq_sub_of_le_right hba]
    exact Int.natAbs_natCast_sub_natCast_of_ge hba

theorem manhattanDist_ofNatPoint (z w : LatticePoint) :
    manhattanDist (ofNatPoint z) (ofNatPoint w) = natManhattanDist z w := by
  simp only [manhattanDist, ofNatPoint, natManhattanDist]
  rw [natAbs_natCast_sub_eq_dist, natAbs_natCast_sub_eq_dist]

/-- In a normalized rectangular hull, the natural occupied core and `A` are
the same finite vertex type. -/
noncomputable def encodedOccupiedCoreEquiv
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1)) :
    {z // z ∈ encodedOccupiedCore R S A} ≃ {p // p ∈ A} where
  toFun z := ⟨ofNatPoint z.1, (mem_encodedOccupiedCore.mp z.2).2.2⟩
  invFun p := by
    have hpRect := hHull.2.2.1 p.2
    have hpBounds :
        ((0 : ℤ) ≤ p.1.1 ∧ p.1.1 < (R + 1 : ℕ)) ∧
        ((0 : ℤ) ≤ p.1.2 ∧ p.1.2 < (S + 1 : ℕ)) := by
      simpa [rectangle] using hpRect
    let z : LatticePoint := (p.1.1.toNat, p.1.2.toNat)
    have hz : ofNatPoint z = p.1 := by
      apply Prod.ext <;> simp [z, ofNatPoint, hpBounds.1.1, hpBounds.2.1]
    refine ⟨z, mem_encodedOccupiedCore.mpr ⟨?_, ?_, ?_⟩⟩
    · apply Int.toNat_le.mpr
      omega
    · apply Int.toNat_le.mpr
      omega
    · rw [hz]
      exact p.2
  left_inv z := by
    apply Subtype.ext
    exact ofNatPoint_injective (by
      simp only [ofNatPoint]
      apply Prod.ext <;> simp)
  right_inv p := by
    apply Subtype.ext
    have hpRect := hHull.2.2.1 p.2
    have hpBounds :
        ((0 : ℤ) ≤ p.1.1 ∧ p.1.1 < (R + 1 : ℕ)) ∧
        ((0 : ℤ) ≤ p.1.2 ∧ p.1.2 < (S + 1 : ℕ)) := by
      simpa [rectangle] using hpRect
    apply Prod.ext <;> simp [ofNatPoint, hpBounds.1.1, hpBounds.2.1]

/-- The coordinate equivalence is a graph isomorphism between the square
lattice on the natural occupied core and the manuscript's induced grid on
`A`. -/
noncomputable def encodedOccupiedCoreGraphIso
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1)) :
    faceLattice.comap
        (fun z : {z // z ∈ encodedOccupiedCore R S A} => z.1) ≃g
      inducedGrid A where
  toEquiv := encodedOccupiedCoreEquiv hHull
  map_rel_iff' := by
    intro z w
    change manhattanDist (ofNatPoint z.1) (ofNatPoint w.1) = 1 ↔
      natManhattanDist z.1 w.1 = 1
    rw [manhattanDist_ofNatPoint]

/-- Connectedness of `A` therefore gives connectedness of the natural
occupied core. -/
theorem encodedOccupiedCore_connected
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    (faceLattice.comap
      (fun z : {z // z ∈ encodedOccupiedCore R S A} => z.1)).Connected := by
  exact (encodedOccupiedCoreGraphIso hHull).connected_iff.mpr hconn

/-- Every core point remains occupied after only boundary-attached vacancies
are removed. -/
theorem encodedOccupiedCore_subset_boundaryOccupied
    (R S : ℕ) (A : Finset Point) :
    encodedOccupiedCore R S A ⊆
      occupiedVertices R S
        (boundaryVacancies R S (encodedVacancies R S A)) := by
  intro z hz
  have hzCore := mem_encodedOccupiedCore.mp hz
  apply Finset.mem_sdiff.mpr
  refine ⟨mem_grid.mpr ⟨hzCore.1, hzCore.2.1⟩, ?_⟩
  intro hzB
  have hzW := boundaryVacancies_subset R S (encodedVacancies R S A) hzB
  exact (mem_encodedVacancies.mp hzW).2.2 hzCore.2.2

noncomputable section

abbrev BoundaryOccupiedVertex (R S : ℕ) (A : Finset Point) :=
  ↑(occupiedVertices R S
    (boundaryVacancies R S (encodedVacancies R S A)))

abbrev EncodedCoreVertex (R S : ℕ) (A : Finset Point) :=
  ↑(encodedOccupiedCore R S A)

/-- Inclusion of the genuinely occupied core into the grid obtained by filling
all interior vacancy components. -/
def coreToBoundaryOccupied (R S : ℕ) (A : Finset Point) :
    EncodedCoreVertex R S A → BoundaryOccupiedVertex R S A :=
  fun z => ⟨z.1, encodedOccupiedCore_subset_boundaryOccupied R S A z.2⟩

private theorem neighbor_mem_boundaryOccupied
    {R S : ℕ} {A : Finset Point}
    (p : BoundaryOccupiedVertex R S A)
    (hpCore : p.1 ∉ encodedOccupiedCore R S A)
    {u : LatticePoint} (huGrid : u ∈ grid R S)
    (hpu : KingAdjacent p.1 u) :
    u ∈ occupiedVertices R S
      (boundaryVacancies R S (encodedVacancies R S A)) := by
  classical
  have hpOcc := Finset.mem_sdiff.mp p.2
  have hpBounds := mem_grid.mp hpOcc.1
  have hpNotA : ofNatPoint p.1 ∉ A := by
    intro hpA
    exact hpCore (mem_encodedOccupiedCore.mpr
      ⟨hpBounds.1, hpBounds.2, hpA⟩)
  have hpW : p.1 ∈ encodedVacancies R S A :=
    mem_encodedVacancies.mpr ⟨hpBounds.1, hpBounds.2, hpNotA⟩
  apply Finset.mem_sdiff.mpr
  refine ⟨huGrid, ?_⟩
  by_cases huW : u ∈ encodedVacancies R S A
  · intro huB
    let pp : {z // z ∈ encodedVacancies R S A} := ⟨p.1, hpW⟩
    let uu : {z // z ∈ encodedVacancies R S A} := ⟨u, huW⟩
    have hadj : (kingGraph (encodedVacancies R S A)).Adj pp uu := by
      rw [kingGraph_adj_iff]
      exact hpu
    have huAttach : IsBoundaryAttached R S (encodedVacancies R S A) u :=
      mem_boundaryVacancies.mp huB
    have hpAttach : IsBoundaryAttached R S (encodedVacancies R S A) p.1 :=
      isBoundaryAttached_of_reachable huAttach hadj.reachable.symm
    exact hpOcc.2 (mem_boundaryVacancies.mpr hpAttach)
  · intro huB
    exact huW (boundaryVacancies_subset R S (encodedVacancies R S A) huB)

noncomputable def boundaryOccupiedFaceGraph (R S : ℕ) (A : Finset Point) :
    SimpleGraph (BoundaryOccupiedVertex R S A) :=
  faceLattice.comap fun z => z.1

private theorem boundaryOccupied_reaches_core_target
    {R S : ℕ} {A : Finset Point}
    (p : BoundaryOccupiedVertex R S A)
    (q : EncodedCoreVertex R S A)
    (hy : p.1.2 = q.1.2)
    (hpCore : p.1 ∉ encodedOccupiedCore R S A) :
    ∃ c : EncodedCoreVertex R S A,
      (boundaryOccupiedFaceGraph R S A).Reachable p
        (coreToBoundaryOccupied R S A c) := by
  induction hd : Nat.dist p.1.1 q.1.1 using Nat.strong_induction_on generalizing p with
  | h d ih =>
      have hpqX : p.1.1 ≠ q.1.1 := by
        intro heq
        apply hpCore
        have hpq : p.1 = q.1 := Prod.ext heq hy
        exact hpq.symm ▸ q.2
      rcases lt_or_gt_of_ne hpqX with hright | hleft
      · let uv : LatticePoint := (p.1.1 + 1, p.1.2)
        have hpGrid := mem_grid.mp (Finset.mem_sdiff.mp p.2).1
        have hqGrid := mem_grid.mp
          (encodedOccupiedCore_subset_boundaryOccupied R S A q.2 |>
            Finset.mem_sdiff.mp |>.1)
        have huGrid : uv ∈ grid R S := by
          apply mem_grid.mpr
          exact ⟨by dsimp [uv]; omega, by simpa [uv] using hpGrid.2⟩
        have hking : KingAdjacent p.1 uv := by
          refine ⟨?_, ?_, ?_⟩
          · intro heq
            have := congrArg Prod.fst heq
            simp [uv] at this
          · simp [uv, Nat.dist]
          · simp [uv, Nat.dist]
        have huOcc := neighbor_mem_boundaryOccupied p hpCore huGrid hking
        let u : BoundaryOccupiedVertex R S A := ⟨uv, huOcc⟩
        have hpu : (boundaryOccupiedFaceGraph R S A).Adj p u := by
          change natManhattanDist p.1 u.1 = 1
          simp [u, uv, natManhattanDist, Nat.dist]
        by_cases huCore : uv ∈ encodedOccupiedCore R S A
        · let c : EncodedCoreVertex R S A := ⟨uv, huCore⟩
          refine ⟨c, hpu.reachable.trans ?_⟩
          have huc : u = coreToBoundaryOccupied R S A c := by
            apply Subtype.ext
            rfl
          rw [huc]
        · have hdistlt : Nat.dist u.1.1 q.1.1 < d := by
            have hle : u.1.1 ≤ q.1.1 := by simp [u, uv]; omega
            rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt hright)] at hd
            rw [Nat.dist_eq_sub_of_le hle]
            simp [u, uv] at hle ⊢
            omega
          have huy : u.1.2 = q.1.2 := by simpa [u, uv] using hy
          rcases ih _ hdistlt u huy huCore rfl with ⟨c, huc⟩
          exact ⟨c, hpu.reachable.trans huc⟩

      · let uv : LatticePoint := (p.1.1 - 1, p.1.2)
        have hpGrid := mem_grid.mp (Finset.mem_sdiff.mp p.2).1
        have huGrid : uv ∈ grid R S := by
          apply mem_grid.mpr
          exact ⟨by dsimp [uv]; omega, by simpa [uv] using hpGrid.2⟩
        have hking : KingAdjacent p.1 uv := by
          have hpPos : 0 < p.1.1 := by omega
          refine ⟨?_, ?_, ?_⟩
          · intro heq
            have := congrArg Prod.fst heq
            simp [uv] at this
            omega
          · simp [uv, Nat.dist]
            omega
          · simp [uv, Nat.dist]
        have huOcc := neighbor_mem_boundaryOccupied p hpCore huGrid hking
        let u : BoundaryOccupiedVertex R S A := ⟨uv, huOcc⟩
        have hpu : (boundaryOccupiedFaceGraph R S A).Adj p u := by
          change natManhattanDist p.1 u.1 = 1
          simp [u, uv, natManhattanDist, Nat.dist]
          omega
        by_cases huCore : uv ∈ encodedOccupiedCore R S A
        · let c : EncodedCoreVertex R S A := ⟨uv, huCore⟩
          refine ⟨c, hpu.reachable.trans ?_⟩
          have huc : u = coreToBoundaryOccupied R S A c := by
            apply Subtype.ext
            rfl
          rw [huc]
        · have hdistlt : Nat.dist u.1.1 q.1.1 < d := by
            have hle : q.1.1 ≤ u.1.1 := by simp [u, uv]; omega
            rw [Nat.dist_eq_sub_of_le_right (Nat.le_of_lt hleft)] at hd
            rw [Nat.dist_eq_sub_of_le_right hle]
            simp [u, uv] at hle ⊢
            omega
          have huy : u.1.2 = q.1.2 := by simpa [u, uv] using hy
          rcases ih _ hdistlt u huy huCore rfl with ⟨c, huc⟩
          exact ⟨c, hpu.reachable.trans huc⟩

/-- Every vertex left after deleting boundary-attached vacancies can reach a
genuinely occupied vertex of `A`.  Interior vacancy components are filled in,
and a horizontal step toward an occupied point in the same row cannot enter a
boundary-attached component. -/
theorem boundaryOccupied_reaches_core
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (p : BoundaryOccupiedVertex R S A) :
    ∃ c : EncodedCoreVertex R S A,
      (boundaryOccupiedFaceGraph R S A).Reachable p
        (coreToBoundaryOccupied R S A c) := by
  classical
  by_cases hpCore : p.1 ∈ encodedOccupiedCore R S A
  · let c : EncodedCoreVertex R S A := ⟨p.1, hpCore⟩
    refine ⟨c, ?_⟩
    have hpc : p = coreToBoundaryOccupied R S A c := by
      apply Subtype.ext
      rfl
    rw [hpc]
  · have hpGrid := mem_grid.mp (Finset.mem_sdiff.mp p.2).1
    rcases exists_occupied_in_row hHull hconn hpGrid.2 with ⟨x, hxR, hxA⟩
    have hqCore : (x, p.1.2) ∈ encodedOccupiedCore R S A :=
      mem_encodedOccupiedCore.mpr ⟨hxR, hpGrid.2, hxA⟩
    let q : EncodedCoreVertex R S A := ⟨(x, p.1.2), hqCore⟩
    exact boundaryOccupied_reaches_core_target p q rfl hpCore

/-- The occupied core includes into the filled boundary-occupied grid as a
graph homomorphism. -/
def coreToBoundaryOccupiedHom (R S : ℕ) (A : Finset Point) :
    (faceLattice.comap
      (fun z : EncodedCoreVertex R S A => z.1)) →g
      boundaryOccupiedFaceGraph R S A where
  toFun := coreToBoundaryOccupied R S A
  map_rel' := by
    intro p q hpq
    exact hpq

/-- The grid remaining after deletion of boundary-attached encoded vacancies
is connected.  This discharges the non-planar half of the cellulation
certificate directly from connectedness of `A`. -/
theorem boundaryOccupiedFaceGraph_connected
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    (boundaryOccupiedFaceGraph R S A).Connected := by
  have hcore := encodedOccupiedCore_connected hHull hconn
  letI : Nonempty (BoundaryOccupiedVertex R S A) :=
    hcore.nonempty.map (coreToBoundaryOccupied R S A)
  refine { preconnected := ?_ }
  intro p q
  rcases boundaryOccupied_reaches_core hHull hconn p with ⟨cp, hp⟩
  rcases boundaryOccupied_reaches_core hHull hconn q with ⟨cq, hq⟩
  have hmiddle : (boundaryOccupiedFaceGraph R S A).Reachable
      (coreToBoundaryOccupied R S A cp)
      (coreToBoundaryOccupied R S A cq) :=
    (hcore cp cq).map (coreToBoundaryOccupiedHom R S A)
  exact hp.trans (hmiddle.trans hq.symm)

theorem occupiedGrid_encodedBoundaryVacancies_connected
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    (occupiedGridMultigraph R S
      (boundaryVacancies R S (encodedVacancies R S A))).Connected := by
  rw [Multigraph.LabeledMultigraph.Connected,
    occupiedGrid_toSimpleGraph_eq_faceLattice]
  exact boundaryOccupiedFaceGraph_connected hHull hconn

/-- A connected occupied grid satisfying the finite Euler cardinality identity
has a concrete `GridCellulationCertificate`.  Thus neither the spanning tree
nor the cotree bijection needs to be postulated separately. -/
noncomputable def gridCellulationCertificateOfConnectedEuler
    {R S : ℕ} {V : Finset LatticePoint}
    (hconn : (occupiedGridMultigraph R S V).Connected)
    (heuler :
      (occupiedVertices R S V).card + (unmarkedFaces R S V).card =
        (horizontalOccupiedEdges R S V).card +
          (verticalOccupiedEdges R S V).card + 1) :
    GridCellulationCertificate R S V := by
  classical
  let tree := Classical.choose
    (Multigraph.LabeledMultigraph.exists_isSpanningTree
      (occupiedGridMultigraph R S V) hconn)
  have htree := Classical.choose_spec
    (Multigraph.LabeledMultigraph.exists_isSpanningTree
      (occupiedGridMultigraph R S V) hconn)
  refine ⟨tree, htree, ?_⟩
  apply Fintype.equivOfCardEq
  have htreeCard : tree.card + 1 = (occupiedVertices R S V).card := by
    simpa [OccupiedVertex] using htree.card_edges_add_one
  have hedgeCard : Fintype.card (OccupiedEdge R S V) =
      (horizontalOccupiedEdges R S V).card +
        (verticalOccupiedEdges R S V).card := by
    simp [OccupiedEdge]
  have hcompl : Fintype.card {e : OccupiedEdge R S V // e ∉ tree} =
      Fintype.card (OccupiedEdge R S V) - tree.card := by
    have h := Fintype.card_subtype_compl
      (fun e : OccupiedEdge R S V => e ∈ tree)
    convert h using 1
    exact congrArg (fun n => Fintype.card (OccupiedEdge R S V) - n)
      (Fintype.card_coe tree).symm
  rw [hcompl, hedgeCard, Fintype.card_coe]
  omega

/-- Proposition-valued form of
`gridCellulationCertificateOfConnectedEuler`. -/
theorem gridCellulationCertificate_exists_of_connected_euler
    {R S : ℕ} {V : Finset LatticePoint}
    (hconn : (occupiedGridMultigraph R S V).Connected)
    (heuler :
      (occupiedVertices R S V).card + (unmarkedFaces R S V).card =
        (horizontalOccupiedEdges R S V).card +
          (verticalOccupiedEdges R S V).card + 1) :
    Nonempty (GridCellulationCertificate R S V) :=
  ⟨gridCellulationCertificateOfConnectedEuler hconn heuler⟩

/-- The sole remaining planar statement for the normalized boundary-vacancy
set, expressed as a scalar finite Euler equality. -/
def EncodedBoundaryEulerIdentity (R S : ℕ) (A : Finset Point) : Prop :=
  let B := boundaryVacancies R S (encodedVacancies R S A)
  (occupiedVertices R S B).card + (unmarkedFaces R S B).card =
    (horizontalOccupiedEdges R S B).card +
      (verticalOccupiedEdges R S B).card + 1

/-- Once the scalar Euler identity is known, all data in the manuscript's
cellulation certificate are constructed: connectedness, the labelled spanning
tree, and the cotree-face equivalence. -/
noncomputable def gridCellulationCertificate_encodedBoundaryVacancies_of_euler
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (heuler : EncodedBoundaryEulerIdentity R S A) :
    GridCellulationCertificate R S
      (boundaryVacancies R S (encodedVacancies R S A)) :=
  gridCellulationCertificateOfConnectedEuler
    (occupiedGrid_encodedBoundaryVacancies_connected hHull hconn) heuler

/-- The marked-face identity now depends only on the scalar planar Euler
equality; the formerly bundled spanning-tree/cotree certificate has been
eliminated. -/
theorem card_markedFaces_encodedBoundaryVacancies_of_euler
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (heuler : EncodedBoundaryEulerIdentity R S A) :
    (markedFaces R S
      (boundaryVacancies R S (encodedVacancies R S A))).card =
      (boundaryVacancies R S (encodedVacancies R S A)).card +
        horizontalInternalRunCount R S
          (boundaryVacancies R S (encodedVacancies R S A)) +
        verticalInternalRunCount R S
          (boundaryVacancies R S (encodedVacancies R S A)) :=
  card_markedFaces_encodedBoundaryVacancies_of_cellulation hHull hconn
    (gridCellulationCertificate_encodedBoundaryVacancies_of_euler
      hHull hconn heuler)

end

end Boundary

end SquareMaximality
