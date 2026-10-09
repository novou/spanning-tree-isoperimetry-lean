import SquareMaximality.Dual.InteriorFactor
import SquareMaximality.Dual.Components
import SquareMaximality.Multigraph.ContractionTrees
import SquareMaximality.Boundary.Cellulation

/-!
# Interior face stars and the Tapp reduction

This module refines the interior-component certificate used in
`Dual.InteriorFactor`.  It constructs the bounded dual face-star graph and
the finite family of its spanning trees.  The only external enumerative input
is a graph-level form of Tapp's lower bound; planar deletion/duality is kept
in a separate interface.

The face-star construction corresponds to `general.tex`, equations
`forest-event` and `interior-factor` and the paragraph immediately preceding
them.  The manuscript is used only as mathematical provenance, not as Lean
instructions.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Dual

open Multigraph

/-! ## The bounded face-star graph -/

/-- The part of the dual edge graph whose vertices are bounded faces. -/
def boundedDualGraph {r s : ℕ} (X : Finset (Fin r × Fin s)) :
    SimpleGraph (BoundedFace r s) :=
  (dualEdgeGraph X).comap some

/-- The bounded dual graph with isolated faces suppressed.  For an interior
vacancy component this is exactly the manuscript's graph `H_J`. -/
def boundedDualCore {r s : ℕ} (X : Finset (Fin r × Fin s)) :
    SimpleGraph {f // f ∈ (boundedDualGraph X).support} :=
  (boundedDualGraph X).induce (boundedDualGraph X).support

noncomputable instance boundedDualCoreVertexFintype
    {r s : ℕ} (X : Finset (Fin r × Fin s)) :
    Fintype {f // f ∈ (boundedDualGraph X).support} :=
  Fintype.ofFinite _

/-- The explicit face-star graph of one canonical interior component. -/
noncomputable def interiorFaceStarGraph
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    SimpleGraph {f // f ∈
      (boundedDualGraph (canonicalInteriorPrimal R S A i)).support} :=
  boundedDualCore (canonicalInteriorPrimal R S A i)

/-- Natural coordinates of a bounded dual face. -/
def boundedFaceCoord {r s : ℕ} (f : BoundedFace r s) :
    Boundary.LatticePoint := (f.1.1, f.2.1)

theorem boundedFaceCoord_injective {r s : ℕ} :
    Function.Injective (boundedFaceCoord (r := r) (s := s)) := by
  intro f g h
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- Coordinate embedding of the vertices of a bounded face-star core. -/
def boundedDualCoreCoord {r s : ℕ} (X : Finset (Fin r × Fin s)) :
    {f // f ∈ (boundedDualGraph X).support} ↪ Boundary.LatticePoint where
  toFun f := boundedFaceCoord f.1
  inj' := boundedFaceCoord_injective.comp Subtype.val_injective

/-- Coordinate membership in the four corners of a natural-coordinate unit
square. -/
def UnitSquareCorner (z w : Boundary.LatticePoint) : Prop :=
  z.1 ≤ w.1 ∧ w.1 ≤ z.1 + 1 ∧ z.2 ≤ w.2 ∧ w.2 ≤ z.2 + 1

/-- The southwest face coordinate of the dual unit square surrounding an
interior primal vertex. -/
def faceSquareStart {R S : ℕ} (p : Fin (R + 1) × Fin (S + 1)) :
    Boundary.LatticePoint := (p.1.1 - 1, p.2.1 - 1)

/-- Bounded dual adjacency is ordinary nearest-neighbour square-lattice
adjacency in face coordinates. -/
theorem boundedDualGraph_le_faceLattice
    {r s : ℕ} (X : Finset (Fin r × Fin s)) :
    boundedDualGraph X ≤ Boundary.faceLattice.comap boundedFaceCoord := by
  intro f g hfg
  rcases hfg.2 with ⟨e, _heX, hlink⟩
  cases e with
  | horizontal e =>
      change s(horizontalBelow e, horizontalAbove e) = s(some f, some g) at hlink
      by_cases hy0 : e.y.1 = 0
      · rw [horizontalBelow, dif_pos hy0] at hlink
        rcases Sym2.eq_iff.mp hlink with h | h <;> cases h.1
      · by_cases hytop : e.y.1 + 1 < s
        · rw [horizontalBelow, dif_neg hy0,
              horizontalAbove, dif_pos hytop] at hlink
          rcases Sym2.eq_iff.mp hlink with h | h
          · have hf := Option.some.inj h.1
            have hg := Option.some.inj h.2
            change Boundary.natManhattanDist (boundedFaceCoord f)
                (boundedFaceCoord g) = 1
            rw [← hf, ← hg]
            simp [Boundary.natManhattanDist, boundedFaceCoord, Nat.dist]
            omega
          · have hf := Option.some.inj h.2
            have hg := Option.some.inj h.1
            change Boundary.natManhattanDist (boundedFaceCoord f)
                (boundedFaceCoord g) = 1
            rw [← hf, ← hg]
            simp [Boundary.natManhattanDist, boundedFaceCoord, Nat.dist]
            omega
        · rw [horizontalAbove, dif_neg hytop] at hlink
          rcases Sym2.eq_iff.mp hlink with h | h <;> cases h.2
  | vertical e =>
      change s(verticalLeft e, verticalRight e) = s(some f, some g) at hlink
      by_cases hx0 : e.x.1 = 0
      · rw [verticalLeft, dif_pos hx0] at hlink
        rcases Sym2.eq_iff.mp hlink with h | h <;> cases h.1
      · by_cases hxright : e.x.1 + 1 < r
        · rw [verticalLeft, dif_neg hx0,
              verticalRight, dif_pos hxright] at hlink
          rcases Sym2.eq_iff.mp hlink with h | h
          · have hf := Option.some.inj h.1
            have hg := Option.some.inj h.2
            change Boundary.natManhattanDist (boundedFaceCoord f)
                (boundedFaceCoord g) = 1
            rw [← hf, ← hg]
            simp [Boundary.natManhattanDist, boundedFaceCoord, Nat.dist]
            omega
          · have hf := Option.some.inj h.2
            have hg := Option.some.inj h.1
            change Boundary.natManhattanDist (boundedFaceCoord f)
                (boundedFaceCoord g) = 1
            rw [← hf, ← hg]
            simp [Boundary.natManhattanDist, boundedFaceCoord, Nat.dist]
            omega
        · rw [verticalRight, dif_neg hxright] at hlink
          rcases Sym2.eq_iff.mp hlink with h | h <;> cases h.2

/-- The isolated-vertex-suppressed bounded dual core is explicitly embedded
as a finite square-lattice graph. -/
theorem boundedDualCore_le_faceLattice
    {r s : ℕ} (X : Finset (Fin r × Fin s)) :
    boundedDualCore X ≤
      Boundary.faceLattice.comap (boundedDualCoreCoord X) := by
  intro f g hfg
  exact boundedDualGraph_le_faceLattice X hfg

/-- Every bounded face touched by the selected dual edges is a corner of the
unit square contributed by some selected interior primal vertex. -/
theorem boundedDualGraph_vertex_corner_of_adj
    {R S : ℕ} {X : Finset (Fin (R + 1) × Fin (S + 1))}
    (hX : ∀ p ∈ X, 0 < p.1.1 ∧ p.1.1 < R ∧
      0 < p.2.1 ∧ p.2.1 < S)
    {f g : BoundedFace (R + 1) (S + 1)}
    (hfg : (boundedDualGraph X).Adj f g) :
    ∃ p ∈ X, UnitSquareCorner (faceSquareStart p) (boundedFaceCoord f) := by
  rcases hfg.2 with ⟨e, heX, hlink⟩
  rcases mem_vacancyDualEdges.mp heX with ⟨p, hpX, hpinc⟩
  refine ⟨p, hpX, ?_⟩
  have hpBounds := hX p hpX
  have hfend : some f ∈ (rectangleDual (R + 1) (S + 1)).ends e := by
    rw [hlink]
    exact Sym2.mem_mk_left _ _
  cases e with
  | horizontal e =>
      change p = horizontalPrimalLeft e ∨ p = horizontalPrimalRight e at hpinc
      change some f ∈ s(horizontalBelow e, horizontalAbove e) at hfend
      rcases Sym2.mem_iff.mp hfend with hf | hf
      · by_cases hy0 : e.y.1 = 0
        · rw [horizontalBelow, dif_pos hy0] at hf
          cases hf
        · rw [horizontalBelow, dif_neg hy0] at hf
          have hf' := Option.some.inj hf
          have hfx := congrArg (fun z : BoundedFace (R + 1) (S + 1) => z.1.1) hf'
          have hfy := congrArg (fun z : BoundedFace (R + 1) (S + 1) => z.2.1) hf'
          rcases hpinc with hpLeft | hpRight
          · have hpx := congrArg (fun z => z.1.1) hpLeft
            have hpy := congrArg (fun z => z.2.1) hpLeft
            simp only [UnitSquareCorner, faceSquareStart, boundedFaceCoord]
            simp [horizontalPrimalLeft] at hpx hpy
            simp only at hfx hfy
            omega
          · have hpx := congrArg (fun z => z.1.1) hpRight
            have hpy := congrArg (fun z => z.2.1) hpRight
            simp only [UnitSquareCorner, faceSquareStart, boundedFaceCoord]
            simp [horizontalPrimalRight] at hpx hpy
            simp only at hfx hfy
            omega
      · by_cases hytop : e.y.1 + 1 < S + 1
        · rw [horizontalAbove, dif_pos hytop] at hf
          have hf' := Option.some.inj hf
          have hfx := congrArg (fun z : BoundedFace (R + 1) (S + 1) => z.1.1) hf'
          have hfy := congrArg (fun z : BoundedFace (R + 1) (S + 1) => z.2.1) hf'
          rcases hpinc with hpLeft | hpRight
          · have hpx := congrArg (fun z => z.1.1) hpLeft
            have hpy := congrArg (fun z => z.2.1) hpLeft
            simp only [UnitSquareCorner, faceSquareStart, boundedFaceCoord]
            simp [horizontalPrimalLeft] at hpx hpy
            simp only at hfx hfy
            omega
          · have hpx := congrArg (fun z => z.1.1) hpRight
            have hpy := congrArg (fun z => z.2.1) hpRight
            simp only [UnitSquareCorner, faceSquareStart, boundedFaceCoord]
            simp [horizontalPrimalRight] at hpx hpy
            simp only at hfx hfy
            omega
        · rw [horizontalAbove, dif_neg hytop] at hf
          cases hf
  | vertical e =>
      change p = verticalPrimalBottom e ∨ p = verticalPrimalTop e at hpinc
      change some f ∈ s(verticalLeft e, verticalRight e) at hfend
      rcases Sym2.mem_iff.mp hfend with hf | hf
      · by_cases hx0 : e.x.1 = 0
        · rw [verticalLeft, dif_pos hx0] at hf
          cases hf
        · rw [verticalLeft, dif_neg hx0] at hf
          have hf' := Option.some.inj hf
          have hfx := congrArg (fun z : BoundedFace (R + 1) (S + 1) => z.1.1) hf'
          have hfy := congrArg (fun z : BoundedFace (R + 1) (S + 1) => z.2.1) hf'
          rcases hpinc with hpBottom | hpTop
          · have hpx := congrArg (fun z => z.1.1) hpBottom
            have hpy := congrArg (fun z => z.2.1) hpBottom
            simp only [UnitSquareCorner, faceSquareStart, boundedFaceCoord]
            simp [verticalPrimalBottom] at hpx hpy
            simp only at hfx hfy
            omega
          · have hpx := congrArg (fun z => z.1.1) hpTop
            have hpy := congrArg (fun z => z.2.1) hpTop
            simp only [UnitSquareCorner, faceSquareStart, boundedFaceCoord]
            simp [verticalPrimalTop] at hpx hpy
            simp only at hfx hfy
            omega
      · by_cases hxright : e.x.1 + 1 < R + 1
        · rw [verticalRight, dif_pos hxright] at hf
          have hf' := Option.some.inj hf
          have hfx := congrArg (fun z : BoundedFace (R + 1) (S + 1) => z.1.1) hf'
          have hfy := congrArg (fun z : BoundedFace (R + 1) (S + 1) => z.2.1) hf'
          rcases hpinc with hpBottom | hpTop
          · have hpx := congrArg (fun z => z.1.1) hpBottom
            have hpy := congrArg (fun z => z.2.1) hpBottom
            simp only [UnitSquareCorner, faceSquareStart, boundedFaceCoord]
            simp [verticalPrimalBottom] at hpx hpy
            simp only at hfx hfy
            omega
          · have hpx := congrArg (fun z => z.1.1) hpTop
            have hpy := congrArg (fun z => z.2.1) hpTop
            simp only [UnitSquareCorner, faceSquareStart, boundedFaceCoord]
            simp [verticalPrimalTop] at hpx hpy
            simp only at hfx hfy
            omega
        · rw [verticalRight, dif_neg hxright] at hf
          cases hf

/-! ## Complete unit squares contributed by interior primal vertices -/

/-- A natural-coordinate unit square is completely present in a graph
presented inside the square lattice. -/
def ContainsUnitSquare {V : Type*} (H : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint) (z : Boundary.LatticePoint) : Prop :=
  ∃ sw se nw ne : V,
    coord sw = z ∧
    coord se = (z.1 + 1, z.2) ∧
    coord nw = (z.1, z.2 + 1) ∧
    coord ne = (z.1 + 1, z.2 + 1) ∧
    H.Adj sw se ∧ H.Adj sw nw ∧ H.Adj se ne ∧ H.Adj nw ne

/-- Every coordinate satisfying the unit-square corner inequalities is
represented by one of the four displayed vertices. -/
theorem ContainsUnitSquare.exists_vertex_of_corner
    {V : Type*} {H : SimpleGraph V}
    {coord : V ↪ Boundary.LatticePoint} {z w : Boundary.LatticePoint}
    (h : ContainsUnitSquare H coord z) (hw : UnitSquareCorner z w) :
    ∃ v : V, coord v = w := by
  rcases h with ⟨sw, se, nw, ne, hsw, hse, hnw, hne, _⟩
  have hx : w.1 = z.1 ∨ w.1 = z.1 + 1 := by
    dsimp only [UnitSquareCorner] at hw
    omega
  have hy : w.2 = z.2 ∨ w.2 = z.2 + 1 := by
    dsimp only [UnitSquareCorner] at hw
    omega
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact ⟨sw, hsw.trans (Prod.ext hx.symm hy.symm)⟩
  · exact ⟨nw, hnw.trans (Prod.ext hx.symm hy.symm)⟩
  · exact ⟨se, hse.trans (Prod.ext hx.symm hy.symm)⟩
  · exact ⟨ne, hne.trans (Prod.ext hx.symm hy.symm)⟩

/-- A displayed complete square has a distinguished southwest vertex from
which every vertex at one of its four coordinates is reachable. -/
theorem ContainsUnitSquare.exists_reachable_corner
    {V : Type*} {H : SimpleGraph V}
    {coord : V ↪ Boundary.LatticePoint} {z : Boundary.LatticePoint}
    (h : ContainsUnitSquare H coord z) :
    ∃ a : V, coord a = z ∧
      ∀ v : V, UnitSquareCorner z (coord v) → H.Reachable a v := by
  rcases h with ⟨sw, se, nw, ne, hsw, hse, hnw, hne,
    hswse, hswnw, hsene, hnwne⟩
  refine ⟨sw, hsw, ?_⟩
  intro v hv
  have hx : (coord v).1 = z.1 ∨ (coord v).1 = z.1 + 1 := by
    dsimp only [UnitSquareCorner] at hv
    omega
  have hy : (coord v).2 = z.2 ∨ (coord v).2 = z.2 + 1 := by
    dsimp only [UnitSquareCorner] at hv
    omega
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have hvco : coord v = coord sw := by
      rw [hsw]
      exact Prod.ext hx hy
    rw [coord.injective hvco]
  · have hvco : coord v = coord nw := by
      rw [hnw]
      exact Prod.ext hx hy
    rw [coord.injective hvco]
    exact hswnw.reachable
  · have hvco : coord v = coord se := by
      rw [hse]
      exact Prod.ext hx hy
    rw [coord.injective hvco]
    exact hswse.reachable
  · have hvco : coord v = coord ne := by
      rw [hne]
      exact Prod.ext hx hy
    rw [coord.injective hvco]
    exact hswse.reachable.trans hsene.reachable

/-- Unit squares centered at king-adjacent positive natural points share a
corner coordinate. -/
theorem faceSquares_overlap_of_kingAdjacent
    {R S : ℕ} {p q : Fin (R + 1) × Fin (S + 1)}
    (hp : 0 < p.1.1 ∧ 0 < p.2.1) (hq : 0 < q.1.1 ∧ 0 < q.2.1)
    (hpq : Boundary.KingAdjacent (finPoint p) (finPoint q)) :
    ∃ w, UnitSquareCorner (faceSquareStart p) w ∧
      UnitSquareCorner (faceSquareStart q) w := by
  let w : Boundary.LatticePoint :=
    (max (p.1.1 - 1) (q.1.1 - 1), max (p.2.1 - 1) (q.2.1 - 1))
  refine ⟨w, ?_, ?_⟩
  all_goals
    simp only [UnitSquareCorner, faceSquareStart, w, finPoint] at hpq ⊢
    simp only [Boundary.KingAdjacent] at hpq
    simp only [Nat.dist] at hpq
    omega

/-- A canonical interior vacancy never lies on the rectangular perimeter. -/
theorem canonicalInteriorPrimal_not_perimeter
    {R S : ℕ} {A : Finset Point}
    {i : Fin (Boundary.canonicalInteriorCount R S A)}
    {p : Fin (R + 1) × Fin (S + 1)}
    (hp : p ∈ canonicalInteriorPrimal R S A i) :
    ¬ Boundary.IsPerimeter R S (finPoint p) := by
  let V := Boundary.canonicalVacancies R S A
  have hpC : finPoint p ∈ Boundary.interiorComponent R S V
      ((Boundary.canonicalInteriorEquiv R S A).symm i) :=
    mem_canonicalInteriorPrimal.mp hp
  have hpI : finPoint p ∈ Boundary.interiorVacancies R S V :=
    Boundary.interiorComponent_subset_interiorVacancies R S V _ hpC
  intro hperim
  exact (Boundary.mem_interiorVacancies.mp hpI).2
    (Boundary.isBoundaryAttached_of_perimeter
      (Boundary.mem_interiorVacancies.mp hpI).1 hperim)

theorem canonicalInteriorPrimal_bounds
    {R S : ℕ} {A : Finset Point}
    {i : Fin (Boundary.canonicalInteriorCount R S A)}
    {p : Fin (R + 1) × Fin (S + 1)}
    (hp : p ∈ canonicalInteriorPrimal R S A i) :
    0 < p.1.1 ∧ p.1.1 < R ∧ 0 < p.2.1 ∧ p.2.1 < S := by
  have hnot := canonicalInteriorPrimal_not_perimeter hp
  have hxle : p.1.1 ≤ R := Nat.le_of_lt_succ p.1.2
  have hyle : p.2.1 ≤ S := Nat.le_of_lt_succ p.2.2
  simp only [Boundary.IsPerimeter, finPoint] at hnot
  omega

/-! ## Connectivity of the face-star union -/

/-- King adjacency on the explicit finite primal vertices of one canonical
interior component. -/
noncomputable def canonicalInteriorPrimalKingGraph
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    SimpleGraph {p // p ∈ canonicalInteriorPrimal R S A i} :=
  SimpleGraph.fromRel fun p q =>
    Boundary.KingAdjacent (finPoint p.1) (finPoint q.1)

@[simp] theorem canonicalInteriorPrimalKingGraph_adj_iff
    {R S : ℕ} {A : Finset Point}
    {i : Fin (Boundary.canonicalInteriorCount R S A)}
    (p q : {p // p ∈ canonicalInteriorPrimal R S A i}) :
    (canonicalInteriorPrimalKingGraph R S A i).Adj p q ↔
      Boundary.KingAdjacent (finPoint p.1) (finPoint q.1) := by
  simp only [canonicalInteriorPrimalKingGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, hpq | hqp⟩
    · exact hpq
    · exact @Std.Symm.symm _ _ Boundary.kingAdjacent_symm _ _ hqp
  · intro hpq
    refine ⟨?_, Or.inl hpq⟩
    intro h
    exact hpq.1 (congrArg finPoint (Subtype.ext_iff.mp h))

/-- The explicit primal component is graph-isomorphic to the corresponding
connected-component support of the original king graph. -/
noncomputable def canonicalInteriorPrimalKingIso
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    canonicalInteriorPrimalKingGraph R S A i ≃g
      ((Boundary.canonicalInteriorEquiv R S A).symm i).1.toSimpleGraph := by
  let V := Boundary.canonicalVacancies R S A
  let C := ((Boundary.canonicalInteriorEquiv R S A).symm i).1
  let X := canonicalInteriorPrimal R S A i
  let e : {p // p ∈ X} ≃ {z : {z // z ∈ V} // z ∈ C.supp} :=
    {
      toFun := fun p => by
        have hpC : finPoint p.1 ∈ Boundary.interiorComponent R S V
            ((Boundary.canonicalInteriorEquiv R S A).symm i) :=
          mem_canonicalInteriorPrimal.mp p.2
        let hpData := Boundary.mem_interiorComponent.mp hpC
        let hpV : finPoint p.1 ∈ V := Classical.choose hpData
        have hpClass := Classical.choose_spec hpData
        exact ⟨⟨finPoint p.1, hpV⟩,
          (SimpleGraph.ConnectedComponent.mem_supp_iff C _).mpr hpClass⟩
      invFun := fun z => by
        have hzGrid : z.1.1 ∈ Boundary.grid R S :=
          encodedVacancies_subset_grid R S A z.1.2
        let p : Fin (R + 1) × Fin (S + 1) :=
          (finGridEquiv R S).symm ⟨z.1.1, hzGrid⟩
        refine ⟨p, mem_canonicalInteriorPrimal.mpr ?_⟩
        exact Boundary.mem_interiorComponent.mpr ⟨z.1.2,
          (SimpleGraph.ConnectedComponent.mem_supp_iff C _).mp z.2⟩
      left_inv := by
        intro p
        apply Subtype.ext
        apply (finGridEquiv R S).injective
        apply Subtype.ext
        simp
      right_inv := by
        intro z
        apply Subtype.ext
        apply Subtype.ext
        simp
    }
  exact {
    toEquiv := e
    map_rel_iff' := by
      intro p q
      rw [canonicalInteriorPrimalKingGraph_adj_iff,
        SimpleGraph.ConnectedComponent.toSimpleGraph_adj,
        Boundary.kingGraph_adj_iff]
      simp [e]
  }

/-- Each canonical interior primal component is connected for king moves. -/
theorem canonicalInteriorPrimalKingGraph_connected
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    (canonicalInteriorPrimalKingGraph R S A i).Connected := by
  exact (canonicalInteriorPrimalKingIso R S A i).connected_iff.mpr
    (SimpleGraph.ConnectedComponent.connected_toSimpleGraph _)

/-- The square-start map is injective on any collection of interior primal
vertices. -/
theorem faceSquareStart_injectiveOn
    {R S : ℕ} {X : Finset (Fin (R + 1) × Fin (S + 1))}
    (hX : ∀ p ∈ X, 0 < p.1.1 ∧ 0 < p.2.1) :
    Set.InjOn faceSquareStart (X : Set (Fin (R + 1) × Fin (S + 1))) := by
  intro p hp q hq h
  apply Prod.ext <;> apply Fin.ext
  · have hp0 := (hX p hp).1
    have hq0 := (hX q hq).1
    have hcoord := congrArg Prod.fst h
    simp only [faceSquareStart] at hcoord
    omega
  · have hp0 := (hX p hp).2
    have hq0 := (hX q hq).2
    have hcoord := congrArg Prod.snd h
    simp only [faceSquareStart] at hcoord
    omega

/-- The explicitly exhibited unit-square starts in one interior component. -/
noncomputable def interiorSquareStarts
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    Finset Boundary.LatticePoint := by
  classical
  exact (canonicalInteriorPrimal R S A i).image faceSquareStart

theorem card_canonicalInteriorPrimal_eq
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    (canonicalInteriorPrimal R S A i).card =
      (Boundary.canonicalInterior R S A i).card := by
  classical
  let C := Boundary.interiorComponent R S (Boundary.canonicalVacancies R S A)
    ((Boundary.canonicalInteriorEquiv R S A).symm i)
  have hprimal : (canonicalInteriorPrimal R S A i).image finPoint = C := by
    ext z
    constructor
    · rintro hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      exact mem_canonicalInteriorPrimal.mp hp
    · intro hz
      have hzI : z ∈ Boundary.interiorVacancies R S
          (Boundary.canonicalVacancies R S A) :=
        Boundary.interiorComponent_subset_interiorVacancies R S
          (Boundary.canonicalVacancies R S A)
          ((Boundary.canonicalInteriorEquiv R S A).symm i) hz
      have hzV : z ∈ Boundary.canonicalVacancies R S A :=
        Boundary.interiorVacancies_subset R S _ hzI
      have hzGrid : z ∈ Boundary.grid R S :=
        encodedVacancies_subset_grid R S A hzV
      let p : Fin (R + 1) × Fin (S + 1) :=
        (finGridEquiv R S).symm ⟨z, hzGrid⟩
      have hpz : finPoint p = z := by simp [p]
      exact Finset.mem_image.mpr ⟨p,
        mem_canonicalInteriorPrimal.mpr (hpz.symm ▸ hz), hpz⟩
  calc
    (canonicalInteriorPrimal R S A i).card =
        ((canonicalInteriorPrimal R S A i).image finPoint).card :=
      (Finset.card_image_of_injective _ finPoint_injective).symm
    _ = C.card := congrArg Finset.card hprimal
    _ = (C.image Boundary.ofNatPoint).card :=
      (Finset.card_image_of_injective _ Boundary.ofNatPoint_injective).symm
    _ = (Boundary.canonicalInterior R S A i).card := by
      rfl

/-- The four dual edges incident with an interior primal vertex form a
complete unit square in the bounded dual core. -/
theorem containsUnitSquare_faceSquareStart
    {R S : ℕ} {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {p : Fin (R + 1) × Fin (S + 1)} (hp : p ∈ X)
    (hbounds : 0 < p.1.1 ∧ p.1.1 < R ∧
      0 < p.2.1 ∧ p.2.1 < S) :
    ContainsUnitSquare (boundedDualCore X) (boundedDualCoreCoord X)
      (faceSquareStart p) := by
  let sw : BoundedFace (R + 1) (S + 1) :=
    (⟨p.1.1 - 1, by omega⟩, ⟨p.2.1 - 1, by omega⟩)
  let se : BoundedFace (R + 1) (S + 1) :=
    (⟨p.1.1, by omega⟩, ⟨p.2.1 - 1, by omega⟩)
  let nw : BoundedFace (R + 1) (S + 1) :=
    (⟨p.1.1 - 1, by omega⟩, ⟨p.2.1, by omega⟩)
  let ne : BoundedFace (R + 1) (S + 1) :=
    (⟨p.1.1, by omega⟩, ⟨p.2.1, by omega⟩)
  have hswse : (boundedDualGraph X).Adj sw se := by
    refine ⟨?_, ?_⟩
    · intro h
      have h' : sw = se := Option.some.inj h
      have := congrArg (fun f : BoundedFace (R + 1) (S + 1) => f.1.1) h'
      simp only [sw, se] at this
      omega
    · let e : VerticalEdge (R + 1) (S + 1) :=
        ⟨p.1, ⟨p.2.1 - 1, by omega⟩⟩
      refine ⟨RectangleEdge.vertical e, ?_, ?_⟩
      · apply mem_vacancyDualEdges.mpr
        refine ⟨p, hp, Or.inr ?_⟩
        apply Prod.ext <;> apply Fin.ext
        · rfl
        · simp [e, verticalPrimalTop]
          omega
      ·
        have hx0 : p.1.1 ≠ 0 := by omega
        have hxR : p.1.1 + 1 < R + 1 := by omega
        simp only [Multigraph.LabeledMultigraph.IsLink,
          rectangleDual_vertical_ends]
        simp [e, verticalLeft, verticalRight, sw, se, hx0, hxR]
  have hswnw : (boundedDualGraph X).Adj sw nw := by
    refine ⟨?_, ?_⟩
    · intro h
      have h' : sw = nw := Option.some.inj h
      have := congrArg (fun f : BoundedFace (R + 1) (S + 1) => f.2.1) h'
      simp only [sw, nw] at this
      omega
    · let e : HorizontalEdge (R + 1) (S + 1) :=
        ⟨⟨p.1.1 - 1, by omega⟩, p.2⟩
      refine ⟨RectangleEdge.horizontal e, ?_, ?_⟩
      · apply mem_vacancyDualEdges.mpr
        refine ⟨p, hp, Or.inr ?_⟩
        apply Prod.ext <;> apply Fin.ext
        · simp [e, horizontalPrimalRight]
          omega
        · rfl
      ·
        have hy0 : p.2.1 ≠ 0 := by omega
        have hyS : p.2.1 + 1 < S + 1 := by omega
        simp only [Multigraph.LabeledMultigraph.IsLink,
          rectangleDual_horizontal_ends]
        simp [e, horizontalBelow, horizontalAbove, sw, nw, hy0, hyS]
  have hsene : (boundedDualGraph X).Adj se ne := by
    refine ⟨?_, ?_⟩
    · intro h
      have h' : se = ne := Option.some.inj h
      have := congrArg (fun f : BoundedFace (R + 1) (S + 1) => f.2.1) h'
      simp only [se, ne] at this
      omega
    · let e : HorizontalEdge (R + 1) (S + 1) :=
        ⟨⟨p.1.1, by omega⟩, p.2⟩
      refine ⟨RectangleEdge.horizontal e, ?_, ?_⟩
      · apply mem_vacancyDualEdges.mpr
        refine ⟨p, hp, Or.inl ?_⟩
        apply Prod.ext <;> apply Fin.ext <;> rfl
      ·
        have hy0 : p.2.1 ≠ 0 := by omega
        have hyS : p.2.1 + 1 < S + 1 := by omega
        simp only [Multigraph.LabeledMultigraph.IsLink,
          rectangleDual_horizontal_ends]
        simp [e, horizontalBelow, horizontalAbove, se, ne, hy0, hyS]
  have hnwne : (boundedDualGraph X).Adj nw ne := by
    refine ⟨?_, ?_⟩
    · intro h
      have h' : nw = ne := Option.some.inj h
      have := congrArg (fun f : BoundedFace (R + 1) (S + 1) => f.1.1) h'
      simp only [nw, ne] at this
      omega
    · let e : VerticalEdge (R + 1) (S + 1) :=
        ⟨p.1, ⟨p.2.1, by omega⟩⟩
      refine ⟨RectangleEdge.vertical e, ?_, ?_⟩
      · apply mem_vacancyDualEdges.mpr
        refine ⟨p, hp, Or.inl ?_⟩
        apply Prod.ext <;> apply Fin.ext <;> rfl
      ·
        have hx0 : p.1.1 ≠ 0 := by omega
        have hxR : p.1.1 + 1 < R + 1 := by omega
        simp only [Multigraph.LabeledMultigraph.IsLink,
          rectangleDual_vertical_ends]
        simp [e, verticalLeft, verticalRight, nw, ne, hx0, hxR]
  let sw' : {f // f ∈ (boundedDualGraph X).support} :=
    ⟨sw, hswse.mem_support_left⟩
  let se' : {f // f ∈ (boundedDualGraph X).support} :=
    ⟨se, hswse.mem_support_right⟩
  let nw' : {f // f ∈ (boundedDualGraph X).support} :=
    ⟨nw, hswnw.mem_support_right⟩
  let ne' : {f // f ∈ (boundedDualGraph X).support} :=
    ⟨ne, hsene.mem_support_right⟩
  refine ⟨sw', se', nw', ne', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Prod.ext <;> simp [boundedDualCoreCoord, boundedFaceCoord, sw', sw,
      faceSquareStart]
  · apply Prod.ext <;> simp [boundedDualCoreCoord, boundedFaceCoord, se', se,
      faceSquareStart]
    omega
  · apply Prod.ext <;> simp [boundedDualCoreCoord, boundedFaceCoord, nw', nw,
      faceSquareStart]
    omega
  · apply Prod.ext <;> simp [boundedDualCoreCoord, boundedFaceCoord, ne', ne,
      faceSquareStart]
    all_goals omega
  · exact hswse
  · exact hswnw
  · exact hsene
  · exact hnwne

/-- Every canonical interior vacancy contributes its distinct complete unit
square to the explicit face-star core. -/
theorem interiorSquareStarts_complete
    {R S : ℕ} {A : Finset Point}
    (i : Fin (Boundary.canonicalInteriorCount R S A))
    {z : Boundary.LatticePoint} (hz : z ∈ interiorSquareStarts R S A i) :
    ContainsUnitSquare (interiorFaceStarGraph R S A i)
      (boundedDualCoreCoord (canonicalInteriorPrimal R S A i)) z := by
  classical
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  exact containsUnitSquare_faceSquareStart hp
    (canonicalInteriorPrimal_bounds hp)

/-- A consistent southwest anchor vertex for the square contributed by a
canonical interior primal vertex. -/
noncomputable def interiorSquareAnchor
    {R S : ℕ} {A : Finset Point}
    (i : Fin (Boundary.canonicalInteriorCount R S A))
    (p : {p // p ∈ canonicalInteriorPrimal R S A i}) :
    {f // f ∈
      (boundedDualGraph (canonicalInteriorPrimal R S A i)).support} :=
  Classical.choose
    (ContainsUnitSquare.exists_reachable_corner
      (containsUnitSquare_faceSquareStart p.2
        (canonicalInteriorPrimal_bounds p.2)))

@[simp] theorem interiorSquareAnchor_coord
    {R S : ℕ} {A : Finset Point}
    (i : Fin (Boundary.canonicalInteriorCount R S A))
    (p : {p // p ∈ canonicalInteriorPrimal R S A i}) :
    boundedDualCoreCoord (canonicalInteriorPrimal R S A i)
        (interiorSquareAnchor i p) = faceSquareStart p.1 := by
  exact (Classical.choose_spec
    (ContainsUnitSquare.exists_reachable_corner
      (containsUnitSquare_faceSquareStart p.2
        (canonicalInteriorPrimal_bounds p.2)))).1

theorem interiorSquareAnchor_reaches_corner
    {R S : ℕ} {A : Finset Point}
    (i : Fin (Boundary.canonicalInteriorCount R S A))
    (p : {p // p ∈ canonicalInteriorPrimal R S A i})
    (v : {f // f ∈
      (boundedDualGraph (canonicalInteriorPrimal R S A i)).support})
    (hv : UnitSquareCorner (faceSquareStart p.1)
      (boundedDualCoreCoord (canonicalInteriorPrimal R S A i) v)) :
    (interiorFaceStarGraph R S A i).Reachable
      (interiorSquareAnchor i p) v := by
  exact (Classical.choose_spec
    (ContainsUnitSquare.exists_reachable_corner
      (containsUnitSquare_faceSquareStart p.2
        (canonicalInteriorPrimal_bounds p.2)))).2 v hv

/-- King-adjacent component vertices have mutually reachable face-square
anchors because their two complete unit squares share a bounded face. -/
theorem interiorSquareAnchor_reachable_of_adj
    {R S : ℕ} {A : Finset Point}
    {i : Fin (Boundary.canonicalInteriorCount R S A)}
    {p q : {p // p ∈ canonicalInteriorPrimal R S A i}}
    (hpq : (canonicalInteriorPrimalKingGraph R S A i).Adj p q) :
    (interiorFaceStarGraph R S A i).Reachable
      (interiorSquareAnchor i p) (interiorSquareAnchor i q) := by
  have hpqKing := (canonicalInteriorPrimalKingGraph_adj_iff p q).mp hpq
  obtain ⟨w, hpw, hqw⟩ := faceSquares_overlap_of_kingAdjacent
    ⟨(canonicalInteriorPrimal_bounds p.2).1,
      (canonicalInteriorPrimal_bounds p.2).2.2.1⟩
    ⟨(canonicalInteriorPrimal_bounds q.2).1,
      (canonicalInteriorPrimal_bounds q.2).2.2.1⟩ hpqKing
  obtain ⟨v, hvcoord⟩ := ContainsUnitSquare.exists_vertex_of_corner
    (containsUnitSquare_faceSquareStart p.2
      (canonicalInteriorPrimal_bounds p.2)) hpw
  have hpv : (interiorFaceStarGraph R S A i).Reachable
      (interiorSquareAnchor i p) v :=
    interiorSquareAnchor_reaches_corner i p v (by simpa [hvcoord] using hpw)
  have hqv : (interiorFaceStarGraph R S A i).Reachable
      (interiorSquareAnchor i q) v :=
    interiorSquareAnchor_reaches_corner i q v (by simpa [hvcoord] using hqw)
  exact hpv.trans hqv.symm

/-- King reachability of primal component vertices transports to
reachability of their face-square anchors. -/
theorem interiorSquareAnchor_reachable
    {R S : ℕ} {A : Finset Point}
    {i : Fin (Boundary.canonicalInteriorCount R S A)}
    {p q : {p // p ∈ canonicalInteriorPrimal R S A i}}
    (hpq : (canonicalInteriorPrimalKingGraph R S A i).Reachable p q) :
    (interiorFaceStarGraph R S A i).Reachable
      (interiorSquareAnchor i p) (interiorSquareAnchor i q) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hpq ⊢
  apply hpq.lift' (interiorSquareAnchor i)
  intro u v huv
  change Relation.ReflTransGen (interiorFaceStarGraph R S A i).Adj
    (interiorSquareAnchor i u) (interiorSquareAnchor i v)
  rw [← SimpleGraph.reachable_iff_reflTransGen]
  exact interiorSquareAnchor_reachable_of_adj huv

/-- Every vertex of the bounded dual core lies in one of the displayed
face-star squares and is therefore reachable from that square's anchor. -/
theorem exists_interiorSquareAnchor_reaching
    {R S : ℕ} {A : Finset Point}
    (i : Fin (Boundary.canonicalInteriorCount R S A))
    (v : {f // f ∈
      (boundedDualGraph (canonicalInteriorPrimal R S A i)).support}) :
    ∃ p : {p // p ∈ canonicalInteriorPrimal R S A i},
      (interiorFaceStarGraph R S A i).Reachable
        (interiorSquareAnchor i p) v := by
  obtain ⟨g, hvg⟩ :=
    (boundedDualGraph (canonicalInteriorPrimal R S A i)).mem_support.mp v.2
  obtain ⟨p, hp, hpCorner⟩ := boundedDualGraph_vertex_corner_of_adj
    (fun p hp => canonicalInteriorPrimal_bounds hp) hvg
  refine ⟨⟨p, hp⟩, interiorSquareAnchor_reaches_corner i ⟨p, hp⟩ v ?_⟩
  exact hpCorner

/-- The union of face-stars of one canonical interior king component is
connected.  This discharges the connectivity assertion preceding the
manuscript's invocation of Tapp. -/
theorem interiorFaceStarGraph_connected
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    (interiorFaceStarGraph R S A i).Connected := by
  let hKing := canonicalInteriorPrimalKingGraph_connected R S A i
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  obtain ⟨p⟩ := hKing.nonempty
  refine ⟨interiorSquareAnchor i p, ?_⟩
  intro v
  obtain ⟨q, hqv⟩ := exists_interiorSquareAnchor_reaching i v
  have hpq : (canonicalInteriorPrimalKingGraph R S A i).Reachable p q :=
    hKing.preconnected p q
  exact (interiorSquareAnchor_reachable hpq).trans hqv

/-! ## The finite spanning-tree event family -/

/-- The exact finite spanning-tree type counted by `treeCount` for one
interior face-star graph. -/
abbrev InteriorFaceStarTree
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :=
  {T : SimpleGraph {f // f ∈
      (boundedDualGraph (canonicalInteriorPrimal R S A i)).support} //
    T ≤ interiorFaceStarGraph R S A i ∧ T.IsTree}

noncomputable instance interiorFaceStarTreeFintype
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    Fintype (InteriorFaceStarTree R S A i) :=
  Fintype.ofFinite _

noncomputable def interiorFaceStarTreeCount
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) : ℕ :=
  Fintype.card (InteriorFaceStarTree R S A i)

theorem interiorFaceStarTreeCount_eq_treeCount
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    interiorFaceStarTreeCount R S A i =
      treeCount (interiorFaceStarGraph R S A i) := by
  rw [interiorFaceStarTreeCount, treeCount, Nat.card_eq_fintype_card]

/-- Canonical enumeration of all face-star spanning trees. -/
noncomputable def interiorFaceStarTreeAt
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    Fin (interiorFaceStarTreeCount R S A i) →
      InteriorFaceStarTree R S A i :=
  (Fintype.equivFin (InteriorFaceStarTree R S A i)).symm

/-- Embed a bounded-core vertex into the ambient rectangular dual. -/
def boundedDualCoreToDualVertex {r s : ℕ}
    (X : Finset (Fin r × Fin s)) :
    {f // f ∈ (boundedDualGraph X).support} ↪ RectangleDualVertex r s where
  toFun f := some f.1
  inj' := fun _ _ h => Subtype.ext (Option.some.inj h)

private theorem exists_ambientLabel_of_faceStarEdge
    {R S : ℕ} {A : Finset Point}
    {i : Fin (Boundary.canonicalInteriorCount R S A)}
    (T : InteriorFaceStarTree R S A i) (p : T.1.edgeSet) :
    ∃ e ∈ vacancyDualEdges (canonicalInteriorPrimal R S A i),
      (rectangleDual (R + 1) (S + 1)).ends e =
        Sym2.map (boundedDualCoreToDualVertex
          (canonicalInteriorPrimal R S A i)) p.1 := by
  induction hp : p.1 using Sym2.inductionOn with
  | _ u v =>
      have huvT : T.1.Adj u v := by
        rw [← SimpleGraph.mem_edgeSet, ← hp]
        exact p.2
      have huvH := T.2.1 huvT
      change (boundedDualGraph (canonicalInteriorPrimal R S A i)).Adj u.1 v.1 at huvH
      rcases huvH.2 with ⟨e, he, hlink⟩
      refine ⟨e, he, ?_⟩
      change (rectangleDual (R + 1) (S + 1)).ends e = s(some u.1, some v.1) at hlink
      change (rectangleDual (R + 1) (S + 1)).ends e = s(some u.1, some v.1)
      simpa [hp, boundedDualCoreToDualVertex] using hlink

/-- Choose the ambient dual label representing one simple face-star edge. -/
noncomputable def ambientLabelOfFaceStarEdge
    {R S : ℕ} {A : Finset Point}
    {i : Fin (Boundary.canonicalInteriorCount R S A)}
    (T : InteriorFaceStarTree R S A i) (p : T.1.edgeSet) :
    RectangleEdge (R + 1) (S + 1) :=
  Classical.choose (exists_ambientLabel_of_faceStarEdge T p)

@[simp] theorem ambientLabelOfFaceStarEdge_mem
    {R S : ℕ} {A : Finset Point}
    {i : Fin (Boundary.canonicalInteriorCount R S A)}
    (T : InteriorFaceStarTree R S A i) (p : T.1.edgeSet) :
    ambientLabelOfFaceStarEdge T p ∈
      vacancyDualEdges (canonicalInteriorPrimal R S A i) :=
  (Classical.choose_spec (exists_ambientLabel_of_faceStarEdge T p)).1

theorem ambientLabelOfFaceStarEdge_ends
    {R S : ℕ} {A : Finset Point}
    {i : Fin (Boundary.canonicalInteriorCount R S A)}
    (T : InteriorFaceStarTree R S A i) (p : T.1.edgeSet) :
    (rectangleDual (R + 1) (S + 1)).ends
        (ambientLabelOfFaceStarEdge T p) =
      Sym2.map (boundedDualCoreToDualVertex
        (canonicalInteriorPrimal R S A i)) p.1 :=
  (Classical.choose_spec (exists_ambientLabel_of_faceStarEdge T p)).2

theorem ambientLabelOfFaceStarEdge_injective
    {R S : ℕ} {A : Finset Point}
    {i : Fin (Boundary.canonicalInteriorCount R S A)}
    (T : InteriorFaceStarTree R S A i) :
    Function.Injective (ambientLabelOfFaceStarEdge T) := by
  intro p q hpq
  apply Subtype.ext
  apply Sym2.map.injective (boundedDualCoreToDualVertex
    (canonicalInteriorPrimal R S A i)).injective
  rw [← ambientLabelOfFaceStarEdge_ends T p,
    ← ambientLabelOfFaceStarEdge_ends T q, hpq]

/-- Ambient dual edge block associated with one simple spanning tree of the
face-star graph. -/
noncomputable def ambientBlockOfFaceStarTree
    {R S : ℕ} {A : Finset Point}
    {i : Fin (Boundary.canonicalInteriorCount R S A)}
    (T : InteriorFaceStarTree R S A i) :
    Finset (RectangleEdge (R + 1) (S + 1)) := by
  classical
  letI := Fintype.ofFinite T.1.edgeSet
  exact Finset.univ.image (ambientLabelOfFaceStarEdge T)

@[simp] theorem mem_ambientBlockOfFaceStarTree
    {R S : ℕ} {A : Finset Point}
    {i : Fin (Boundary.canonicalInteriorCount R S A)}
    (T : InteriorFaceStarTree R S A i)
    (e : RectangleEdge (R + 1) (S + 1)) :
    e ∈ ambientBlockOfFaceStarTree T ↔
      ∃ p : T.1.edgeSet, ambientLabelOfFaceStarEdge T p = e := by
  classical
  simp [ambientBlockOfFaceStarTree]

/-- Pulling the chosen ambient labels back to the bounded-core vertex type
recovers the original simple spanning tree exactly. -/
theorem ambientBlockOfFaceStarTree_comap
    {R S : ℕ} {A : Finset Point}
    {i : Fin (Boundary.canonicalInteriorCount R S A)}
    (T : InteriorFaceStarTree R S A i) :
    ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
      (ambientBlockOfFaceStarTree T :
        Set (RectangleEdge (R + 1) (S + 1)))).comap
          (boundedDualCoreToDualVertex
            (canonicalInteriorPrimal R S A i)) = T.1 := by
  ext u v
  constructor
  · rintro ⟨huv, e, he, hlink⟩
    obtain ⟨p, rfl⟩ := (mem_ambientBlockOfFaceStarTree T e).mp he
    have hpEnds := ambientLabelOfFaceStarEdge_ends T p
    have hpPair : p.1 = s(u, v) := by
      apply Sym2.map.injective (boundedDualCoreToDualVertex
        (canonicalInteriorPrimal R S A i)).injective
      rw [Sym2.map_mk, ← hpEnds]
      exact hlink
    rw [← SimpleGraph.mem_edgeSet, ← hpPair]
    exact p.2
  · intro huv
    let p : T.1.edgeSet := ⟨s(u, v), huv⟩
    refine ⟨(boundedDualCoreToDualVertex
      (canonicalInteriorPrimal R S A i)).injective.ne huv.ne,
      ambientLabelOfFaceStarEdge T p, ?_, ?_⟩
    · exact (mem_ambientBlockOfFaceStarTree T _).mpr ⟨p, rfl⟩
    · change (rectangleDual (R + 1) (S + 1)).ends
          (ambientLabelOfFaceStarEdge T p) = _
      rw [ambientLabelOfFaceStarEdge_ends T p]
      rfl

/-- The ambient dual edge block in the canonical finite enumeration. -/
noncomputable def interiorEventBlock
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A))
    (j : Fin (interiorFaceStarTreeCount R S A i)) :
    Finset (RectangleEdge (R + 1) (S + 1)) :=
  ambientBlockOfFaceStarTree (interiorFaceStarTreeAt R S A i j)

theorem interiorEventBlock_subset_vacancyDualEdges
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A))
    (j : Fin (interiorFaceStarTreeCount R S A i)) :
    interiorEventBlock R S A i j ⊆
      vacancyDualEdges (canonicalInteriorPrimal R S A i) := by
  intro e he
  obtain ⟨p, rfl⟩ :=
    (mem_ambientBlockOfFaceStarTree
      (interiorFaceStarTreeAt R S A i j) e).mp he
  exact ambientLabelOfFaceStarEdge_mem _ _

/-- Distinct spanning trees of the same face-star graph give incompatible
ambient containment events.  The proof uses only acyclicity: an ambient tree
restricted to the core cannot contain two different maximal acyclic graphs
on that same vertex type. -/
theorem interiorEventBlock_incompatible
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    (rectangleDual (R + 1) (S + 1)).PairwiseIncompatible
      (interiorEventBlock R S A i) := by
  classical
  letI : DecidableEq (RectangleEdge (R + 1) (S + 1)) := Classical.decEq _
  intro j k hjk hforest
  rcases hforest with ⟨U, hUnionU⟩
  let Tj := interiorFaceStarTreeAt R S A i j
  let Tk := interiorFaceStarTreeAt R S A i k
  let emb := boundedDualCoreToDualVertex
    (canonicalInteriorPrimal R S A i)
  let K := ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
    (U.1 : Set (RectangleEdge (R + 1) (S + 1)))).comap emb
  have hBjU : ambientBlockOfFaceStarTree Tj ⊆ U.1 := by
    intro e he
    apply hUnionU
    exact Finset.mem_union_left _ he
  have hBkU : ambientBlockOfFaceStarTree Tk ⊆ U.1 := by
    intro e he
    apply hUnionU
    exact Finset.mem_union_right _ he
  have hTjK : Tj.1 ≤ K := by
    intro u v huv
    have huvBlock :
        (((rectangleDual (R + 1) (S + 1)).simpleGraphOn
          (ambientBlockOfFaceStarTree Tj :
            Set (RectangleEdge (R + 1) (S + 1)))).comap emb).Adj u v := by
      rw [ambientBlockOfFaceStarTree_comap Tj]
      exact huv
    exact (rectangleDual (R + 1) (S + 1)).simpleGraphOn_mono hBjU huvBlock
  have hTkK : Tk.1 ≤ K := by
    intro u v huv
    have huvBlock :
        (((rectangleDual (R + 1) (S + 1)).simpleGraphOn
          (ambientBlockOfFaceStarTree Tk :
            Set (RectangleEdge (R + 1) (S + 1)))).comap emb).Adj u v := by
      rw [ambientBlockOfFaceStarTree_comap Tk]
      exact huv
    exact (rectangleDual (R + 1) (S + 1)).simpleGraphOn_mono hBkU huvBlock
  have hKacyclic : K.IsAcyclic := by
    exact SimpleGraph.IsAcyclic.of_comap emb U.2.toSimpleGraph_isTree.isAcyclic
  letI : Nonempty {f // f ∈
      (boundedDualGraph (canonicalInteriorPrimal R S A i)).support} :=
    Tj.2.2.nonempty
  have hTjMax : Maximal SimpleGraph.IsAcyclic Tj.1 :=
    SimpleGraph.maximal_isAcyclic_iff_isTree.mpr Tj.2.2
  have hTkMax : Maximal SimpleGraph.IsAcyclic Tk.1 :=
    SimpleGraph.maximal_isAcyclic_iff_isTree.mpr Tk.2.2
  have hTjEq : Tj.1 = K :=
    le_antisymm hTjK (hTjMax.le_of_ge hKacyclic hTjK)
  have hTkEq : Tk.1 = K :=
    le_antisymm hTkK (hTkMax.le_of_ge hKacyclic hTkK)
  have hTrees : Tj = Tk := Subtype.ext (hTjEq.trans hTkEq.symm)
  apply hjk
  exact (Fintype.equivFin (InteriorFaceStarTree R S A i)).symm.injective hTrees

/-! ## The external Tapp input -/

/-- The precise graph-level consequence of Tapp's theorem used here.

It applies to an arbitrary finite connected graph embedded in the natural
square lattice and to an explicitly exhibited finite family of complete unit
squares.  In particular, it does not mention vacancy components, deletion
probabilities, or the target `exponentialMultiplicity` field. -/
def TappSquareFamilyLowerBound (κ : ℝ) : Prop :=
  ∀ {V : Type} [Fintype V]
    (H : SimpleGraph V) (coord : V ↪ Boundary.LatticePoint)
    (squares : Finset Boundary.LatticePoint),
    H ≤ Boundary.faceLattice.comap coord →
    H.Connected →
    (∀ z ∈ squares, ContainsUnitSquare H coord z) →
    Real.exp (κ * squares.card) ≤ treeCount H

@[simp] theorem card_interiorSquareStarts
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    (interiorSquareStarts R S A i).card =
      (Boundary.canonicalInterior R S A i).card := by
  classical
  rw [interiorSquareStarts, Finset.card_image_iff.mpr]
  · exact card_canonicalInteriorPrimal_eq R S A i
  · exact faceSquareStart_injectiveOn fun p hp =>
      ⟨(canonicalInteriorPrimal_bounds hp).1,
        (canonicalInteriorPrimal_bounds hp).2.2.1⟩

/-! ## Multiplicity and the remaining planar interface -/

/-- Tapp's graph-level bound gives the required number of face-star spanning
trees after the proved square injection and connectivity reductions. -/
theorem interiorFaceStarTree_multiplicity_of_tapp
    {κ : ℝ} (hTapp : TappSquareFamilyLowerBound κ)
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    Real.exp (κ * (Boundary.canonicalInterior R S A i).card) ≤
      interiorFaceStarTreeCount R S A i := by
  have h := hTapp (interiorFaceStarGraph R S A i)
    (boundedDualCoreCoord (canonicalInteriorPrimal R S A i))
    (interiorSquareStarts R S A i)
    (boundedDualCore_le_faceLattice _)
    (interiorFaceStarGraph_connected R S A i)
    (fun z hz => interiorSquareStarts_complete i hz)
  rw [card_interiorSquareStarts,
    ← interiorFaceStarTreeCount_eq_treeCount] at h
  exact h

/-- The primal graph remaining after deletion of one canonical interior
component.  Its connectivity is independent of planar tree duality. -/
def InteriorDeletionConnected
    (A : Finset Point) (R S : ℕ)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) : Prop :=
  (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
    Boundary.canonicalInterior R S A i)).Connected

/-- Natural-coordinate vertices left after deleting one canonical interior
component. -/
noncomputable def interiorDeletionNaturalVertices
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    Finset Boundary.LatticePoint :=
  Boundary.grid R S \ Boundary.interiorComponent R S
    (Boundary.canonicalVacancies R S A)
    ((Boundary.canonicalInteriorEquiv R S A).symm i)

noncomputable abbrev InteriorDeletionNaturalVertex
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :=
  ↑(interiorDeletionNaturalVertices R S A i)

/-- Square-lattice graph on the natural-coordinate deletion vertices. -/
noncomputable def interiorDeletionNaturalGraph
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    SimpleGraph (InteriorDeletionNaturalVertex R S A i) :=
  Boundary.faceLattice.comap fun z => z.1

theorem encodedOccupiedCore_subset_interiorDeletion
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    Boundary.encodedOccupiedCore R S A ⊆
      interiorDeletionNaturalVertices R S A i := by
  intro z hz
  have hzCore := Boundary.mem_encodedOccupiedCore.mp hz
  apply Finset.mem_sdiff.mpr
  refine ⟨Boundary.mem_grid.mpr ⟨hzCore.1, hzCore.2.1⟩, ?_⟩
  intro hzC
  have hzI : z ∈ Boundary.interiorVacancies R S
      (Boundary.canonicalVacancies R S A) :=
    Boundary.interiorComponent_subset_interiorVacancies R S _ _ hzC
  have hzV : z ∈ Boundary.canonicalVacancies R S A :=
    Boundary.interiorVacancies_subset R S _ hzI
  exact (Boundary.mem_encodedVacancies.mp hzV).2.2 hzCore.2.2

/-- Inclusion of the genuinely occupied core into the deletion graph. -/
noncomputable def coreToInteriorDeletion
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    Boundary.EncodedCoreVertex R S A →
      InteriorDeletionNaturalVertex R S A i :=
  fun z => ⟨z.1, encodedOccupiedCore_subset_interiorDeletion R S A i z.2⟩

private theorem neighbor_mem_interiorDeletion
    {R S : ℕ} {A : Finset Point}
    {i : Fin (Boundary.canonicalInteriorCount R S A)}
    (p : InteriorDeletionNaturalVertex R S A i)
    (hpCore : p.1 ∉ Boundary.encodedOccupiedCore R S A)
    {u : Boundary.LatticePoint} (huGrid : u ∈ Boundary.grid R S)
    (hpu : Boundary.KingAdjacent p.1 u) :
    u ∈ interiorDeletionNaturalVertices R S A i := by
  classical
  let V := Boundary.canonicalVacancies R S A
  let c := (Boundary.canonicalInteriorEquiv R S A).symm i
  have hpD := Finset.mem_sdiff.mp p.2
  have hpBounds := Boundary.mem_grid.mp hpD.1
  have hpNotA : Boundary.ofNatPoint p.1 ∉ A := by
    intro hpA
    exact hpCore (Boundary.mem_encodedOccupiedCore.mpr
      ⟨hpBounds.1, hpBounds.2, hpA⟩)
  have hpV : p.1 ∈ V :=
    Boundary.mem_encodedVacancies.mpr
      ⟨hpBounds.1, hpBounds.2, hpNotA⟩
  apply Finset.mem_sdiff.mpr
  refine ⟨huGrid, ?_⟩
  intro huC
  have huV : u ∈ V :=
    Boundary.interiorVacancies_subset R S _
      (Boundary.interiorComponent_subset_interiorVacancies R S V c huC)
  have hpClass : (Boundary.kingGraph V).connectedComponentMk ⟨p.1, hpV⟩ = c.1 := by
    have huClass := (Boundary.mem_interiorComponent.mp huC).2
    have hadj : (Boundary.kingGraph V).Adj ⟨p.1, hpV⟩ ⟨u, huV⟩ :=
      (Boundary.kingGraph_adj_iff _ _).mpr hpu
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans huClass
  exact hpD.2 (Boundary.mem_interiorComponent.mpr ⟨hpV, hpClass⟩)

private theorem interiorDeletion_reaches_core_target
    {R S : ℕ} {A : Finset Point}
    {i : Fin (Boundary.canonicalInteriorCount R S A)}
    (p : InteriorDeletionNaturalVertex R S A i)
    (q : Boundary.EncodedCoreVertex R S A)
    (hy : p.1.2 = q.1.2)
    (hpCore : p.1 ∉ Boundary.encodedOccupiedCore R S A) :
    ∃ c : Boundary.EncodedCoreVertex R S A,
      (interiorDeletionNaturalGraph R S A i).Reachable p
        (coreToInteriorDeletion R S A i c) := by
  induction hd : Nat.dist p.1.1 q.1.1 using Nat.strong_induction_on generalizing p with
  | h d ih =>
      have hpqX : p.1.1 ≠ q.1.1 := by
        intro heq
        apply hpCore
        have hpq : p.1 = q.1 := Prod.ext heq hy
        exact hpq.symm ▸ q.2
      rcases lt_or_gt_of_ne hpqX with hright | hleft
      · let uv : Boundary.LatticePoint := (p.1.1 + 1, p.1.2)
        have hpGrid := Boundary.mem_grid.mp (Finset.mem_sdiff.mp p.2).1
        have hqGrid := Boundary.mem_grid.mp
          (Boundary.encodedOccupiedCore_subset_boundaryOccupied R S A q.2 |>
            Finset.mem_sdiff.mp |>.1)
        have huGrid : uv ∈ Boundary.grid R S := by
          apply Boundary.mem_grid.mpr
          exact ⟨by dsimp [uv]; omega, by simpa [uv] using hpGrid.2⟩
        have hking : Boundary.KingAdjacent p.1 uv := by
          refine ⟨?_, ?_, ?_⟩
          · intro heq
            have := congrArg Prod.fst heq
            simp [uv] at this
          · simp [uv, Nat.dist]
          · simp [uv, Nat.dist]
        have huD := neighbor_mem_interiorDeletion p hpCore huGrid hking
        let u : InteriorDeletionNaturalVertex R S A i := ⟨uv, huD⟩
        have hpu : (interiorDeletionNaturalGraph R S A i).Adj p u := by
          change Boundary.natManhattanDist p.1 u.1 = 1
          simp [u, uv, Boundary.natManhattanDist, Nat.dist]
        by_cases huCore : uv ∈ Boundary.encodedOccupiedCore R S A
        · let c : Boundary.EncodedCoreVertex R S A := ⟨uv, huCore⟩
          refine ⟨c, hpu.reachable.trans ?_⟩
          have huc : u = coreToInteriorDeletion R S A i c := by
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

      · let uv : Boundary.LatticePoint := (p.1.1 - 1, p.1.2)
        have hpGrid := Boundary.mem_grid.mp (Finset.mem_sdiff.mp p.2).1
        have huGrid : uv ∈ Boundary.grid R S := by
          apply Boundary.mem_grid.mpr
          exact ⟨by dsimp [uv]; omega, by simpa [uv] using hpGrid.2⟩
        have hking : Boundary.KingAdjacent p.1 uv := by
          have hpPos : 0 < p.1.1 := by omega
          refine ⟨?_, ?_, ?_⟩
          · intro heq
            have := congrArg Prod.fst heq
            simp [uv] at this
            omega
          · simp [uv, Nat.dist]
            omega
          · simp [uv, Nat.dist]
        have huD := neighbor_mem_interiorDeletion p hpCore huGrid hking
        let u : InteriorDeletionNaturalVertex R S A i := ⟨uv, huD⟩
        have hpu : (interiorDeletionNaturalGraph R S A i).Adj p u := by
          change Boundary.natManhattanDist p.1 u.1 = 1
          simp [u, uv, Boundary.natManhattanDist, Nat.dist]
          omega
        by_cases huCore : uv ∈ Boundary.encodedOccupiedCore R S A
        · let c : Boundary.EncodedCoreVertex R S A := ⟨uv, huCore⟩
          refine ⟨c, hpu.reachable.trans ?_⟩
          have huc : u = coreToInteriorDeletion R S A i c := by
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

/-- Every natural-coordinate vertex left by the deletion can reach a genuinely
occupied core vertex.  The proof follows a row toward an occupied point; a
first step into the deleted king component would force the starting point
into that same component. -/
theorem interiorDeletionNatural_reaches_core
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (i : Fin (Boundary.canonicalInteriorCount R S A))
    (p : InteriorDeletionNaturalVertex R S A i) :
    ∃ c : Boundary.EncodedCoreVertex R S A,
      (interiorDeletionNaturalGraph R S A i).Reachable p
        (coreToInteriorDeletion R S A i c) := by
  classical
  by_cases hpCore : p.1 ∈ Boundary.encodedOccupiedCore R S A
  · let c : Boundary.EncodedCoreVertex R S A := ⟨p.1, hpCore⟩
    refine ⟨c, ?_⟩
    have hpc : p = coreToInteriorDeletion R S A i c := by
      apply Subtype.ext
      rfl
    rw [hpc]
  · have hpGrid := Boundary.mem_grid.mp (Finset.mem_sdiff.mp p.2).1
    rcases Boundary.exists_occupied_in_row hHull hconn hpGrid.2 with
      ⟨x, hxR, hxA⟩
    have hqCore : (x, p.1.2) ∈ Boundary.encodedOccupiedCore R S A :=
      Boundary.mem_encodedOccupiedCore.mpr ⟨hxR, hpGrid.2, hxA⟩
    let q : Boundary.EncodedCoreVertex R S A := ⟨(x, p.1.2), hqCore⟩
    exact interiorDeletion_reaches_core_target p q rfl hpCore

/-- The occupied-core inclusion is a graph homomorphism into the natural
deletion graph. -/
noncomputable def coreToInteriorDeletionHom
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    (Boundary.faceLattice.comap
      (fun z : Boundary.EncodedCoreVertex R S A => z.1)) →g
      interiorDeletionNaturalGraph R S A i where
  toFun := coreToInteriorDeletion R S A i
  map_rel' := by
    intro p q hpq
    exact hpq

/-- The natural-coordinate graph remaining after one interior component is
deleted is connected. -/
theorem interiorDeletionNaturalGraph_connected
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    (interiorDeletionNaturalGraph R S A i).Connected := by
  have hcore := Boundary.encodedOccupiedCore_connected hHull hconn
  letI : Nonempty (InteriorDeletionNaturalVertex R S A i) :=
    hcore.nonempty.map (coreToInteriorDeletion R S A i)
  refine { preconnected := ?_ }
  intro p q
  rcases interiorDeletionNatural_reaches_core hHull hconn i p with ⟨cp, hp⟩
  rcases interiorDeletionNatural_reaches_core hHull hconn i q with ⟨cq, hq⟩
  have hmiddle : (interiorDeletionNaturalGraph R S A i).Reachable
      (coreToInteriorDeletion R S A i cp)
      (coreToInteriorDeletion R S A i cq) :=
    (hcore cp cq).map (coreToInteriorDeletionHom R S A i)
  exact hp.trans (hmiddle.trans hq.symm)

/-- Natural and integer coordinates give equivalent vertex types after
deleting the selected canonical interior component. -/
noncomputable def interiorDeletionNaturalEquiv
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    InteriorDeletionNaturalVertex R S A i ≃
      {p // p ∈ rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i} where
  toFun z := by
    have hz := Finset.mem_sdiff.mp z.2
    refine ⟨Boundary.ofNatPoint z.1, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
    · exact Boundary.ofNatPoint_mem_standardRectangle.mpr
        (Boundary.mem_grid.mp hz.1)
    · intro hzImage
      rcases Finset.mem_image.mp hzImage with ⟨w, hw, hzw⟩
      have heq : z.1 = w := Boundary.ofNatPoint_injective hzw.symm
      exact hz.2 (heq ▸ hw)
  invFun p := by
    have hp := Finset.mem_sdiff.mp p.2
    have hpBounds :
        ((0 : ℤ) ≤ p.1.1 ∧ p.1.1 < (R + 1 : ℕ)) ∧
        ((0 : ℤ) ≤ p.1.2 ∧ p.1.2 < (S + 1 : ℕ)) := by
      simpa [rectangle] using hp.1
    let z : Boundary.LatticePoint := (p.1.1.toNat, p.1.2.toNat)
    have hzval : Boundary.ofNatPoint z = p.1 := by
      apply Prod.ext <;>
        simp [z, Boundary.ofNatPoint, hpBounds.1.1, hpBounds.2.1]
    have hzGrid : z ∈ Boundary.grid R S := by
      apply Boundary.mem_grid.mpr
      constructor <;> apply Int.toNat_le.mpr <;> omega
    refine ⟨z, Finset.mem_sdiff.mpr ⟨hzGrid, ?_⟩⟩
    intro hzComponent
    apply hp.2
    rw [← hzval]
    exact Finset.mem_image.mpr ⟨z, hzComponent, rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext <;> simp [Boundary.ofNatPoint]
  right_inv p := by
    apply Subtype.ext
    have hp := Finset.mem_sdiff.mp p.2
    have hpBounds :
        ((0 : ℤ) ≤ p.1.1 ∧ p.1.1 < (R + 1 : ℕ)) ∧
        ((0 : ℤ) ≤ p.1.2 ∧ p.1.2 < (S + 1 : ℕ)) := by
      simpa [rectangle] using hp.1
    apply Prod.ext <;>
      simp [Boundary.ofNatPoint, hpBounds.1.1, hpBounds.2.1]

/-- The coordinate equivalence preserves exactly the nearest-neighbour graph. -/
noncomputable def interiorDeletionNaturalGraphIso
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    interiorDeletionNaturalGraph R S A i ≃g
      inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i) where
  toEquiv := interiorDeletionNaturalEquiv R S A i
  map_rel_iff' := by
    intro z w
    change manhattanDist (Boundary.ofNatPoint z.1)
        (Boundary.ofNatPoint w.1) = 1 ↔
      Boundary.natManhattanDist z.1 w.1 = 1
    rw [Boundary.manhattanDist_ofNatPoint]

/-- Deleting any one canonical interior vacancy component leaves a connected
primal grid.  Thus deletion connectivity is not an external input. -/
theorem interiorDeletionConnected_of_hull
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    InteriorDeletionConnected A R S i := by
  exact (interiorDeletionNaturalGraphIso R S A i).connected_iff.mp
    (interiorDeletionNaturalGraph_connected hHull hconn i)

/-- The narrow planar duality residual for the interior event construction.
It equates finite tree counts, rather than assuming the probability ratio or
the final exponential estimate. -/
structure InteriorPlanarDualityInput
    (A : Finset Point) (R S : ℕ)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) : Prop where
  rectangleTreeCount :
    (rectangleDual (R + 1) (S + 1)).spanningTreeCount =
      tauRect (R + 1) (S + 1)
  containmentTreeCount :
    ∀ j : Fin (interiorFaceStarTreeCount R S A i),
      (rectangleDual (R + 1) (S + 1)).containmentCount
        (interiorEventBlock R S A i j) =
      tau (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i)

theorem isEdgeForest_iff_containmentCount_pos
    {V E : Type*} [Fintype V] [Fintype E]
    (G : LabeledMultigraph V E) (F : Finset E) :
    G.IsEdgeForest F ↔ 0 < G.containmentCount F := by
  constructor
  · exact G.containmentCount_pos_of_isEdgeForest
  · intro h
    classical
    rw [Multigraph.LabeledMultigraph.containmentCount, Finset.card_pos] at h
    rcases h with ⟨T, hT⟩
    exact ⟨T, (Finset.mem_filter.mp hT).2⟩

/-- The ambient rectangular dual has a spanning tree whenever an interior
component index exists; such an index supplies the required nondegenerate
side lengths. -/
theorem rectangleDual_spanningTreeCount_pos_of_interior
    (R S : ℕ) (A : Finset Point)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) :
    0 < (rectangleDual (R + 1) (S + 1)).spanningTreeCount := by
  obtain ⟨p⟩ := (canonicalInteriorPrimalKingGraph_connected R S A i).nonempty
  have hpBounds := canonicalInteriorPrimal_bounds p.2
  have hconn : (rectangleDual (R + 1) (S + 1)).Connected :=
    rectangleDual_connected (by omega) (by omega)
  obtain ⟨T, hT⟩ :=
    (rectangleDual (R + 1) (S + 1)).exists_isSpanningTree hconn
  exact (rectangleDual (R + 1) (S + 1)).spanningTreeCount_pos_iff.mpr
    ⟨T, hT⟩

/-- The planar count identities imply the exact common event ratio. -/
theorem InteriorPlanarDualityInput.eventRatio
    {A : Finset Point} {R S : ℕ}
    {i : Fin (Boundary.canonicalInteriorCount R S A)}
    (d : InteriorPlanarDualityInput A R S i)
    (j : Fin (interiorFaceStarTreeCount R S A i)) :
    (rectangleDual (R + 1) (S + 1)).containmentRatio
        (interiorEventBlock R S A i j) =
      (tau (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i) : ℝ) /
      (tauRect (R + 1) (S + 1) : ℝ) := by
  unfold Multigraph.LabeledMultigraph.containmentRatio
  rw [d.containmentTreeCount j, d.rectangleTreeCount]

/-- Construct the former bundled interior certificate from the proved
face-star/event algebra, Tapp's graph theorem, deletion connectivity, and the
separate planar tree-count identities. -/
noncomputable def canonicalInteriorEventCertificate_of_tapp
    {κ : ℝ} {A : Finset Point} {R S : ℕ}
    (i : Fin (Boundary.canonicalInteriorCount R S A))
    (hTapp : TappSquareFamilyLowerBound κ)
    (hDeletion : InteriorDeletionConnected A R S i)
    (hPlanar : InteriorPlanarDualityInput A R S i) :
    CanonicalInteriorEventCertificate κ A R S i where
  eventCount := interiorFaceStarTreeCount R S A i
  block := interiorEventBlock R S A i
  ambientPositive := rectangleDual_spanningTreeCount_pos_of_interior R S A i
  blockForest j := by
    apply (isEdgeForest_iff_containmentCount_pos
      (rectangleDual (R + 1) (S + 1)) _).mpr
    rw [hPlanar.containmentTreeCount j]
    exact (tau_pos_iff_connected _).mpr hDeletion
  incompatible := interiorEventBlock_incompatible R S A i
  eventRatio := hPlanar.eventRatio
  exponentialMultiplicity :=
    interiorFaceStarTree_multiplicity_of_tapp hTapp R S A i

end Dual
end SquareMaximality
