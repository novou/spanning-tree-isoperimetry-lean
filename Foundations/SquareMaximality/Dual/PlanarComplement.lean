module

public import SquareMaximality.Dual.BoundaryDeterminants
public import SquareMaximality.Multigraph.ContractionTrees
public import SquareMaximality.Boundary.Euler

@[expose] public section

set_option backward.privateInPublic true

/-!
# Explicit planar complement for rectangular grids

This file constructs the finite geometric data left abstract by
`Dual.BoundaryDeterminants`.  The development starts with the local facts
needed to identify the non-root components and the surviving labels of the
boundary contraction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SquareMaximality
namespace Dual

open Multigraph
open Multigraph.LabeledMultigraph

noncomputable section

/-- Every endpoint of a side label of a bounded face is one of that face's
four primal corners. -/
theorem finPoint_mem_faceCorners_of_primalIncident_faceSideEdge
    {R S : ℕ} (f : BoundedFace (R + 1) (S + 1)) (d : FaceSide)
    (p : Fin (R + 1) × Fin (S + 1))
    (hp : PrimalIncident p (faceSideEdge f d)) :
    finPoint p ∈ Boundary.faceCorners (f.1.1, f.2.1) := by
  rw [Boundary.mem_faceCorners]
  cases d with
  | south =>
      change p = horizontalPrimalLeft _ ∨ p = horizontalPrimalRight _ at hp
      rcases hp with rfl | rfl <;>
        simp [finPoint, horizontalPrimalLeft,
          horizontalPrimalRight]
  | north =>
      change p = horizontalPrimalLeft _ ∨ p = horizontalPrimalRight _ at hp
      rcases hp with rfl | rfl <;>
        simp [finPoint, horizontalPrimalLeft,
          horizontalPrimalRight]
  | west =>
      change p = verticalPrimalBottom _ ∨ p = verticalPrimalTop _ at hp
      rcases hp with rfl | rfl <;>
        simp [finPoint, verticalPrimalBottom,
          verticalPrimalTop]
  | east =>
      change p = verticalPrimalBottom _ ∨ p = verticalPrimalTop _ at hp
      rcases hp with rfl | rfl <;>
        simp [finPoint, verticalPrimalBottom,
          verticalPrimalTop]

/-- If two bounded dual faces share a label and a primal vertex is a corner
of both faces, that label is incident with the primal vertex. -/
theorem primalIncident_of_rectangleDual_isLink_some_some_of_mem_corners
    {R S : ℕ} (p : Fin (R + 1) × Fin (S + 1))
    (f g : BoundedFace (R + 1) (S + 1))
    (e : RectangleEdge (R + 1) (S + 1))
    (he : (rectangleDual (R + 1) (S + 1)).IsLink e (some f) (some g))
    (hpf : finPoint p ∈ Boundary.faceCorners (f.1.1, f.2.1))
    (hpg : finPoint p ∈ Boundary.faceCorners (g.1.1, g.2.1)) :
    PrimalIncident p e := by
  simp only [Boundary.mem_faceCorners, finPoint] at hpf hpg
  cases e with
  | horizontal e =>
      rw [rectangleDual_horizontal_isLink_some_some_iff] at he
      change p = horizontalPrimalLeft e ∨ p = horizontalPrimalRight e
      rcases he with h | h
      · by_cases hx : p.1.1 = e.x.1
        · left
          apply Prod.ext <;> apply Fin.ext
          · exact hx
          · simp only [horizontalPrimalLeft]
            have hex := congrArg Fin.val h.1
            omega
        · right
          apply Prod.ext <;> apply Fin.ext
          · simp only [horizontalPrimalRight]
            have hex := congrArg Fin.val h.1
            omega
          · simp only [horizontalPrimalRight]
            omega
      · by_cases hx : p.1.1 = e.x.1
        · left
          apply Prod.ext <;> apply Fin.ext
          · exact hx
          · simp only [horizontalPrimalLeft]
            omega
        · right
          apply Prod.ext <;> apply Fin.ext
          · simp only [horizontalPrimalRight]
            have hex := congrArg Fin.val h.1
            omega
          · simp only [horizontalPrimalRight]
            omega
  | vertical e =>
      rw [rectangleDual_vertical_isLink_some_some_iff] at he
      change p = verticalPrimalBottom e ∨ p = verticalPrimalTop e
      rcases he with h | h
      · by_cases hy : p.2.1 = e.y.1
        · left
          apply Prod.ext <;> apply Fin.ext
          · simp only [verticalPrimalBottom]
            omega
          · exact hy
        · right
          apply Prod.ext <;> apply Fin.ext
          · simp only [verticalPrimalTop]
            omega
          · simp only [verticalPrimalTop]
            have hey := congrArg Fin.val h.1
            omega
      · by_cases hy : p.2.1 = e.y.1
        · left
          apply Prod.ext <;> apply Fin.ext
          · simp only [verticalPrimalBottom]
            omega
          · exact hy
        · right
          apply Prod.ext <;> apply Fin.ext
          · simp only [verticalPrimalTop]
            omega
          · simp only [verticalPrimalTop]
            have hey := congrArg Fin.val h.1
            omega

/-- Two bounded faces at Manhattan distance one and sharing a selected
primal corner are adjacent in the selected dual graph. -/
theorem dualEdgeGraph_adj_some_some_of_shared_selected_corner
    {R S : ℕ} {X : Finset (Fin (R + 1) × Fin (S + 1))}
    (p : Fin (R + 1) × Fin (S + 1)) (hpX : p ∈ X)
    (f g : BoundedFace (R + 1) (S + 1))
    (hpf : finPoint p ∈ Boundary.faceCorners (f.1.1, f.2.1))
    (hpg : finPoint p ∈ Boundary.faceCorners (g.1.1, g.2.1))
    (hfg : Boundary.natManhattanDist (f.1.1, f.2.1)
      (g.1.1, g.2.1) = 1) :
    (dualEdgeGraph X).Adj (some f) (some g) := by
  rcases (rectangleDual_exists_isLink_some_some_iff f g).2 hfg with ⟨e, he⟩
  rw [dualEdgeGraph_adj_iff]
  refine ⟨?_, e, ?_, he⟩
  · intro h
    have hface : f = g := Option.some_injective _ h
    subst g
    simp [Boundary.natManhattanDist] at hfg
  · exact mem_vacancyDualEdges.mpr
      ⟨p, hpX,
        primalIncident_of_rectangleDual_isLink_some_some_of_mem_corners
          p f g e he hpf hpg⟩

/-- All bounded dual faces having the same selected primal corner lie in one
selected-label component. -/
theorem dualEdgeGraph_reachable_some_some_of_shared_selected_corner
    {R S : ℕ} {X : Finset (Fin (R + 1) × Fin (S + 1))}
    (p : Fin (R + 1) × Fin (S + 1)) (hpX : p ∈ X)
    (f g : BoundedFace (R + 1) (S + 1))
    (hpf : finPoint p ∈ Boundary.faceCorners (f.1.1, f.2.1))
    (hpg : finPoint p ∈ Boundary.faceCorners (g.1.1, g.2.1)) :
    (dualEdgeGraph X).Reachable (some f) (some g) := by
  have hpf' := (Boundary.mem_faceCorners.mp hpf)
  have hpg' := (Boundary.mem_faceCorners.mp hpg)
  by_cases hx : f.1.1 = g.1.1
  · by_cases hy : f.2.1 = g.2.1
    · have hface : f = g := by
        apply Prod.ext <;> apply Fin.ext
        · exact hx
        · exact hy
      subst g
      rfl
    · have hdist : Boundary.natManhattanDist (f.1.1, f.2.1)
          (g.1.1, g.2.1) = 1 := by
        unfold Boundary.natManhattanDist Nat.dist
        omega
      exact (dualEdgeGraph_adj_some_some_of_shared_selected_corner
        p hpX f g hpf hpg hdist).reachable
  · by_cases hy : f.2.1 = g.2.1
    · have hdist : Boundary.natManhattanDist (f.1.1, f.2.1)
          (g.1.1, g.2.1) = 1 := by
        unfold Boundary.natManhattanDist Nat.dist
        omega
      exact (dualEdgeGraph_adj_some_some_of_shared_selected_corner
        p hpX f g hpf hpg hdist).reachable
    · let m : BoundedFace (R + 1) (S + 1) := (f.1, g.2)
      have hpm : finPoint p ∈ Boundary.faceCorners (m.1.1, m.2.1) := by
        rw [Boundary.mem_faceCorners]
        exact ⟨hpf'.1, hpf'.2.1, hpg'.2.2.1, hpg'.2.2.2⟩
      have hfm : Boundary.natManhattanDist (f.1.1, f.2.1)
          (m.1.1, m.2.1) = 1 := by
        unfold Boundary.natManhattanDist Nat.dist
        simp only [m]
        omega
      have hmg : Boundary.natManhattanDist (m.1.1, m.2.1)
          (g.1.1, g.2.1) = 1 := by
        unfold Boundary.natManhattanDist Nat.dist
        simp only [m]
        omega
      exact (dualEdgeGraph_adj_some_some_of_shared_selected_corner
        p hpX f m hpf hpm hfm).reachable.trans
          (dualEdgeGraph_adj_some_some_of_shared_selected_corner
            p hpX m g hpm hpg hmg).reachable

/-- Lower-left face coordinate of a unit interval containing two grid
coordinates at distance at most one. -/
def sharedFaceCoordinate (N : ℕ) (hN : 0 < N) (x y : ℕ)
    (hx : x ≤ N) (hy : y ≤ N) : Fin N :=
  if htop : min x y = N then
    ⟨N - 1, by omega⟩
  else
    ⟨min x y, by omega⟩

theorem sharedFaceCoordinate_bounds
    (N : ℕ) (hN : 0 < N) (x y : ℕ)
    (hx : x ≤ N) (hy : y ≤ N) (hxy : Nat.dist x y ≤ 1) :
    let a := sharedFaceCoordinate N hN x y hx hy
    a.1 ≤ x ∧ x ≤ a.1 + 1 ∧ a.1 ≤ y ∧ y ≤ a.1 + 1 := by
  dsimp only
  rcases le_total x y with hle | hle
  · rw [Nat.dist_eq_sub_of_le hle] at hxy
    simp only [sharedFaceCoordinate, Nat.min_eq_left hle]
    split <;> simp_all <;> omega
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hle] at hxy
    simp only [sharedFaceCoordinate, Nat.min_eq_right hle]
    split <;> simp_all <;> omega

/-- King-adjacent grid vertices are corners of a common bounded unit face
when both face dimensions are nonzero. -/
theorem exists_boundedFace_shared_corner_of_kingAdjacent
    {R S : ℕ} (hR : 0 < R) (hS : 0 < S)
    (p q : Fin (R + 1) × Fin (S + 1))
    (hpq : Boundary.KingAdjacent (finPoint p) (finPoint q)) :
    ∃ f : BoundedFace (R + 1) (S + 1),
      finPoint p ∈ Boundary.faceCorners (f.1.1, f.2.1) ∧
      finPoint q ∈ Boundary.faceCorners (f.1.1, f.2.1) := by
  have hpX : p.1.1 ≤ R := by have := p.1.2; omega
  have hqX : q.1.1 ≤ R := by have := q.1.2; omega
  have hpY : p.2.1 ≤ S := by have := p.2.2; omega
  have hqY : q.2.1 ≤ S := by have := q.2.2; omega
  let fx := sharedFaceCoordinate R hR p.1.1 q.1.1 hpX hqX
  let fy := sharedFaceCoordinate S hS p.2.1 q.2.1 hpY hqY
  let f : BoundedFace (R + 1) (S + 1) :=
    (⟨fx.1, by have := fx.2; omega⟩,
      ⟨fy.1, by have := fy.2; omega⟩)
  have hxBounds := sharedFaceCoordinate_bounds R hR p.1.1 q.1.1
    hpX hqX hpq.2.1
  have hyBounds := sharedFaceCoordinate_bounds S hS p.2.1 q.2.1
    hpY hqY hpq.2.2
  refine ⟨f, ?_, ?_⟩
  · rw [Boundary.mem_faceCorners]
    exact ⟨hxBounds.1, hxBounds.2.1, hyBounds.1, hyBounds.2.1⟩
  · rw [Boundary.mem_faceCorners]
    exact ⟨hxBounds.2.2.1, hxBounds.2.2.2,
      hyBounds.2.2.1, hyBounds.2.2.2⟩

/-- A bounded face having a selected perimeter corner is joined to the
exterior by a selected dual label. -/
theorem dualEdgeGraph_adj_some_none_of_selected_perimeter_corner
    {R S : ℕ} {X : Finset (Fin (R + 1) × Fin (S + 1))}
    (p : Fin (R + 1) × Fin (S + 1)) (hpX : p ∈ X)
    (f : BoundedFace (R + 1) (S + 1))
    (hpf : finPoint p ∈ Boundary.faceCorners (f.1.1, f.2.1))
    (hpPerim : Boundary.IsPerimeter R S (finPoint p)) :
    (dualEdgeGraph X).Adj (some f) none := by
  have hpBounds := Boundary.mem_faceCorners.mp hpf
  simp only [finPoint] at hpBounds
  rw [dualEdgeGraph_adj_iff]
  refine ⟨by simp, ?_⟩
  simp only [Boundary.IsPerimeter, finPoint] at hpPerim
  rcases hpPerim with hy0 | hyrest
  · let e := faceSideEdge f FaceSide.west
    refine ⟨e, mem_vacancyDualEdges.mpr ⟨p, hpX, ?_⟩, ?_⟩
    · change p = verticalPrimalBottom _ ∨ p = verticalPrimalTop _
      by_cases hy : p.2.1 = f.2.1
      · left
        apply Prod.ext <;> apply Fin.ext
        · simp only [verticalPrimalBottom]
          omega
        · exact hy
      · right
        apply Prod.ext <;> apply Fin.ext
        · simp only [verticalPrimalTop]
          omega
        · simp only [verticalPrimalTop]
          omega
    · change (rectangleDual (R + 1) (S + 1)).ends e = s(some f, none)
      have hfx0 : f.1.1 = 0 := by omega
      have hR : 0 < R := by have := f.1.2; omega
      simp [e, faceSideEdge, rectangleDual, verticalLeft, verticalRight,
        hfx0, hR]
      apply Prod.ext
      · apply Fin.ext
        exact hfx0.symm
      · rfl
  · rcases hyrest with hxR | hyrest
    · let e := faceSideEdge f FaceSide.east
      refine ⟨e, mem_vacancyDualEdges.mpr ⟨p, hpX, ?_⟩, ?_⟩
      · change p = verticalPrimalBottom _ ∨ p = verticalPrimalTop _
        by_cases hy : p.2.1 = f.2.1
        · left
          apply Prod.ext <;> apply Fin.ext
          · simp only [verticalPrimalBottom]
            omega
          · exact hy
        · right
          apply Prod.ext <;> apply Fin.ext
          · simp only [verticalPrimalTop]
            omega
          · simp only [verticalPrimalTop]
            omega
      · change (rectangleDual (R + 1) (S + 1)).ends e = s(some f, none)
        simp [e, faceSideEdge, rectangleDual, verticalLeft, verticalRight]
        omega
    · rcases hyrest with hy0 | hyS
      · let e := faceSideEdge f FaceSide.south
        refine ⟨e, mem_vacancyDualEdges.mpr ⟨p, hpX, ?_⟩, ?_⟩
        · change p = horizontalPrimalLeft _ ∨ p = horizontalPrimalRight _
          by_cases hx : p.1.1 = f.1.1
          · left
            apply Prod.ext <;> apply Fin.ext
            · exact hx
            · simp only [horizontalPrimalLeft]
              omega
          · right
            apply Prod.ext <;> apply Fin.ext
            · simp only [horizontalPrimalRight]
              omega
            · simp only [horizontalPrimalRight]
              omega
        · change (rectangleDual (R + 1) (S + 1)).ends e = s(some f, none)
          have hfy0 : f.2.1 = 0 := by omega
          have hS : 0 < S := by have := f.2.2; omega
          simp [e, faceSideEdge, rectangleDual, horizontalBelow,
            horizontalAbove, hfy0, hS]
          apply Prod.ext
          · rfl
          · apply Fin.ext
            exact hfy0.symm
      · let e := faceSideEdge f FaceSide.north
        refine ⟨e, mem_vacancyDualEdges.mpr ⟨p, hpX, ?_⟩, ?_⟩
        · change p = horizontalPrimalLeft _ ∨ p = horizontalPrimalRight _
          by_cases hx : p.1.1 = f.1.1
          · left
            apply Prod.ext <;> apply Fin.ext
            · exact hx
            · simp only [horizontalPrimalLeft]
              omega
          · right
            apply Prod.ext <;> apply Fin.ext
            · simp only [horizontalPrimalRight]
              omega
            · simp only [horizontalPrimalRight]
              omega
        · change (rectangleDual (R + 1) (S + 1)).ends e = s(some f, none)
          simp [e, faceSideEdge, rectangleDual, horizontalBelow,
            horizontalAbove]
          omega

/-! ## Wiring boundary-attached vacancy components -/

/-- A king walk ending on the perimeter lifts to the induced graph on the
boundary-attached vacancies. -/
theorem kingWalk_lifts_to_boundaryVacancies
    {R S : ℕ} {V : Finset Boundary.LatticePoint}
    {p q : {z // z ∈ V}} (w : (Boundary.kingGraph V).Walk p q)
    (hq : Boundary.IsPerimeter R S q.1) :
    ∃ hpB : p.1 ∈ Boundary.boundaryVacancies R S V,
      ∃ hqB : q.1 ∈ Boundary.boundaryVacancies R S V,
        (Boundary.kingGraph (Boundary.boundaryVacancies R S V)).Reachable
          ⟨p.1, hpB⟩ ⟨q.1, hqB⟩ := by
  induction w with
  | @nil u =>
      have huAttached := Boundary.isBoundaryAttached_of_perimeter u.2 hq
      let huB := Boundary.mem_boundaryVacancies.mpr huAttached
      exact ⟨huB, huB, SimpleGraph.Reachable.refl _⟩
  | @cons p v q hpv w ih =>
      rcases ih hq with ⟨hvB, hqB, hvq⟩
      have hpAttached : Boundary.IsBoundaryAttached R S V p.1 :=
        ⟨p.2, q, hq, (SimpleGraph.Walk.cons hpv w).reachable⟩
      let hpB := Boundary.mem_boundaryVacancies.mpr hpAttached
      have hpvB :
          (Boundary.kingGraph (Boundary.boundaryVacancies R S V)).Adj
            (⟨p.1, hpB⟩ : {z // z ∈ Boundary.boundaryVacancies R S V})
            ⟨v.1, hvB⟩ := by
        apply (Boundary.kingGraph_adj_iff _ _).mpr
        exact (Boundary.kingGraph_adj_iff p v).mp hpv
      exact ⟨hpB, hqB, hpvB.reachable.trans hvq⟩

/-- Every boundary-attached vacancy reaches a perimeter vacancy within the
king graph induced by the boundary-attached set itself. -/
theorem boundaryVacancy_reachable_perimeter
    {R S : ℕ} {V : Finset Boundary.LatticePoint}
    (p : {z // z ∈ Boundary.boundaryVacancies R S V}) :
    ∃ q : {z // z ∈ Boundary.boundaryVacancies R S V},
      Boundary.IsPerimeter R S q.1 ∧
        (Boundary.kingGraph (Boundary.boundaryVacancies R S V)).Reachable p q := by
  rcases Boundary.mem_boundaryVacancies.mp p.2 with ⟨hpV, q, hqPerim, hpq⟩
  rcases hpq with ⟨w⟩
  rcases kingWalk_lifts_to_boundaryVacancies w hqPerim with
    ⟨hpB, hqB, hpqB⟩
  let p' : {z // z ∈ Boundary.boundaryVacancies R S V} := ⟨p.1, hpB⟩
  let q' : {z // z ∈ Boundary.boundaryVacancies R S V} := ⟨q.1, hqB⟩
  have hpp' : p = p' := Subtype.ext rfl
  exact ⟨q', hqPerim, hpp'.symm ▸ hpqB⟩

/-- Convert one canonical boundary vacancy to its explicit rectangular
primal vertex. -/
def canonicalBoundaryVacancyPrimal (R S : ℕ) (A : Finset Point)
    (z : {z // z ∈ canonicalBoundaryNaturalVacancies R S A}) :
    Fin (R + 1) × Fin (S + 1) :=
  (finGridEquiv R S).symm ⟨z.1,
    (Boundary.boundaryVacancies_subset R S _ z.2 |> fun hz =>
      encodedVacancies_subset_grid R S A hz)⟩

@[simp] theorem finPoint_canonicalBoundaryVacancyPrimal
    (R S : ℕ) (A : Finset Point)
    (z : {z // z ∈ canonicalBoundaryNaturalVacancies R S A}) :
    finPoint (canonicalBoundaryVacancyPrimal R S A z) = z.1 := by
  exact finPoint_finGridEquiv_symm R S _

theorem canonicalBoundaryVacancyPrimal_mem
    (R S : ℕ) (A : Finset Point)
    (z : {z // z ∈ canonicalBoundaryNaturalVacancies R S A}) :
    canonicalBoundaryVacancyPrimal R S A z ∈
      canonicalBoundaryPrimal R S A := by
  rw [mem_canonicalBoundaryPrimal,
    finPoint_canonicalBoundaryVacancyPrimal]
  exact z.2

/-- A deterministic bounded face having a given grid vertex as a corner. -/
def boundaryFaceAnchor {R S : ℕ} (hR : 0 < R) (hS : 0 < S)
    (p : Fin (R + 1) × Fin (S + 1)) :
    BoundedFace (R + 1) (S + 1) :=
  let hx : p.1.1 ≤ R := by have := p.1.2; omega
  let hy : p.2.1 ≤ S := by have := p.2.2; omega
  (⟨(sharedFaceCoordinate R hR p.1.1 p.1.1 hx hx).1, by
      have := (sharedFaceCoordinate R hR p.1.1 p.1.1 hx hx).2
      omega⟩,
   ⟨(sharedFaceCoordinate S hS p.2.1 p.2.1 hy hy).1, by
      have := (sharedFaceCoordinate S hS p.2.1 p.2.1 hy hy).2
      omega⟩)

theorem finPoint_mem_faceCorners_boundaryFaceAnchor
    {R S : ℕ} (hR : 0 < R) (hS : 0 < S)
    (p : Fin (R + 1) × Fin (S + 1)) :
    finPoint p ∈ Boundary.faceCorners
      ((boundaryFaceAnchor hR hS p).1.1,
        (boundaryFaceAnchor hR hS p).2.1) := by
  have hx : p.1.1 ≤ R := by have := p.1.2; omega
  have hy : p.2.1 ≤ S := by have := p.2.2; omega
  have hxBounds := sharedFaceCoordinate_bounds R hR p.1.1 p.1.1
    hx hx (by simp)
  have hyBounds := sharedFaceCoordinate_bounds S hS p.2.1 p.2.1
    hy hy (by simp)
  rw [Boundary.mem_faceCorners]
  exact ⟨hxBounds.1, hxBounds.2.1, hyBounds.1, hyBounds.2.1⟩

/-- King-adjacent canonical boundary vacancies have mutually reachable
bounded-face anchors in the selected dual graph. -/
theorem canonicalBoundaryFaceAnchor_reachable_of_kingAdjacent
    {R S : ℕ} (hR : 0 < R) (hS : 0 < S) (A : Finset Point)
    (p q : {z // z ∈ canonicalBoundaryNaturalVacancies R S A})
    (hpq : Boundary.KingAdjacent p.1 q.1) :
    (dualEdgeGraph (canonicalBoundaryPrimal R S A)).Reachable
      (some (boundaryFaceAnchor hR hS
        (canonicalBoundaryVacancyPrimal R S A p)))
      (some (boundaryFaceAnchor hR hS
        (canonicalBoundaryVacancyPrimal R S A q))) := by
  let pp := canonicalBoundaryVacancyPrimal R S A p
  let qq := canonicalBoundaryVacancyPrimal R S A q
  have hpqFin : Boundary.KingAdjacent (finPoint pp) (finPoint qq) := by
    simpa [pp, qq] using hpq
  rcases exists_boundedFace_shared_corner_of_kingAdjacent hR hS pp qq hpqFin with
    ⟨f, hpf, hqf⟩
  have hpAnchor := finPoint_mem_faceCorners_boundaryFaceAnchor hR hS pp
  have hqAnchor := finPoint_mem_faceCorners_boundaryFaceAnchor hR hS qq
  have hpReach := dualEdgeGraph_reachable_some_some_of_shared_selected_corner
    pp (canonicalBoundaryVacancyPrimal_mem R S A p)
      (boundaryFaceAnchor hR hS pp) f hpAnchor hpf
  have hqReach := dualEdgeGraph_reachable_some_some_of_shared_selected_corner
    qq (canonicalBoundaryVacancyPrimal_mem R S A q)
      (boundaryFaceAnchor hR hS qq) f hqAnchor hqf
  exact hpReach.trans hqReach.symm

/-- King reachability of canonical boundary vacancies transports to
reachability of their bounded-face anchors. -/
theorem canonicalBoundaryFaceAnchor_reachable
    {R S : ℕ} (hR : 0 < R) (hS : 0 < S) (A : Finset Point)
    {p q : {z // z ∈ canonicalBoundaryNaturalVacancies R S A}}
    (hpq : (Boundary.kingGraph
      (canonicalBoundaryNaturalVacancies R S A)).Reachable p q) :
    (dualEdgeGraph (canonicalBoundaryPrimal R S A)).Reachable
      (some (boundaryFaceAnchor hR hS
        (canonicalBoundaryVacancyPrimal R S A p)))
      (some (boundaryFaceAnchor hR hS
        (canonicalBoundaryVacancyPrimal R S A q))) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hpq ⊢
  apply hpq.lift' (fun z => some (boundaryFaceAnchor hR hS
    (canonicalBoundaryVacancyPrimal R S A z)))
  intro u v huv
  change Relation.ReflTransGen
    (dualEdgeGraph (canonicalBoundaryPrimal R S A)).Adj _ _
  rw [← SimpleGraph.reachable_iff_reflTransGen]
  exact canonicalBoundaryFaceAnchor_reachable_of_kingAdjacent hR hS A u v
    ((Boundary.kingGraph_adj_iff u v).mp huv)
/-- No contracted label is incident with an unmarked bounded face. -/
theorem not_mem_canonicalBoundaryDualEdges_of_unmarked_incident
    {R S : ℕ} {A : Finset Point}
    (z : CanonicalBoundaryUnmarkedFace R S A)
    (e : RectangleEdge (R + 1) (S + 1))
    (he : some ((boundedFaceEquivFaceIndices R S).symm
      ⟨z.1, (Boundary.mem_unmarkedFaces.mp z.2).1⟩) ∈
        (rectangleDual (R + 1) (S + 1)).ends e) :
    e ∉ canonicalBoundaryDualEdges R S A := by
  intro heF
  rw [canonicalBoundaryDualEdges, mem_vacancyDualEdges] at heF
  rcases heF with ⟨p, hpX, hpe⟩
  let f := (boundedFaceEquivFaceIndices R S).symm
    ⟨z.1, (Boundary.mem_unmarkedFaces.mp z.2).1⟩
  have hside := faceSideEdge_surjective_incident f ⟨e, he⟩
  rcases hside with ⟨d, hd⟩
  have hpCorner : finPoint p ∈ Boundary.faceCorners z.1 := by
    have hcorner := finPoint_mem_faceCorners_of_primalIncident_faceSideEdge
      f d p (hd.symm ▸ hpe)
    have hfcoord := congrArg Subtype.val
      ((boundedFaceEquivFaceIndices R S).apply_symm_apply
        ⟨z.1, (Boundary.mem_unmarkedFaces.mp z.2).1⟩)
    rw [← hfcoord]
    exact hcorner
  have hpV : finPoint p ∈ canonicalBoundaryNaturalVacancies R S A := by
    exact mem_canonicalBoundaryPrimal.mp hpX
  have hinter : finPoint p ∈
      Boundary.faceCorners z.1 ∩ canonicalBoundaryNaturalVacancies R S A :=
    Finset.mem_inter.mpr ⟨hpCorner, hpV⟩
  have hempty := (Boundary.mem_unmarkedFaces.mp z.2).2
  have : finPoint p ∈ (∅ : Finset Boundary.LatticePoint) := hempty ▸ hinter
  simp at this

/-! ## Isolated vertices under labelled contraction -/

/-- A vertex incident with none of the selected labels is isolated in the
simple graph that generates the contraction. -/
theorem simpleGraphOn_isIsolated_of_no_selected_incident
    {V E : Type*} (G : LabeledMultigraph V E) (F : Finset E) (u : V)
    (hu : ∀ e ∈ F, u ∉ G.ends e) :
    (G.simpleGraphOn (F : Set E)).IsIsolated u := by
  intro v huv
  rw [G.simpleGraphOn_adj] at huv
  rcases huv with ⟨_, e, heF, he⟩
  exact hu e heF (by rw [he]; exact Sym2.mem_mk_left u v)

/-- The contraction component of an isolated vertex is a singleton. -/
theorem contractionMap_eq_iff_of_isolated
    {V E : Type*} (G : LabeledMultigraph V E) (F : Finset E) (u v : V)
    (hu : (G.simpleGraphOn (F : Set E)).IsIsolated u) :
    G.contractionMap F v = G.contractionMap F u ↔ v = u := by
  constructor
  · intro hcomponent
    by_contra hvu
    have hreach : (G.simpleGraphOn (F : Set E)).Reachable v u :=
      SimpleGraph.ConnectedComponent.exact hcomponent
    exact (SimpleGraph.not_reachable_of_neighborSet_right_eq_empty hvu
      hu.neighborSet_eq_empty) hreach
  · rintro rfl
    rfl

/-- At an isolated contraction component, incident surviving labels are
canonically the original incident labels. -/
noncomputable def contractIncidentLabelEquivOfIsolated
    {V E : Type*} (G : LabeledMultigraph V E) (F : Finset E) (u : V)
    (hloop : ∀ e, ¬G.IsLoop e)
    (hu : (G.simpleGraphOn (F : Set E)).IsIsolated u) :
    IncidentLabel (G.contract F) (G.contractionMap F u) ≃
      IncidentLabel G u where
  toFun e := by
    refine ⟨e.1.1, ?_⟩
    have he := e.2
    change G.contractionMap F u ∈
      Sym2.map (G.contractionMap F) (G.ends e.1.1) at he
    rcases Sym2.mem_map.mp he with ⟨v, hv, hvu⟩
    have : v = u :=
      (contractionMap_eq_iff_of_isolated G F u v hu).mp hvu
    simpa [this] using hv
  invFun e := by
    have hsurvive : ¬(G.contractWithLoops F).IsLoop e.1 := by
      intro hcollapsed
      change (Sym2.map (G.contractionMap F) (G.ends e.1)).IsDiag at hcollapsed
      rcases Sym2.mem_iff_exists.mp e.2 with ⟨v, hv⟩
      rw [hv, Sym2.map_mk, Sym2.mk_isDiag_iff] at hcollapsed
      have hvu : v = u :=
        (contractionMap_eq_iff_of_isolated G F u v hu).mp hcollapsed.symm
      subst v
      exact hloop e.1 ((G.isLoop_iff_exists_isLoopAt e.1).mpr ⟨u, hv⟩)
    refine ⟨⟨e.1, hsurvive⟩, ?_⟩
    change G.contractionMap F u ∈
      Sym2.map (G.contractionMap F) (G.ends e.1)
    exact Sym2.mem_map.mpr ⟨u, e.2, rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    rfl

/-- Contracting labels away from a vertex preserves its labelled degree. -/
theorem contract_degree_eq_of_isolated
    {V E : Type*} [Fintype V] [Finite E]
    (G : LabeledMultigraph V E) (F : Finset E)
    [Fintype ((G.simpleGraphOn (F : Set E)).ConnectedComponent)] (u : V)
    (hloop : ∀ e, ¬G.IsLoop e)
    (hu : (G.simpleGraphOn (F : Set E)).IsIsolated u) :
    (G.contract F).degree (G.contractionMap F u) = G.degree u := by
  rw [degree_eq_natCard_incidentLabel (G.contract F)
      (fun e => (G.contractWithLoops F).deleteLoops_loopless e)
      (G.contractionMap F u),
    degree_eq_natCard_incidentLabel G hloop u]
  exact Nat.card_congr (contractIncidentLabelEquivOfIsolated G F u hloop hu)

/-- Between two isolated contraction components, surviving link labels are
canonically the original link labels. -/
noncomputable def contractLinkEdgeEquivOfIsolated
    {V E : Type*} (G : LabeledMultigraph V E) (F : Finset E) (u v : V)
    (hu : (G.simpleGraphOn (F : Set E)).IsIsolated u)
    (hv : (G.simpleGraphOn (F : Set E)).IsIsolated v)
    (huv : u ≠ v) :
    (G.contract F).LinkEdge (G.contractionMap F u) (G.contractionMap F v) ≃
      G.LinkEdge u v where
  toFun e := by
    refine ⟨e.1.1, ?_⟩
    change G.ends e.1.1 = s(u, v)
    have he := e.2
    change Sym2.map (G.contractionMap F) (G.ends e.1.1) =
      s(G.contractionMap F u, G.contractionMap F v) at he
    induction hends : G.ends e.1.1 using Sym2.inductionOn with
    | _ a b =>
        rw [hends, Sym2.map_mk] at he
        rcases Sym2.eq_iff.mp he with h | h
        · have hau : a = u :=
            (contractionMap_eq_iff_of_isolated G F u a hu).mp h.1
          have hbv : b = v :=
            (contractionMap_eq_iff_of_isolated G F v b hv).mp h.2
          subst a
          subst b
          rfl
        · have hav : a = v :=
            (contractionMap_eq_iff_of_isolated G F v a hv).mp h.1
          have hbu : b = u :=
            (contractionMap_eq_iff_of_isolated G F u b hu).mp h.2
          subst a
          subst b
          exact Sym2.eq_swap
  invFun e := by
    have hmapne : G.contractionMap F u ≠ G.contractionMap F v := by
      intro h
      have hvu : v = u :=
        (contractionMap_eq_iff_of_isolated G F u v hu).mp h.symm
      exact huv hvu.symm
    have hmapped : (G.contractWithLoops F).IsLink e.1
        (G.contractionMap F u) (G.contractionMap F v) :=
      G.mapVertices_isLink (G.contractionMap F) e.1 u v e.2
    have hsurvive : ¬(G.contractWithLoops F).IsLoop e.1 :=
      (G.contractWithLoops F).not_isLoop_of_isLink_of_ne hmapped hmapne
    exact ⟨⟨e.1, hsurvive⟩, hmapped⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    rfl

/-- Contracting labels away from two vertices preserves their adjacency
multiplicity. -/
theorem contract_adjacencyMultiplicity_eq_of_isolated
    {V E : Type*} [Fintype V] [Finite E]
    (G : LabeledMultigraph V E) (F : Finset E) (u v : V)
    (hu : (G.simpleGraphOn (F : Set E)).IsIsolated u)
    (hv : (G.simpleGraphOn (F : Set E)).IsIsolated v) :
    (G.contract F).adjacencyMultiplicity
        (G.contractionMap F u) (G.contractionMap F v) =
      G.adjacencyMultiplicity u v := by
  by_cases huv : u = v
  · subst v
    simp
  · have hmapne : G.contractionMap F u ≠ G.contractionMap F v := by
      intro h
      have hvu : v = u :=
        (contractionMap_eq_iff_of_isolated G F u v hu).mp h.symm
      exact huv hvu.symm
    rw [(G.contract F).adjacencyMultiplicity_of_ne hmapne,
      G.adjacencyMultiplicity_of_ne huv]
    unfold LabeledMultigraph.edgeMultiplicity
    exact Nat.card_congr (contractLinkEdgeEquivOfIsolated G F u v hu hv huv)

/-! ## The surviving bounded-face components -/

noncomputable local instance planarComplementContractedVertexFintype
    (R S : ℕ) (A : Finset Point) :
    Fintype (CanonicalBoundaryContractedVertex R S A) :=
  canonicalBoundaryContractedVertexFintype R S A

/-- The bounded dual vertex represented by an unmarked natural face index. -/
def canonicalBoundaryUnmarkedDualVertex (R S : ℕ) (A : Finset Point)
    (z : CanonicalBoundaryUnmarkedFace R S A) :
    Option (BoundedFace (R + 1) (S + 1)) :=
  some ((boundedFaceEquivFaceIndices R S).symm
    ⟨z.1, (Boundary.mem_unmarkedFaces.mp z.2).1⟩)

/-- The contraction component represented by an unmarked face. -/
def canonicalBoundaryUnmarkedComponent (R S : ℕ) (A : Finset Point)
    (z : CanonicalBoundaryUnmarkedFace R S A) :
    CanonicalBoundaryContractedVertex R S A :=
  (rectangleDual (R + 1) (S + 1)).contractionMap
    (canonicalBoundaryDualEdges R S A)
    (canonicalBoundaryUnmarkedDualVertex R S A z)

/-- Every unmarked bounded face is an isolated vertex of the selected-label
graph used for the boundary contraction. -/
theorem canonicalBoundaryUnmarkedDualVertex_isIsolated
    (R S : ℕ) (A : Finset Point)
    (z : CanonicalBoundaryUnmarkedFace R S A) :
    ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
      (canonicalBoundaryDualEdges R S A :
        Set (RectangleEdge (R + 1) (S + 1)))).IsIsolated
      (canonicalBoundaryUnmarkedDualVertex R S A z) := by
  apply simpleGraphOn_isIsolated_of_no_selected_incident
  intro e heF hez
  exact (not_mem_canonicalBoundaryDualEdges_of_unmarked_incident z e hez) heF

/-- Contracting the vacancy labels preserves degree four at each unmarked
bounded face. -/
theorem canonicalBoundaryContractedDual_degree_unmarkedComponent
    (R S : ℕ) (A : Finset Point)
    (z : CanonicalBoundaryUnmarkedFace R S A) :
    (canonicalBoundaryContractedDual R S A).degree
      (canonicalBoundaryUnmarkedComponent R S A z) = 4 := by
  let f := (boundedFaceEquivFaceIndices R S).symm
    ⟨z.1, (Boundary.mem_unmarkedFaces.mp z.2).1⟩
  have hR : 2 ≤ R + 1 := by
    have := f.1.2
    omega
  have hS : 2 ≤ S + 1 := by
    have := f.2.2
    omega
  calc
    (canonicalBoundaryContractedDual R S A).degree
        (canonicalBoundaryUnmarkedComponent R S A z) =
      (rectangleDual (R + 1) (S + 1)).degree
        (canonicalBoundaryUnmarkedDualVertex R S A z) :=
      contract_degree_eq_of_isolated
        (rectangleDual (R + 1) (S + 1))
        (canonicalBoundaryDualEdges R S A)
        (canonicalBoundaryUnmarkedDualVertex R S A z)
        (rectangleDual_not_isLoop hR hS)
        (canonicalBoundaryUnmarkedDualVertex_isIsolated R S A z)
    _ = 4 := by
      change (rectangleDual (R + 1) (S + 1)).degree (some f) = 4
      exact rectangleDual_degree_some f

/-- Contracting vacancy labels preserves the exact square-lattice adjacency
multiplicity between unmarked bounded faces. -/
theorem canonicalBoundaryContractedDual_adjacency_unmarkedComponents
    (R S : ℕ) (A : Finset Point)
    (z w : CanonicalBoundaryUnmarkedFace R S A) :
    (canonicalBoundaryContractedDual R S A).adjacencyMultiplicity
        (canonicalBoundaryUnmarkedComponent R S A z)
        (canonicalBoundaryUnmarkedComponent R S A w) =
      if Boundary.natManhattanDist z.1 w.1 = 1 then 1 else 0 := by
  let f := (boundedFaceEquivFaceIndices R S).symm
    ⟨z.1, (Boundary.mem_unmarkedFaces.mp z.2).1⟩
  let g := (boundedFaceEquivFaceIndices R S).symm
    ⟨w.1, (Boundary.mem_unmarkedFaces.mp w.2).1⟩
  have hfcoord : (f.1.1, f.2.1) = z.1 := by
    exact congrArg
      (fun q : {x // x ∈ Boundary.faceIndices R S} => q.1)
      ((boundedFaceEquivFaceIndices R S).apply_symm_apply
        ⟨z.1, (Boundary.mem_unmarkedFaces.mp z.2).1⟩)
  have hgcoord : (g.1.1, g.2.1) = w.1 := by
    exact congrArg
      (fun q : {x // x ∈ Boundary.faceIndices R S} => q.1)
      ((boundedFaceEquivFaceIndices R S).apply_symm_apply
        ⟨w.1, (Boundary.mem_unmarkedFaces.mp w.2).1⟩)
  calc
    (canonicalBoundaryContractedDual R S A).adjacencyMultiplicity
        (canonicalBoundaryUnmarkedComponent R S A z)
        (canonicalBoundaryUnmarkedComponent R S A w) =
      (rectangleDual (R + 1) (S + 1)).adjacencyMultiplicity
        (canonicalBoundaryUnmarkedDualVertex R S A z)
        (canonicalBoundaryUnmarkedDualVertex R S A w) :=
      contract_adjacencyMultiplicity_eq_of_isolated
        (rectangleDual (R + 1) (S + 1))
        (canonicalBoundaryDualEdges R S A)
        (canonicalBoundaryUnmarkedDualVertex R S A z)
        (canonicalBoundaryUnmarkedDualVertex R S A w)
        (canonicalBoundaryUnmarkedDualVertex_isIsolated R S A z)
        (canonicalBoundaryUnmarkedDualVertex_isIsolated R S A w)
    _ = if Boundary.natManhattanDist z.1 w.1 = 1 then 1 else 0 := by
      change (rectangleDual (R + 1) (S + 1)).adjacencyMultiplicity
        (some f) (some g) = _
      rw [rectangleDual_adjacencyMultiplicity_some_some, hfcoord, hgcoord]

/-! ## Component classification from marked-face wiring -/

/-- An unmarked face component is never the exterior component. -/
theorem canonicalBoundaryUnmarkedComponent_ne_root
    (R S : ℕ) (A : Finset Point)
    (z : CanonicalBoundaryUnmarkedFace R S A) :
    canonicalBoundaryUnmarkedComponent R S A z ≠
      canonicalBoundaryContractionRoot R S A := by
  intro h
  have hvertex : (none : Option (BoundedFace (R + 1) (S + 1))) =
      canonicalBoundaryUnmarkedDualVertex R S A z :=
    (contractionMap_eq_iff_of_isolated
      (rectangleDual (R + 1) (S + 1))
      (canonicalBoundaryDualEdges R S A)
      (canonicalBoundaryUnmarkedDualVertex R S A z) none
      (canonicalBoundaryUnmarkedDualVertex_isIsolated R S A z)).mp h.symm
  simp [canonicalBoundaryUnmarkedDualVertex] at hvertex

/-- Distinct unmarked face indices give distinct original bounded dual
vertices. -/
theorem canonicalBoundaryUnmarkedDualVertex_injective
    (R S : ℕ) (A : Finset Point) :
    Function.Injective (canonicalBoundaryUnmarkedDualVertex R S A) := by
  intro z w hzw
  have hface :
      (boundedFaceEquivFaceIndices R S).symm
          ⟨z.1, (Boundary.mem_unmarkedFaces.mp z.2).1⟩ =
        (boundedFaceEquivFaceIndices R S).symm
          ⟨w.1, (Boundary.mem_unmarkedFaces.mp w.2).1⟩ :=
    Option.some_injective _ hzw
  have hindex :
      (⟨z.1, (Boundary.mem_unmarkedFaces.mp z.2).1⟩ :
          {x // x ∈ Boundary.faceIndices R S}) =
        ⟨w.1, (Boundary.mem_unmarkedFaces.mp w.2).1⟩ :=
    (boundedFaceEquivFaceIndices R S).symm.injective hface
  apply Subtype.ext
  exact congrArg
    (fun q : {x // x ∈ Boundary.faceIndices R S} => q.1) hindex

/-- Distinct unmarked faces remain distinct after contraction. -/
theorem canonicalBoundaryUnmarkedComponent_injective
    (R S : ℕ) (A : Finset Point) :
    Function.Injective (canonicalBoundaryUnmarkedComponent R S A) := by
  intro z w hzw
  have hvertex : canonicalBoundaryUnmarkedDualVertex R S A w =
      canonicalBoundaryUnmarkedDualVertex R S A z :=
    (contractionMap_eq_iff_of_isolated
      (rectangleDual (R + 1) (S + 1))
      (canonicalBoundaryDualEdges R S A)
      (canonicalBoundaryUnmarkedDualVertex R S A z)
      (canonicalBoundaryUnmarkedDualVertex R S A w)
      (canonicalBoundaryUnmarkedDualVertex_isIsolated R S A z)).mp hzw.symm
  exact canonicalBoundaryUnmarkedDualVertex_injective R S A hvertex.symm

/-- The precise remaining connectivity assertion for the contraction:
every bounded face meeting a canonical boundary vacancy belongs to the
exterior component. -/
def BoundaryMarkedFaceWiring (R S : ℕ) (A : Finset Point) : Prop :=
  ∀ f : BoundedFace (R + 1) (S + 1),
    (f.1.1, f.2.1) ∈ Boundary.markedFaces R S
      (canonicalBoundaryNaturalVacancies R S A) →
    (rectangleDual (R + 1) (S + 1)).contractionMap
        (canonicalBoundaryDualEdges R S A) (some f) =
      canonicalBoundaryContractionRoot R S A

/-- Canonical boundary vacancies do wire every marked face to the exterior.
This is the explicit king-path-to-dual-face-star argument. -/
theorem canonicalBoundaryMarkedFaceWiring
    (R S : ℕ) (A : Finset Point) :
    BoundaryMarkedFaceWiring R S A := by
  intro f hf
  have hR : 0 < R := by have := f.1.2; omega
  have hS : 0 < S := by have := f.2.2; omega
  rcases Boundary.mem_markedFaces.mp hf with
    ⟨_, _, z, hzB, hfx0, hfx1, hfy0, hfy1⟩
  let p : {z // z ∈ canonicalBoundaryNaturalVacancies R S A} := ⟨z, hzB⟩
  let pp := canonicalBoundaryVacancyPrimal R S A p
  have hppCorner : finPoint pp ∈
      Boundary.faceCorners (f.1.1, f.2.1) := by
    rw [Boundary.mem_faceCorners]
    simpa [pp, p] using ⟨hfx0, hfx1, hfy0, hfy1⟩
  rcases boundaryVacancy_reachable_perimeter p with ⟨q, hqPerim, hpq⟩
  let qq := canonicalBoundaryVacancyPrimal R S A q
  have hqPerimFin : Boundary.IsPerimeter R S (finPoint qq) := by
    simpa [qq] using hqPerim
  have hstart :
      (dualEdgeGraph (canonicalBoundaryPrimal R S A)).Reachable
        (some f) (some (boundaryFaceAnchor hR hS pp)) :=
    dualEdgeGraph_reachable_some_some_of_shared_selected_corner
      pp (canonicalBoundaryVacancyPrimal_mem R S A p)
      f (boundaryFaceAnchor hR hS pp) hppCorner
      (finPoint_mem_faceCorners_boundaryFaceAnchor hR hS pp)
  have hmiddle :
      (dualEdgeGraph (canonicalBoundaryPrimal R S A)).Reachable
        (some (boundaryFaceAnchor hR hS pp))
        (some (boundaryFaceAnchor hR hS qq)) :=
    canonicalBoundaryFaceAnchor_reachable hR hS A hpq
  have hend :
      (dualEdgeGraph (canonicalBoundaryPrimal R S A)).Reachable
        (some (boundaryFaceAnchor hR hS qq)) none :=
    (dualEdgeGraph_adj_some_none_of_selected_perimeter_corner
      qq (canonicalBoundaryVacancyPrimal_mem R S A q)
      (boundaryFaceAnchor hR hS qq)
      (finPoint_mem_faceCorners_boundaryFaceAnchor hR hS qq)
      hqPerimFin).reachable
  exact SimpleGraph.ConnectedComponent.sound (hstart.trans (hmiddle.trans hend))

/-- Under marked-face wiring, every non-root contraction component is the
component of a unique unmarked bounded face. -/
theorem canonicalBoundaryUnmarkedComponent_surjective_away_root
    (R S : ℕ) (A : Finset Point)
    (hwiring : BoundaryMarkedFaceWiring R S A) :
    ∀ c : CanonicalBoundaryContractedVertex R S A,
      c ≠ canonicalBoundaryContractionRoot R S A →
      ∃ z : CanonicalBoundaryUnmarkedFace R S A,
        c = canonicalBoundaryUnmarkedComponent R S A z := by
  intro c
  refine SimpleGraph.ConnectedComponent.ind (fun v => ?_) c
  intro hc
  cases v with
  | none =>
      exact (hc rfl).elim
  | some f =>
      let q := boundedFaceEquivFaceIndices R S f
      by_cases hq : q.1 ∈ Boundary.unmarkedFaces R S
          (canonicalBoundaryNaturalVacancies R S A)
      · let z : CanonicalBoundaryUnmarkedFace R S A := ⟨q.1, hq⟩
        refine ⟨z, ?_⟩
        change
          (rectangleDual (R + 1) (S + 1)).contractionMap
              (canonicalBoundaryDualEdges R S A) (some f) =
            (rectangleDual (R + 1) (S + 1)).contractionMap
              (canonicalBoundaryDualEdges R S A)
              (some ((boundedFaceEquivFaceIndices R S).symm
                ⟨q.1, (Boundary.mem_unmarkedFaces.mp hq).1⟩))
        have hqSubtype :
            (⟨q.1, (Boundary.mem_unmarkedFaces.mp hq).1⟩ :
                {x // x ∈ Boundary.faceIndices R S}) = q := by
          apply Subtype.ext
          rfl
        rw [hqSubtype, (boundedFaceEquivFaceIndices R S).symm_apply_apply]
      · have hmarked : q.1 ∈ Boundary.markedFaces R S
            (canonicalBoundaryNaturalVacancies R S A) := by
          have hface : q.1 ∈ Boundary.faceIndices R S := q.2
          simpa [Boundary.unmarkedFaces, hface] using hq
        exact (hc (hwiring f (by simpa [q] using hmarked))).elim

/-- The canonical equivalence from unmarked faces to components away from
the exterior root. -/
noncomputable def canonicalBoundaryUnmarkedAwayEquiv
    (R S : ℕ) (A : Finset Point)
    (hwiring : BoundaryMarkedFaceWiring R S A) :
    CanonicalBoundaryUnmarkedFace R S A ≃
      {c : CanonicalBoundaryContractedVertex R S A //
        c ≠ canonicalBoundaryContractionRoot R S A} :=
  Equiv.ofBijective
    (fun z => ⟨canonicalBoundaryUnmarkedComponent R S A z,
      canonicalBoundaryUnmarkedComponent_ne_root R S A z⟩)
    ⟨fun _ _ h => canonicalBoundaryUnmarkedComponent_injective R S A
        (congrArg Subtype.val h),
      fun c => by
        rcases canonicalBoundaryUnmarkedComponent_surjective_away_root
          R S A hwiring c.1 c.2 with ⟨z, hz⟩
        exact ⟨z, Subtype.ext hz.symm⟩⟩

/-- The component classification aligned with natural unmarked-face
coordinates. -/
noncomputable def canonicalBoundaryComponentEquiv
    (R S : ℕ) (A : Finset Point)
    (hwiring : BoundaryMarkedFaceWiring R S A) :
    CanonicalBoundaryContractedVertex R S A ≃
      Option (CanonicalBoundaryUnmarkedFace R S A) := by
  classical
  exact (Equiv.optionSubtypeNe
      (canonicalBoundaryContractionRoot R S A)).symm.trans
    (Equiv.optionCongr (canonicalBoundaryUnmarkedAwayEquiv R S A hwiring).symm)

@[simp] theorem canonicalBoundaryComponentEquiv_root
    (R S : ℕ) (A : Finset Point)
    (hwiring : BoundaryMarkedFaceWiring R S A) :
    canonicalBoundaryComponentEquiv R S A hwiring
      (canonicalBoundaryContractionRoot R S A) = none := by
  classical
  simp [canonicalBoundaryComponentEquiv]

@[simp] theorem canonicalBoundaryComponentEquiv_unmarkedComponent
    (R S : ℕ) (A : Finset Point)
    (hwiring : BoundaryMarkedFaceWiring R S A)
    (z : CanonicalBoundaryUnmarkedFace R S A) :
    canonicalBoundaryComponentEquiv R S A hwiring
      (canonicalBoundaryUnmarkedComponent R S A z) = some z := by
  classical
  let e := canonicalBoundaryUnmarkedAwayEquiv R S A hwiring
  change Equiv.optionCongr e.symm
      ((Equiv.optionSubtypeNe
        (canonicalBoundaryContractionRoot R S A)).symm
          (canonicalBoundaryUnmarkedComponent R S A z)) = some z
  rw [Equiv.optionSubtypeNe_symm_of_ne
    (canonicalBoundaryUnmarkedComponent_ne_root R S A z)]
  change Equiv.optionCongr e.symm (some (e z)) = some z
  rw [Equiv.optionCongr_apply]
  exact congrArg some (e.symm_apply_apply z)

/-- All four fields of the contraction presentation follow from the single
marked-face wiring assertion. -/
noncomputable def boundaryContractionPresentationOfMarkedFaceWiring
    (R S : ℕ) (A : Finset Point)
    (hwiring : BoundaryMarkedFaceWiring R S A) :
    BoundaryContractionPresentation R S A where
  componentEquiv := canonicalBoundaryComponentEquiv R S A hwiring
  root_eq := canonicalBoundaryComponentEquiv_root R S A hwiring
  degree_face z := by
    have hcomponent := congrArg
      (canonicalBoundaryComponentEquiv R S A hwiring).symm
      (canonicalBoundaryComponentEquiv_unmarkedComponent R S A hwiring z)
    simp only [Equiv.symm_apply_apply] at hcomponent
    rw [← hcomponent]
    exact canonicalBoundaryContractedDual_degree_unmarkedComponent R S A z
  adjacency_face z w := by
    have hz := congrArg
      (canonicalBoundaryComponentEquiv R S A hwiring).symm
      (canonicalBoundaryComponentEquiv_unmarkedComponent R S A hwiring z)
    have hw := congrArg
      (canonicalBoundaryComponentEquiv R S A hwiring).symm
      (canonicalBoundaryComponentEquiv_unmarkedComponent R S A hwiring w)
    simp only [Equiv.symm_apply_apply] at hz hw
    rw [← hz, ← hw]
    exact canonicalBoundaryContractedDual_adjacency_unmarkedComponents R S A z w

/-- The canonical contraction presentation, with no remaining geometric
hypotheses. -/
noncomputable def canonicalBoundaryContractionPresentation
    (R S : ℕ) (A : Finset Point) :
    BoundaryContractionPresentation R S A :=
  boundaryContractionPresentationOfMarkedFaceWiring R S A
    (canonicalBoundaryMarkedFaceWiring R S A)

/-- Once the two planar cotree equivalences are supplied, all contraction
geometry is now constructed internally. -/
noncomputable def boundaryPlanarTreeComplementOfTreeEquivs
    (R S : ℕ) (A : Finset Point)
    (rectangleTreeEquiv :
      SimpleSpanningTreeType
        (inducedGrid (rectangle 0 0 (R + 1) (S + 1))) ≃
        (rectangleDual (R + 1) (S + 1)).SpanningTree)
    (vacancyTreeEquiv :
      SimpleSpanningTreeType
        (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
          Boundary.canonicalBoundary R S A)) ≃
        (canonicalBoundaryContractedDual R S A).SpanningTree) :
    BoundaryPlanarTreeComplement R S A where
  rectangleTreeEquiv := rectangleTreeEquiv
  vacancyTreeEquiv := vacancyTreeEquiv
  contraction := canonicalBoundaryContractionPresentation R S A

/-! ## Labelled trees versus simple spanning subgraphs -/

/-- Labels whose unordered endpoint pair belongs to a displayed simple
subgraph. -/
noncomputable def labelsOfSimpleSubgraph
    {V E : Type*} [Fintype E] (G : LabeledMultigraph V E)
    (T : SimpleGraph V) : Finset E := by
  classical
  exact Finset.univ.filter fun e => G.ends e ∈ T.edgeSet

@[simp] theorem mem_labelsOfSimpleSubgraph
    {V E : Type*} [Fintype E] (G : LabeledMultigraph V E)
    (T : SimpleGraph V) (e : E) :
    e ∈ labelsOfSimpleSubgraph G T ↔ G.ends e ∈ T.edgeSet := by
  classical
  simp [labelsOfSimpleSubgraph]

/-- With globally unique nonloop labels, selecting labels from a simple
subgraph recovers that subgraph exactly. -/
theorem simpleGraphOn_labelsOfSimpleSubgraph
    {V E : Type*} [Fintype E] (G : LabeledMultigraph V E)
    (T : SimpleGraph V) (hT : T ≤ G.toSimpleGraph) :
    G.simpleGraphOn (labelsOfSimpleSubgraph G T : Set E) = T := by
  ext u v
  constructor
  · rintro ⟨_, e, he, huv⟩
    have heT := (mem_labelsOfSimpleSubgraph G T e).mp he
    rw [huv, SimpleGraph.mem_edgeSet] at heT
    exact heT
  · intro huv
    have huvG := hT huv
    rcases huvG with ⟨huvne, e, he⟩
    refine ⟨huvne, e, ?_, he⟩
    apply (mem_labelsOfSimpleSubgraph G T e).mpr
    rw [he, SimpleGraph.mem_edgeSet]
    exact huv

/-- The selected labels of a simple subgraph are in bijection with its
unordered edges when endpoint labels are globally injective. -/
noncomputable def labelsOfSimpleSubgraphEdgeEquiv
    {V E : Type*} [Fintype E] (G : LabeledMultigraph V E)
    (hends : Function.Injective G.ends)
    (T : SimpleGraph V) (hT : T ≤ G.toSimpleGraph) :
    {e : E // e ∈ labelsOfSimpleSubgraph G T} ≃ T.edgeSet :=
  Equiv.ofBijective
    (fun e => ⟨G.ends e.1, (mem_labelsOfSimpleSubgraph G T e.1).mp e.2⟩)
    ⟨fun e e' h => Subtype.ext (hends (congrArg Subtype.val h)),
      fun a => by
        induction ha : a.1 using Sym2.inductionOn with
        | _ u v =>
            have huvT : T.Adj u v := by
              rw [← SimpleGraph.mem_edgeSet, ← ha]
              exact a.2
            rcases hT huvT with ⟨_, e, he⟩
            refine ⟨⟨e, (mem_labelsOfSimpleSubgraph G T e).mpr ?_⟩, ?_⟩
            · rw [he, SimpleGraph.mem_edgeSet]
              exact huvT
            · apply Subtype.ext
              exact he.trans ha.symm⟩

/-- A simple spanning tree determines a labelled spanning tree whenever
ambient labels are unique and nonloop. -/
theorem labelsOfSimpleSubgraph_isSpanningTree
    {V E : Type*} [Fintype V] [Fintype E]
    (G : LabeledMultigraph V E)
    (hloop : ∀ e, ¬G.IsLoop e)
    (hends : Function.Injective G.ends)
    (T : SimpleGraph V) (hTle : T ≤ G.toSimpleGraph) (hTree : T.IsTree) :
    G.IsSpanningTree (labelsOfSimpleSubgraph G T) := by
  letI : Fintype (Sym2 V) := Fintype.ofFinite _
  letI : Fintype T.edgeSet := Fintype.ofFinite _
  refine ⟨fun e _ => hloop e, ?_, ?_⟩
  · rw [simpleGraphOn_labelsOfSimpleSubgraph G T hTle]
    exact hTree.connected
  · have hcard : (labelsOfSimpleSubgraph G T).card = T.edgeFinset.card := by
      rw [← Fintype.card_coe, SimpleGraph.edgeFinset_card]
      exact Fintype.card_congr
        (labelsOfSimpleSubgraphEdgeEquiv G hends T hTle)
    rw [hcard]
    exact hTree.card_edgeFinset

/-- For unique nonloop labels, labelled spanning trees and simple spanning
subgraphs are canonically equivalent. -/
noncomputable def labeledSpanningTreeEquivSimple
    {V E : Type*} [Fintype V] [Fintype E]
    (G : LabeledMultigraph V E)
    (hloop : ∀ e, ¬G.IsLoop e)
    (hends : Function.Injective G.ends) :
    G.SpanningTree ≃ SimpleSpanningTreeType G.toSimpleGraph where
  toFun F := ⟨G.simpleGraphOn (F.1 : Set E),
    (by
      rw [← G.simpleGraphOn_univ]
      exact G.simpleGraphOn_mono (Set.subset_univ _)),
    F.2.toSimpleGraph_isTree⟩
  invFun T := ⟨labelsOfSimpleSubgraph G T.1,
    labelsOfSimpleSubgraph_isSpanningTree G hloop hends T.1 T.2.1 T.2.2⟩
  left_inv F := by
    apply Subtype.ext
    ext e
    constructor
    · intro he
      rw [mem_labelsOfSimpleSubgraph] at he
      induction hendsE : G.ends e using Sym2.inductionOn with
      | _ u v =>
          have huv : (G.simpleGraphOn (F.1 : Set E)).Adj u v := by
            rw [← SimpleGraph.mem_edgeSet, ← hendsE]
            exact he
          rcases huv with ⟨_, e', he'F, he'⟩
          exact hends (hendsE.trans he'.symm) ▸ he'F
    · intro heF
      rw [mem_labelsOfSimpleSubgraph]
      change G.ends e ∈ (G.simpleGraphOn (F.1 : Set E)).edgeSet
      induction hendsE : G.ends e using Sym2.inductionOn with
      | _ u v =>
          rw [SimpleGraph.mem_edgeSet]
          have huvne : u ≠ v := by
            intro huv
            subst v
            exact hloop e ((G.isLoop_iff_exists_isLoopAt e).mpr ⟨u, hendsE⟩)
          exact ⟨huvne, e, heF, hendsE⟩
  right_inv T := by
    apply Subtype.ext
    exact simpleGraphOn_labelsOfSimpleSubgraph G T.1 T.2.1

/-! ## Transport of simple spanning trees -/

/-- A graph isomorphism transports every spanning subgraph, and hence every
spanning tree, by the underlying vertex equivalence. -/
noncomputable def simpleSpanningTreeEquivOfIso
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) :
    SimpleSpanningTreeType G ≃ SimpleSpanningTreeType H where
  toFun T := ⟨e.toEquiv.simpleGraph T.1, by
    constructor
    · intro u v huv
      change T.1.Adj (e.symm u) (e.symm v) at huv
      simpa using e.map_rel_iff.mpr (T.2.1 huv)
    · have hmap : e.toEquiv.simpleGraph T.1 =
          T.1.map e.toEquiv.toEmbedding := by
        exact SimpleGraph.comap_symm T.1 e.toEquiv
      rw [hmap]
      exact (SimpleGraph.Iso.map e.toEquiv T.1).isTree_iff.mp T.2.2⟩
  invFun T := ⟨e.symm.toEquiv.simpleGraph T.1, by
    constructor
    · intro u v huv
      change T.1.Adj (e u) (e v) at huv
      simpa using e.map_rel_iff.mp (T.2.1 huv)
    · have hmap : e.symm.toEquiv.simpleGraph T.1 =
          T.1.map e.symm.toEquiv.toEmbedding := by
        exact SimpleGraph.comap_symm T.1 e.symm.toEquiv
      rw [hmap]
      exact (SimpleGraph.Iso.map e.symm.toEquiv T.1).isTree_iff.mp T.2.2⟩
  left_inv T := by
    apply Subtype.ext
    exact e.toEquiv.simpleGraph.symm_apply_apply T.1
  right_inv T := by
    apply Subtype.ext
    exact e.toEquiv.simpleGraph.apply_symm_apply T.1

/-- The natural integer-coordinate rectangle and the labelled primal
rectangle have the same underlying simple graph. -/
noncomputable def rectangleGridPrimalIso (r s : ℕ) :
    inducedGrid (rectangle 0 0 r s) ≃g
      (rectanglePrimal r s).toSimpleGraph := by
  simpa only [rectanglePrimal_toSimpleGraph] using
    (standardRectangleGridIso r s)

/-! ## Unique labels in the primal rectangle -/

/-- A primal rectangle label is never a loop. -/
theorem rectanglePrimal_not_isLoop
    {r s : ℕ} (e : RectangleEdge r s) :
    ¬(rectanglePrimal r s).IsLoop e := by
  cases e with
  | horizontal e =>
      apply (rectanglePrimal r s).not_isLoop_of_isLink_of_ne
        (u := horizontalPrimalLeft e) (v := horizontalPrimalRight e)
      · rfl
      · intro h
        have hx := congrArg (fun p => p.1.1) h
        simp [horizontalPrimalLeft, horizontalPrimalRight] at hx
  | vertical e =>
      apply (rectanglePrimal r s).not_isLoop_of_isLink_of_ne
        (u := verticalPrimalBottom e) (v := verticalPrimalTop e)
      · rfl
      · intro h
        have hy := congrArg (fun p => p.2.1) h
        simp [verticalPrimalBottom, verticalPrimalTop] at hy

/-- Distinct primal rectangle labels have distinct unordered endpoint
pairs.  Thus no parallel edges are hidden on the primal side. -/
theorem rectanglePrimal_ends_injective (r s : ℕ) :
    Function.Injective (rectanglePrimal r s).ends := by
  intro e f hef
  cases e with
  | horizontal e =>
      cases f with
      | horizontal f =>
          rcases Sym2.eq_iff.mp hef with h | h
          · apply congrArg RectangleEdge.horizontal
            cases e with
            | mk ex ey =>
                cases f with
                | mk fx fy =>
                    have hx : ex = fx := Fin.ext
                      (congrArg (fun p => p.1.1) h.1)
                    have hy : ey = fy := congrArg Prod.snd h.1
                    subst fx
                    subst fy
                    rfl
          · have h₁ := congrArg (fun p => p.1.1) h.1
            have h₂ := congrArg (fun p => p.1.1) h.2
            simp [horizontalPrimalLeft, horizontalPrimalRight] at h₁ h₂
            omega
      | vertical f =>
          rcases Sym2.eq_iff.mp hef with h | h
          · have h₁ := congrArg (fun p => p.2.1) h.1
            have h₂ := congrArg (fun p => p.2.1) h.2
            simp [horizontalPrimalLeft, horizontalPrimalRight,
              verticalPrimalBottom, verticalPrimalTop] at h₁ h₂
            omega
          · have h₁ := congrArg (fun p => p.2.1) h.1
            have h₂ := congrArg (fun p => p.2.1) h.2
            simp [horizontalPrimalLeft, horizontalPrimalRight,
              verticalPrimalBottom, verticalPrimalTop] at h₁ h₂
            omega
  | vertical e =>
      cases f with
      | horizontal f =>
          rcases Sym2.eq_iff.mp hef with h | h
          · have h₁ := congrArg (fun p => p.2.1) h.1
            have h₂ := congrArg (fun p => p.2.1) h.2
            simp [horizontalPrimalLeft, horizontalPrimalRight,
              verticalPrimalBottom, verticalPrimalTop] at h₁ h₂
            omega
          · have h₁ := congrArg (fun p => p.2.1) h.1
            have h₂ := congrArg (fun p => p.2.1) h.2
            simp [horizontalPrimalLeft, horizontalPrimalRight,
              verticalPrimalBottom, verticalPrimalTop] at h₁ h₂
            omega
      | vertical f =>
          rcases Sym2.eq_iff.mp hef with h | h
          · apply congrArg RectangleEdge.vertical
            cases e with
            | mk ex ey =>
                cases f with
                | mk fx fy =>
                    have hx : ex = fx := congrArg Prod.fst h.1
                    have hy : ey = fy := Fin.ext
                      (congrArg (fun p => p.2.1) h.1)
                    subst fx
                    subst fy
                    rfl
          · have h₁ := congrArg (fun p => p.2.1) h.1
            have h₂ := congrArg (fun p => p.2.1) h.2
            simp [verticalPrimalBottom, verticalPrimalTop] at h₁ h₂
            omega

/-! ## The exact rectangle cycle--cut residual -/

/-- Proposition-valued cycle--cut law for the explicit labelled rectangle.
It says exactly that taking the complementary set of the common primal/dual
edge labels exchanges spanning trees.  This is stronger and more useful than
a bare equality of tree counts. -/
def RectangleTreeComplementLaw (r s : ℕ) : Prop :=
  ∀ F : Finset (RectangleEdge r s),
    (rectanglePrimal r s).IsSpanningTree F ↔
      (rectangleDual r s).IsSpanningTree (Finset.univ \ F)

/-- Complementing the common edge labels is an involutive equivalence of
labelled primal and dual trees, assuming precisely the rectangle cycle--cut
law. -/
noncomputable def rectangleLabeledTreeComplementEquiv
    {r s : ℕ} (h : RectangleTreeComplementLaw r s) :
    (rectanglePrimal r s).SpanningTree ≃
      (rectangleDual r s).SpanningTree where
  toFun T := ⟨Finset.univ \ T.1, (h T.1).mp T.2⟩
  invFun T := ⟨Finset.univ \ T.1, by
    apply (h (Finset.univ \ T.1)).mpr
    simpa using T.2⟩
  left_inv T := by
    apply Subtype.ext
    simp
  right_inv T := by
    apply Subtype.ext
    simp

@[simp] theorem mem_rectangleLabeledTreeComplementEquiv
    {r s : ℕ} (h : RectangleTreeComplementLaw r s)
    (T : (rectanglePrimal r s).SpanningTree)
    (e : RectangleEdge r s) :
    e ∈ (rectangleLabeledTreeComplementEquiv h T).1 ↔ e ∉ T.1 := by
  simp [rectangleLabeledTreeComplementEquiv]

/-- The exact full-rectangle equivalence required by the determinant bridge,
with its complement action made explicit at the labelled middle stage. -/
noncomputable def rectangleTreeEquivOfComplementLaw
    (R S : ℕ) (h : RectangleTreeComplementLaw (R + 1) (S + 1)) :
    SimpleSpanningTreeType
        (inducedGrid (rectangle 0 0 (R + 1) (S + 1))) ≃
      (rectangleDual (R + 1) (S + 1)).SpanningTree :=
  (simpleSpanningTreeEquivOfIso
      (rectangleGridPrimalIso (R + 1) (S + 1))).trans
    ((labeledSpanningTreeEquivSimple
      (rectanglePrimal (R + 1) (S + 1))
      rectanglePrimal_not_isLoop
      (rectanglePrimal_ends_injective (R + 1) (S + 1))).symm.trans
        (rectangleLabeledTreeComplementEquiv h))

/-! ## A finite parity obstruction to forests -/

/-- A nonempty finite graph in which every vertex has even degree contains a
cycle.  The proof takes a nontrivial connected component; if it were a tree,
Mathlib's finite-tree leaf theorem would give a vertex of degree one. -/
theorem not_isAcyclic_of_nonempty_even_degree
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hne : G ≠ ⊥) (heven : ∀ v, Even (G.degree v)) :
    ¬G.IsAcyclic := by
  classical
  intro hacyc
  obtain ⟨p, hp⟩ := SimpleGraph.edgeSet_nonempty.mpr hne
  induction hp' : p using Sym2.inductionOn with
  | _ u v =>
      have huv : G.Adj u v := by
        rw [← SimpleGraph.mem_edgeSet, ← hp']
        exact hp
      let C := G.connectedComponentMk u
      have huC : u ∈ C :=
        SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      have hvC : v ∈ C := C.mem_supp_of_adj_mem_supp huC huv
      let uC : C := ⟨u, huC⟩
      let vC : C := ⟨v, hvC⟩
      have huvC : uC ≠ vC := by
        intro h
        exact huv.ne (congrArg Subtype.val h)
      letI : Nontrivial C := ⟨⟨uC, vC, huvC⟩⟩
      letI : Fintype C := Fintype.ofFinite C
      obtain ⟨w, hw⟩ :=
        (hacyc.isTree_connectedComponent C).exists_vert_degree_one_of_nontrivial
      have hwDegree : G.degree w.1 = 1 := by
        apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
        obtain ⟨z, hwz, hzUnique⟩ :=
          SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hw
        refine ⟨z.1, (C.toSimpleGraph_adj w.2 z.2).mp hwz, ?_⟩
        intro q hwq
        have hqC : q ∈ C := C.mem_supp_of_adj_mem_supp w.2 hwq
        let qC : C := ⟨q, hqC⟩
        have hwqC : C.toSimpleGraph.Adj w qC :=
          (C.toSimpleGraph_adj w.2 hqC).mpr hwq
        exact congrArg Subtype.val (hzUnique qC hwqC)
      rcases heven w.1 with ⟨k, hk⟩
      rw [hwDegree] at hk
      omega

/-! ## Abstract finite cycle--cut duality -/

/-- An unordered pair crosses a vertex set when exactly one endpoint belongs
to the set. -/
def sym2CrossesSet {V : Type*} (C : Set V) : Sym2 V → Prop :=
  Sym2.lift ⟨fun u v =>
    (u ∈ C ∧ v ∉ C) ∨ (v ∈ C ∧ u ∉ C), by
      intro u v
      apply propext
      aesop⟩

@[simp] theorem sym2CrossesSet_mk {V : Type*} (C : Set V) (u v : V) :
    sym2CrossesSet C s(u, v) ↔
      (u ∈ C ∧ v ∉ C) ∨ (v ∈ C ∧ u ∉ C) :=
  Iff.rfl

/-- The labels of a multigraph crossing a displayed vertex cut. -/
noncomputable def cutLabels
    {V E : Type*} [Fintype E] (G : LabeledMultigraph V E)
    (C : Set V) : Finset E := by
  classical
  exact Finset.univ.filter fun e => sym2CrossesSet C (G.ends e)

@[simp] theorem mem_cutLabels
    {V E : Type*} [Fintype E] (G : LabeledMultigraph V E)
    (C : Set V) (e : E) :
    e ∈ cutLabels G C ↔ sym2CrossesSet C (G.ends e) := by
  classical
  simp [cutLabels]

/-- A connected finite labelled graph has a cut label across every
nontrivial partition of its vertices. -/
theorem cutLabels_nonempty_of_connected
    {V E : Type*} [Fintype E] (G : LabeledMultigraph V E)
    (hconn : G.Connected) (C : Set V)
    (hC : C.Nonempty) (hCcompl : Cᶜ.Nonempty) :
    (cutLabels G C).Nonempty := by
  classical
  rcases hC with ⟨a, ha⟩
  rcases hCcompl with ⟨b, hb⟩
  have hb' : b ∉ C := hb
  have hcross : ∃ u v, u ∈ C ∧ v ∉ C ∧ G.toSimpleGraph.Adj u v := by
    by_contra hnone
    have hpreserve : ∀ {u v}, G.toSimpleGraph.Adj u v → u ∈ C → v ∈ C := by
      intro u v huv hu
      by_contra hv
      exact hnone ⟨u, v, hu, hv, huv⟩
    have hab := hconn.preconnected a b
    rw [SimpleGraph.reachable_iff_reflTransGen] at hab
    have hmem : ∀ {x y},
        Relation.ReflTransGen G.toSimpleGraph.Adj x y → x ∈ C → y ∈ C := by
      intro x y hxy hx
      induction hxy with
      | refl => exact hx
      | tail _ hyz ih => exact hpreserve hyz ih
    have hbC : b ∈ C := hmem hab ha
    exact hb' hbC
  rcases hcross with ⟨u, v, hu, hv, huv⟩
  rcases huv with ⟨_, e, he⟩
  refine ⟨e, (mem_cutLabels G C e).mpr ?_⟩
  rw [he]
  exact Or.inl ⟨hu, hv⟩

/-- The component cut of a selected edge set contains no selected label.
Equivalently, every label crossing such a component belongs to the
complement of the selected set. -/
theorem cutLabels_component_disjoint
    {V E : Type*} [Fintype E] (G : LabeledMultigraph V E)
    (F : Finset E)
    (c : (G.simpleGraphOn (F : Set E)).ConnectedComponent) :
    Disjoint (cutLabels G c.supp) F := by
  classical
  rw [Finset.disjoint_left]
  intro e heCut heF
  induction hends : G.ends e using Sym2.inductionOn with
  | _ u v =>
      have hcross :
          (u ∈ c.supp ∧ v ∉ c.supp) ∨
            (v ∈ c.supp ∧ u ∉ c.supp) := by
        simpa [hends] using (mem_cutLabels G c.supp e).mp heCut
      have huv : u ≠ v := by
        rcases hcross with h | h
        · exact fun huv => h.2 (huv ▸ h.1)
        · exact fun huv => h.2 (huv ▸ h.1)
      have hadj : (G.simpleGraphOn (F : Set E)).Adj u v :=
        ⟨huv, e, heF, hends⟩
      exact hcross.elim
        (fun h => h.2 (c.mem_supp_of_adj_mem_supp h.1 hadj))
        (fun h => h.2 (c.mem_supp_of_adj_mem_supp h.1 hadj.symm))

/-- Selected labels incident with a displayed vertex.  Unlike simple-graph
degree, this retains parallel labels, which is essential at the exterior
vertex of the rectangular dual. -/
abbrev SelectedIncidentLabels
    {V E : Type*} (G : LabeledMultigraph V E)
    (F : Finset E) (v : V) :=
  {e : E // e ∈ F ∧ v ∈ G.ends e}

/-- Inside a labelled spanning tree, incident selected labels are in
bijection with the neighbors in the supported simple subgraph.  Parallel
labels cannot collide because a labelled tree has injective selected
endpoints. -/
noncomputable def selectedIncidentEquivNeighborSetOfSubsetTree
    {V E : Type*} [Fintype V] [Fintype E]
    (G : LabeledMultigraph V E)
    (T B : Finset E) (hT : G.IsSpanningTree T) (hBT : B ⊆ T) (v : V) :
    SelectedIncidentLabels G B v ≃
      (G.simpleGraphOn (B : Set E)).neighborSet v := by
  classical
  let hloopB : ∀ e ∈ B, ¬G.IsLoop e :=
    fun e he => hT.loopless (hBT he)
  let toIncidence : SelectedIncidentLabels G B v →
      (G.simpleGraphOn (B : Set E)).incidenceSet v := fun e =>
    ⟨G.ends e.1,
      (G.selectedEndpoint B hloopB ⟨e.1, e.2.1⟩).2,
      e.2.2⟩
  have hinj : Function.Injective toIncidence := by
    intro e f hef
    apply Subtype.ext
    have hends : G.ends e.1 = G.ends f.1 :=
      congrArg (fun p : (G.simpleGraphOn (B : Set E)).incidenceSet v => p.1) hef
    have hsub : (⟨e.1, hBT e.2.1⟩ : LabeledMultigraph.SelectedEdge T) =
        ⟨f.1, hBT f.2.1⟩ := IsSpanningTree.ends_injective G hT hends
    exact congrArg
      (fun q : LabeledMultigraph.SelectedEdge T => q.1) hsub
  have hsurj : Function.Surjective toIncidence := by
    intro p
    let pEdge : (G.simpleGraphOn (B : Set E)).edgeSet := ⟨p.1, p.2.1⟩
    rcases G.selectedEndpoint_surjective B hloopB pEdge with ⟨e, he⟩
    have hends : G.ends e.1 = p.1 := congrArg Subtype.val he
    let e' : SelectedIncidentLabels G B v :=
      ⟨e.1, e.2, hends.symm ▸ p.2.2⟩
    refine ⟨e', ?_⟩
    apply Subtype.ext
    exact hends
  exact (Equiv.ofBijective toIncidence ⟨hinj, hsurj⟩).trans
    ((G.simpleGraphOn (B : Set E)).incidenceSetEquivNeighborSet v)

/-- `G` has even labelled boundary along every cut of `H`.  This is the
finite cycle--cut orthogonality condition, stated only in terms of the
explicit common edge labels. -/
def CutBoundaryEven
    {VG VH E : Type*} [Fintype E]
    (G : LabeledMultigraph VG E) (H : LabeledMultigraph VH E) : Prop :=
  ∀ (C : Set VH) (v : VG),
    Even (Nat.card (SelectedIncidentLabels G (cutLabels H C) v))

/-- Under cut-boundary parity, the complement in `H` of a spanning tree of
`G` is connected.  A disconnected component would give a nonempty even
subgraph inside the tree. -/
theorem complement_connected_of_cutBoundaryEven
    {VG VH E : Type*} [Fintype VG] [Fintype VH] [Fintype E]
    [DecidableEq E]
    (G : LabeledMultigraph VG E) (H : LabeledMultigraph VH E)
    (hGloop : ∀ e, ¬G.IsLoop e)
    (hHconn : H.Connected)
    (hEven : CutBoundaryEven G H)
    (F : Finset E) (hF : G.IsSpanningTree F) :
    (H.simpleGraphOn ((Finset.univ \ F : Finset E) : Set E)).Connected := by
  classical
  let K := H.simpleGraphOn ((Finset.univ \ F : Finset E) : Set E)
  letI : Nonempty VH := hHconn.nonempty
  refine { preconnected := ?_ }
  intro a b
  by_contra hab
  let c := K.connectedComponentMk a
  have haC : a ∈ c.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hbC : b ∉ c.supp := by
    intro hb
    exact hab (c.reachable_of_mem_supp haC hb)
  have hcutNonempty : (cutLabels H c.supp).Nonempty :=
    cutLabels_nonempty_of_connected H hHconn c.supp
      ⟨a, haC⟩ ⟨b, hbC⟩
  have hcutSubset : cutLabels H c.supp ⊆ F := by
    intro e he
    by_contra heF
    have heComp : e ∈ Finset.univ \ F := by simp [heF]
    exact Finset.disjoint_left.mp
      (cutLabels_component_disjoint H (Finset.univ \ F) c) he heComp
  let B := G.simpleGraphOn (cutLabels H c.supp : Set E)
  have hBne : B ≠ ⊥ := by
    rcases hcutNonempty with ⟨e, he⟩
    induction hends : G.ends e using Sym2.inductionOn with
    | _ u v =>
        have huv : u ≠ v := by
          intro huv
          subst v
          exact hGloop e
            ((G.isLoop_iff_exists_isLoopAt e).mpr ⟨u, hends⟩)
        intro hbot
        have hadj : B.Adj u v := ⟨huv, e, he, hends⟩
        rw [hbot] at hadj
        exact hadj
  have hBeven : ∀ v, Even (B.degree v) := by
    intro v
    rw [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card]
    rw [← Nat.card_congr
      (selectedIncidentEquivNeighborSetOfSubsetTree G F
        (cutLabels H c.supp) hF hcutSubset v)]
    exact hEven c.supp v
  have hBacyclic : B.IsAcyclic := by
    apply SimpleGraph.IsAcyclic.anti
      (G.simpleGraphOn_mono hcutSubset)
    exact hF.toSimpleGraph_isTree.isAcyclic
  exact (not_isAcyclic_of_nonempty_even_degree B hBne hBeven) hBacyclic

/-- Bidirectional cut parity and the planar Euler cardinality identity imply
the full labelled spanning-tree complement law.  This is the finite
cycle--cut theorem needed below; all topology has been isolated into the two
`CutBoundaryEven` hypotheses. -/
theorem treeComplementLaw_of_cutBoundaryEven
    {VG VH E : Type*} [Fintype VG] [Fintype VH] [Fintype E]
    [DecidableEq E]
    (G : LabeledMultigraph VG E) (H : LabeledMultigraph VH E)
    (hGloop : ∀ e, ¬G.IsLoop e) (hHloop : ∀ e, ¬H.IsLoop e)
    (hGconn : G.Connected) (hHconn : H.Connected)
    (hEuler : Fintype.card E + 2 = Fintype.card VG + Fintype.card VH)
    (hGH : CutBoundaryEven G H) (hHG : CutBoundaryEven H G) :
    ∀ F : Finset E,
      G.IsSpanningTree F ↔ H.IsSpanningTree (Finset.univ \ F) := by
  intro F
  constructor
  · intro hF
    refine ⟨fun e _ => hHloop e,
      complement_connected_of_cutBoundaryEven G H hGloop hHconn hGH F hF,
      ?_⟩
    have hcompl : (Finset.univ \ F).card = Fintype.card E - F.card := by
      rw [Finset.card_sdiff]
      simp
    have hFcard := hF.card_edges_add_one
    have hFle : F.card ≤ Fintype.card E := by
      simpa using Finset.card_le_univ F
    omega
  · intro hT
    refine ⟨fun e _ => hGloop e, ?_, ?_⟩
    · have hconn := complement_connected_of_cutBoundaryEven H G hHloop
          hGconn hHG (Finset.univ \ F) hT
      simpa using hconn
    · have hcompl : (Finset.univ \ F).card = Fintype.card E - F.card := by
        rw [Finset.card_sdiff]
        simp
      have hTcard := hT.card_edges_add_one
      have hFle : F.card ≤ Fintype.card E := by
        simpa using Finset.card_le_univ F
      omega

/-- For a nondegenerate rectangle, the only remaining geometric obligations
for planar tree complementation are the two explicit local cut-parity laws. -/
theorem rectangleTreeComplementLaw_of_cutBoundaryEven
    {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hPrimalBoundary :
      CutBoundaryEven (rectanglePrimal r s) (rectangleDual r s))
    (hDualBoundary :
      CutBoundaryEven (rectangleDual r s) (rectanglePrimal r s)) :
    RectangleTreeComplementLaw r s := by
  apply treeComplementLaw_of_cutBoundaryEven
    (rectanglePrimal r s) (rectangleDual r s)
    rectanglePrimal_not_isLoop (rectangleDual_not_isLoop hr hs)
    (rectanglePrimal_connected (by omega) (by omega))
    (rectangleDual_connected hr hs)
  · simp only [card_rectangleEdge, Fintype.card_prod, Fintype.card_fin,
      card_rectangleDualVertex]
    have hr₁ : r - 1 + 1 = r := by omega
    have hs₁ : s - 1 + 1 = s := by omega
    nlinarith
  · exact hPrimalBoundary
  · exact hDualBoundary

/-! ## Explicit boundary-deletion cotrees -/

/-- Embed a vertex of the canonical boundary-deleted integer grid into the
natural-coordinate primal rectangle. -/
noncomputable def canonicalBoundaryDeletionToPrimal
    (R S : ℕ) (A : Finset Point) :
    {p : Point // p ∈ rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalBoundary R S A} ↪
      (Fin (R + 1) × Fin (S + 1)) where
  toFun p := standardRectangleEquivFin (R + 1) (S + 1)
    ⟨p.1, (Finset.mem_sdiff.mp p.2).1⟩
  inj' := by
    intro p q hpq
    apply Subtype.ext
    have hfull := (standardRectangleEquivFin (R + 1) (S + 1)).injective hpq
    exact congrArg
      (fun z : {p : Point // p ∈ rectangle 0 0 (R + 1) (S + 1)} => z.1)
      hfull

/-- The ambient primal labels selected by a simple spanning tree of the
canonical boundary-deleted grid.  The tree is first embedded in the full
natural-coordinate rectangle, then unique primal labels are recovered from
its unordered edges. -/
noncomputable def canonicalBoundaryPrimalTreeLabels
    (R S : ℕ) (A : Finset Point)
    (T : SimpleSpanningTreeType
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A))) :
    Finset (RectangleEdge (R + 1) (S + 1)) :=
  labelsOfSimpleSubgraph (rectanglePrimal (R + 1) (S + 1))
    (T.1.map (canonicalBoundaryDeletionToPrimal R S A))

/-- Complement the embedded primal-tree labels and discard precisely the
labels that became loops in the canonical dual contraction. -/
noncomputable def canonicalBoundaryContractedCotree
    (R S : ℕ) (A : Finset Point)
    (T : SimpleSpanningTreeType
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A))) :
    Finset ((rectangleDual (R + 1) (S + 1)).contractWithLoops
      (canonicalBoundaryDualEdges R S A)).NonLoopEdge := by
  classical
  exact Finset.univ.filter fun e =>
    e.1 ∉ canonicalBoundaryPrimalTreeLabels R S A T

@[simp] theorem mem_canonicalBoundaryContractedCotree
    (R S : ℕ) (A : Finset Point)
    (T : SimpleSpanningTreeType
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A)))
    (e : ((rectangleDual (R + 1) (S + 1)).contractWithLoops
      (canonicalBoundaryDualEdges R S A)).NonLoopEdge) :
    e ∈ canonicalBoundaryContractedCotree R S A T ↔
      e.1 ∉ canonicalBoundaryPrimalTreeLabels R S A T := by
  classical
  simp [canonicalBoundaryContractedCotree]

/-- The narrow deletion/contraction cycle--cut law.  It requires that the
explicit contracted cotree above is always a tree and that this explicit map
is bijective.  No arbitrary tree equivalence is hidden in the interface. -/
structure BoundaryVacancyTreeComplementLaw
    (R S : ℕ) (A : Finset Point) : Prop where
  cotree_isTree : ∀ T,
    (canonicalBoundaryContractedDual R S A).IsSpanningTree
      (canonicalBoundaryContractedCotree R S A T)
  cotree_bijective : Function.Bijective (fun T =>
    (⟨canonicalBoundaryContractedCotree R S A T,
      cotree_isTree T⟩ : (canonicalBoundaryContractedDual R S A).SpanningTree))

/-- The explicit deletion/contraction complement law gives exactly the
vacancy-tree equivalence required by `BoundaryPlanarTreeComplement`. -/
noncomputable def boundaryVacancyTreeEquivOfComplementLaw
    (R S : ℕ) (A : Finset Point)
    (h : BoundaryVacancyTreeComplementLaw R S A) :
    SimpleSpanningTreeType
        (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
          Boundary.canonicalBoundary R S A)) ≃
      (canonicalBoundaryContractedDual R S A).SpanningTree :=
  Equiv.ofBijective
    (fun T => (⟨canonicalBoundaryContractedCotree R S A T,
      h.cotree_isTree T⟩ : (canonicalBoundaryContractedDual R S A).SpanningTree))
    h.cotree_bijective

/-- The spanning-tree subtype is independent of the chosen finite
enumeration of its vertex type.  This explicit equivalence is useful at
module boundaries where two canonical `Fintype` constructions coexist. -/
noncomputable def spanningTreeEquivOfFintype
    {V E : Type*} [Finite E] (G : LabeledMultigraph V E)
    (i j : Fintype V) :
    @LabeledMultigraph.SpanningTree V E G i inferInstance ≃
      @LabeledMultigraph.SpanningTree V E G j inferInstance := by
  have hcard : @Fintype.card V i = @Fintype.card V j :=
    @Fintype.card_congr V V i j (Equiv.refl V)
  refine
    { toFun := fun T => ⟨T.1, ?_⟩
      invFun := fun T => ⟨T.1, ?_⟩
      left_inv := fun T => Subtype.ext rfl
      right_inv := fun T => Subtype.ext rfl }
  · change (∀ e ∈ T.1, ¬G.IsLoop e) ∧
      (G.simpleGraphOn (T.1 : Set E)).Connected ∧
        T.1.card + 1 = @Fintype.card V j
    rw [← hcard]
    exact T.2
  · change (∀ e ∈ T.1, ¬G.IsLoop e) ∧
      (G.simpleGraphOn (T.1 : Set E)).Connected ∧
        T.1.card + 1 = @Fintype.card V i
    rw [hcard]
    exact T.2

/-- Standard-instance wrapper for clients using the generic contraction
component `Fintype`, rather than the boundary presentation's local finite
enumeration. -/
noncomputable def boundaryVacancyTreeEquivOfComplementLawStandard
    (R S : ℕ) (A : Finset Point)
    (h : BoundaryVacancyTreeComplementLaw R S A) :
    SimpleSpanningTreeType
        (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
          Boundary.canonicalBoundary R S A)) ≃
      @LabeledMultigraph.SpanningTree
        (CanonicalBoundaryContractedVertex R S A)
        ((rectangleDual (R + 1) (S + 1)).contractWithLoops
          (canonicalBoundaryDualEdges R S A)).NonLoopEdge
        (canonicalBoundaryContractedDual R S A)
        ((rectangleDual (R + 1) (S + 1)).contractionComponentFintype
          (canonicalBoundaryDualEdges R S A)) inferInstance :=
  (boundaryVacancyTreeEquivOfComplementLaw R S A h).trans
    (spanningTreeEquivOfFintype (canonicalBoundaryContractedDual R S A)
      (canonicalBoundaryContractedVertexFintype R S A)
      ((rectangleDual (R + 1) (S + 1)).contractionComponentFintype
        (canonicalBoundaryDualEdges R S A)))

@[simp] theorem mem_boundaryVacancyTreeEquivOfComplementLaw
    (R S : ℕ) (A : Finset Point)
    (h : BoundaryVacancyTreeComplementLaw R S A)
    (T : SimpleSpanningTreeType
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A)))
    (e : ((rectangleDual (R + 1) (S + 1)).contractWithLoops
      (canonicalBoundaryDualEdges R S A)).NonLoopEdge) :
    e ∈ (boundaryVacancyTreeEquivOfComplementLaw R S A h T).1 ↔
      e.1 ∉ canonicalBoundaryPrimalTreeLabels R S A T := by
  exact mem_canonicalBoundaryContractedCotree R S A T e

/-- End-to-end construction of all boundary planar data from the two exact
edge-complement laws.  The contraction presentation and marked-face wiring
are supplied by the unconditional geometry proved above. -/
noncomputable def boundaryPlanarTreeComplementOfComplementLaws
    (R S : ℕ) (A : Finset Point)
    (hRectangle : RectangleTreeComplementLaw (R + 1) (S + 1))
    (hBoundary : BoundaryVacancyTreeComplementLaw R S A) :
    BoundaryPlanarTreeComplement R S A :=
  boundaryPlanarTreeComplementOfTreeEquivs R S A
    (rectangleTreeEquivOfComplementLaw R S hRectangle)
    (boundaryVacancyTreeEquivOfComplementLaw R S A hBoundary)

/-! ## Local cut parity on square faces -/

/-- Four successive unordered pairs around a square. -/
def faceSidePair {V : Type*} (southWest southEast northEast northWest : V) :
    FaceSide → Sym2 V
  | .south => s(southWest, southEast)
  | .east => s(southEast, northEast)
  | .north => s(northEast, northWest)
  | .west => s(northWest, southWest)

private def boolCrosses (a b : Bool) : Bool := a != b

private def faceSideCrossBool (a b c d : Bool) : FaceSide → Bool
  | .south => boolCrosses a b
  | .east => boolCrosses b c
  | .north => boolCrosses c d
  | .west => boolCrosses d a

private theorem even_faceSideCrossBool : ∀ a b c d,
    Even ((Finset.univ.filter fun q : FaceSide =>
      faceSideCrossBool a b c d q = true).card) := by
  decide

/-- Every cut meets a four-edge cyclic boundary an even number of times. -/
theorem even_natCard_faceSide_crossesSet
    {V : Type*} (C : Set V) (a b c d : V) :
    Even (Nat.card {q : FaceSide //
      sym2CrossesSet C (faceSidePair a b c d q)}) := by
  classical
  let ab := decide (a ∈ C)
  let bb := decide (b ∈ C)
  let cb := decide (c ∈ C)
  let db := decide (d ∈ C)
  let e : {q : FaceSide // sym2CrossesSet C (faceSidePair a b c d q)} ≃
      {q : FaceSide // faceSideCrossBool ab bb cb db q = true} :=
    Equiv.subtypeEquiv (Equiv.refl FaceSide) (by
      intro q
      cases q <;>
        simp [faceSidePair, faceSideCrossBool, boolCrosses, ab, bb, cb, db,
          sym2CrossesSet] <;> tauto)
  rw [Nat.card_congr e]
  letI : Fintype {q : FaceSide //
      faceSideCrossBool ab bb cb db q = true} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact even_faceSideCrossBool ab bb cb db

/-- Reassociate a selected incident label as an incident label satisfying a
selection predicate. -/
def selectedIncidentLabelsEquivSubtypeIncident
    {V E : Type*} (G : LabeledMultigraph V E) (F : Finset E) (v : V) :
    SelectedIncidentLabels G F v ≃
      {e : IncidentLabel G v // e.1 ∈ F} where
  toFun e := ⟨⟨e.1, e.2.2⟩, e.2.1⟩
  invFun e := ⟨e.1.1, e.2, e.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Southwest corner of a bounded face in natural primal coordinates. -/
def boundedFaceSouthWest {R S : ℕ}
    (f : BoundedFace (R + 1) (S + 1)) : Fin (R + 1) × Fin (S + 1) :=
  (⟨f.1.1, by have := f.1.2; omega⟩,
    ⟨f.2.1, by have := f.2.2; omega⟩)

/-- Southeast corner of a bounded face in natural primal coordinates. -/
def boundedFaceSouthEast {R S : ℕ}
    (f : BoundedFace (R + 1) (S + 1)) : Fin (R + 1) × Fin (S + 1) :=
  (⟨f.1.1 + 1, by have := f.1.2; omega⟩,
    ⟨f.2.1, by have := f.2.2; omega⟩)

/-- Northeast corner of a bounded face in natural primal coordinates. -/
def boundedFaceNorthEast {R S : ℕ}
    (f : BoundedFace (R + 1) (S + 1)) : Fin (R + 1) × Fin (S + 1) :=
  (⟨f.1.1 + 1, by have := f.1.2; omega⟩,
    ⟨f.2.1 + 1, by have := f.2.2; omega⟩)

/-- Northwest corner of a bounded face in natural primal coordinates. -/
def boundedFaceNorthWest {R S : ℕ}
    (f : BoundedFace (R + 1) (S + 1)) : Fin (R + 1) × Fin (S + 1) :=
  (⟨f.1.1, by have := f.1.2; omega⟩,
    ⟨f.2.1 + 1, by have := f.2.2; omega⟩)

theorem rectanglePrimal_faceSideEdge_ends
    {R S : ℕ} (f : BoundedFace (R + 1) (S + 1)) (d : FaceSide) :
    (rectanglePrimal (R + 1) (S + 1)).ends (faceSideEdge f d) =
      faceSidePair (boundedFaceSouthWest f) (boundedFaceSouthEast f)
        (boundedFaceNorthEast f) (boundedFaceNorthWest f) d := by
  cases d <;>
    simp [faceSideEdge, faceSidePair, rectanglePrimal,
      horizontalPrimalLeft, horizontalPrimalRight,
      verticalPrimalBottom, verticalPrimalTop,
      boundedFaceSouthWest, boundedFaceSouthEast,
      boundedFaceNorthEast, boundedFaceNorthWest]

/-- At a bounded dual face, selected cut labels are exactly the four cyclic
side transitions of its primal square. -/
noncomputable def boundedFaceCutIncidentEquiv
    {R S : ℕ} (C : Set (Fin (R + 1) × Fin (S + 1)))
    (f : BoundedFace (R + 1) (S + 1)) :
    SelectedIncidentLabels (rectangleDual (R + 1) (S + 1))
        (cutLabels (rectanglePrimal (R + 1) (S + 1)) C) (some f) ≃
      {d : FaceSide // sym2CrossesSet C
        (faceSidePair (boundedFaceSouthWest f) (boundedFaceSouthEast f)
          (boundedFaceNorthEast f) (boundedFaceNorthWest f) d)} := by
  let e₁ := selectedIncidentLabelsEquivSubtypeIncident
    (rectangleDual (R + 1) (S + 1))
    (cutLabels (rectanglePrimal (R + 1) (S + 1)) C) (some f)
  let e₂ := Equiv.subtypeEquivOfSubtype
    (faceSideEquivIncidentLabel f)
    (p := fun e => e.1 ∈ cutLabels (rectanglePrimal (R + 1) (S + 1)) C)
  exact e₁.trans (e₂.symm.trans
    (Equiv.subtypeEquiv (Equiv.refl FaceSide) (by
      intro d
      rw [mem_cutLabels]
      change sym2CrossesSet C
          ((rectanglePrimal (R + 1) (S + 1)).ends (faceSideEdge f d)) ↔
        sym2CrossesSet C
          (faceSidePair (boundedFaceSouthWest f) (boundedFaceSouthEast f)
            (boundedFaceNorthEast f) (boundedFaceNorthWest f) d)
      rw [rectanglePrimal_faceSideEdge_ends])) )

/-- The labelled cut degree at every bounded dual face is even. -/
theorem rectangleDual_boundedFace_cutBoundaryEven
    {R S : ℕ} (C : Set (Fin (R + 1) × Fin (S + 1)))
    (f : BoundedFace (R + 1) (S + 1)) :
    Even (Nat.card
      (SelectedIncidentLabels (rectangleDual (R + 1) (S + 1))
        (cutLabels (rectanglePrimal (R + 1) (S + 1)) C) (some f))) := by
  rw [Nat.card_congr (boundedFaceCutIncidentEquiv C f)]
  exact even_natCard_faceSide_crossesSet C
    (boundedFaceSouthWest f) (boundedFaceSouthEast f)
    (boundedFaceNorthEast f) (boundedFaceNorthWest f)

/-! ## Labelled handshake parity -/

/-- Swap the order of choosing a vertex and an incident selected label. -/
def sigmaSelectedIncidentLabelsEquiv
    {V E : Type*} (G : LabeledMultigraph V E) (B : Finset E) :
    (Σ v, SelectedIncidentLabels G B v) ≃
      (Σ e : {e : E // e ∈ B}, {v : V // v ∈ G.ends e.1}) where
  toFun x := ⟨⟨x.2.1, x.2.2.1⟩, ⟨x.1, x.2.2.2⟩⟩
  invFun x := ⟨x.2.1, ⟨x.1.1, x.1.2, x.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A nonloop unordered endpoint pair contains exactly two vertices. -/
theorem natCard_vertex_mem_ends_eq_two
    {V E : Type*} (G : LabeledMultigraph V E) (e : E)
    (he : ¬G.IsLoop e) :
    Nat.card {v : V // v ∈ G.ends e} = 2 := by
  classical
  let q := G.ends e
  let eqv : {v : V // v ∈ q} ≃ ↥q.toFinset :=
    Equiv.subtypeEquiv (Equiv.refl V) (by intro v; simp)
  calc
    Nat.card {v : V // v ∈ G.ends e} = Nat.card {v : V // v ∈ q} := rfl
    _ = Nat.card ↥q.toFinset := Nat.card_congr eqv
    _ = q.toFinset.card := Nat.card_eq_finsetCard q.toFinset
    _ = 2 := Sym2.card_toFinset_of_not_isDiag q he

/-- Labelled handshaking: every selected nonloop label contributes once at
each of its two endpoints, including when other labels are parallel. -/
theorem sum_natCard_selectedIncidentLabels_eq_twice_card
    {V E : Type*} [Fintype V] [Fintype E]
    (G : LabeledMultigraph V E) (B : Finset E)
    (hloop : ∀ e ∈ B, ¬G.IsLoop e) :
    (∑ v, Nat.card (SelectedIncidentLabels G B v)) = 2 * B.card := by
  classical
  rw [← Nat.card_sigma]
  rw [Nat.card_congr (sigmaSelectedIncidentLabelsEquiv G B), Nat.card_sigma]
  calc
    (∑ e : {e : E // e ∈ B}, Nat.card {v : V // v ∈ G.ends e.1}) =
        ∑ _e : {e : E // e ∈ B}, 2 := by
      apply Finset.sum_congr rfl
      intro e _
      exact natCard_vertex_mem_ends_eq_two G e.1 (hloop e.1 e.2)
    _ = 2 * B.card := by simp [Nat.mul_comm]

/-- The labelled cut degree at the exterior dual face is even.  All bounded
face degrees are even by the local square argument, while labelled
handshaking says that their sum together with the exterior degree is even.
This deliberately counts boundary-parallel labels separately. -/
theorem rectangleDual_exterior_cutBoundaryEven
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    (C : Set (Fin (R + 1) × Fin (S + 1))) :
    Even (Nat.card
      (SelectedIncidentLabels (rectangleDual (R + 1) (S + 1))
        (cutLabels (rectanglePrimal (R + 1) (S + 1)) C) none)) := by
  classical
  let B := cutLabels (rectanglePrimal (R + 1) (S + 1)) C
  let count : Option (BoundedFace (R + 1) (S + 1)) → ℕ := fun v =>
    Nat.card (SelectedIncidentLabels (rectangleDual (R + 1) (S + 1)) B v)
  have htotal : (∑ v, count v) = 2 * B.card := by
    exact sum_natCard_selectedIncidentLabels_eq_twice_card
      (rectangleDual (R + 1) (S + 1)) B
      (fun e _ => rectangleDual_not_isLoop (by omega) (by omega) e)
  have htotalEven : Even (∑ v, count v) := by
    rw [htotal]
    exact even_two_mul B.card
  rw [Fintype.sum_option] at htotalEven
  have hboundedEven : Even (∑ f, count (some f)) := by
    apply Finset.even_sum
    intro f _
    exact rectangleDual_boundedFace_cutBoundaryEven C f
  exact (Nat.even_add.mp htotalEven).mpr hboundedEven

/-- Every primal cut has even labelled boundary at every dual vertex,
including the exterior vertex with its parallel perimeter labels. -/
theorem rectangleDual_primalCutBoundaryEven
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) :
    CutBoundaryEven
      (rectangleDual (R + 1) (S + 1))
      (rectanglePrimal (R + 1) (S + 1)) := by
  intro C v
  cases v with
  | none => exact rectangleDual_exterior_cutBoundaryEven hR hS C
  | some f => exact rectangleDual_boundedFace_cutBoundaryEven C f

/-! ## Local cut parity around primal vertices -/

/-- The southwest dual sector around a primal vertex; outside the rectangle
all sectors are represented by the single exterior face. -/
def primalVertexSouthWestFace {R S : ℕ}
    (p : Fin (R + 1) × Fin (S + 1)) :
    Option (BoundedFace (R + 1) (S + 1)) :=
  if hx : p.1.1 = 0 then none
  else if hy : p.2.1 = 0 then none
  else some
    (⟨p.1.1 - 1, by have := p.1.2; omega⟩,
      ⟨p.2.1 - 1, by have := p.2.2; omega⟩)

/-- The southeast dual sector around a primal vertex. -/
def primalVertexSouthEastFace {R S : ℕ}
    (p : Fin (R + 1) × Fin (S + 1)) :
    Option (BoundedFace (R + 1) (S + 1)) :=
  if hx : p.1.1 < R then
    if hy : p.2.1 = 0 then none
    else some
      (⟨p.1.1, by omega⟩,
        ⟨p.2.1 - 1, by have := p.2.2; omega⟩)
  else none

/-- The northeast dual sector around a primal vertex. -/
def primalVertexNorthEastFace {R S : ℕ}
    (p : Fin (R + 1) × Fin (S + 1)) :
    Option (BoundedFace (R + 1) (S + 1)) :=
  if hx : p.1.1 < R then
    if hy : p.2.1 < S then some (⟨p.1.1, hx⟩, ⟨p.2.1, hy⟩)
    else none
  else none

/-- The northwest dual sector around a primal vertex. -/
def primalVertexNorthWestFace {R S : ℕ}
    (p : Fin (R + 1) × Fin (S + 1)) :
    Option (BoundedFace (R + 1) (S + 1)) :=
  if hx : p.1.1 = 0 then none
  else if hy : p.2.1 < S then
    some (⟨p.1.1 - 1, by have := p.1.2; omega⟩, ⟨p.2.1, hy⟩)
  else none

/-- The possibly missing primal edge in each cyclic direction around a
primal vertex.  Directions use the same cyclic order as `faceSidePair`:
south, east, north, west. -/
def primalVertexSideEdge {R S : ℕ}
    (p : Fin (R + 1) × Fin (S + 1)) :
    FaceSide → Option (RectangleEdge (R + 1) (S + 1))
  | .south =>
      if hy : p.2.1 = 0 then none
      else some (.vertical
        ⟨p.1, ⟨p.2.1 - 1, by have := p.2.2; omega⟩⟩)
  | .east =>
      if hx : p.1.1 < R then some (.horizontal ⟨⟨p.1.1, hx⟩, p.2⟩)
      else none
  | .north =>
      if hy : p.2.1 < S then some (.vertical ⟨p.1, ⟨p.2.1, hy⟩⟩)
      else none
  | .west =>
      if hx : p.1.1 = 0 then none
      else some (.horizontal
        ⟨⟨p.1.1 - 1, by have := p.1.2; omega⟩, p.2⟩)

/-- Any displayed side edge is genuinely incident with the central primal
vertex. -/
theorem primalVertexSideEdge_incident
    {R S : ℕ} (p : Fin (R + 1) × Fin (S + 1)) (d : FaceSide)
    {e : RectangleEdge (R + 1) (S + 1)}
    (he : primalVertexSideEdge p d = some e) :
    p ∈ (rectanglePrimal (R + 1) (S + 1)).ends e := by
  cases d with
  | south =>
      simp only [primalVertexSideEdge] at he
      split at he
      · contradiction
      · simp only [Option.some.injEq] at he
        subst e
        simp only [rectanglePrimal, verticalPrimalBottom, verticalPrimalTop,
          Sym2.mem_iff]
        right
        apply Prod.ext
        · rfl
        · apply Fin.ext
          change p.2.1 = p.2.1 - 1 + 1
          omega
  | east =>
      simp only [primalVertexSideEdge] at he
      split at he
      · simp only [Option.some.injEq] at he
        subst e
        simp [rectanglePrimal, horizontalPrimalLeft]
      · contradiction
  | north =>
      simp only [primalVertexSideEdge] at he
      split at he
      · simp only [Option.some.injEq] at he
        subst e
        simp [rectanglePrimal, verticalPrimalBottom]
      · contradiction
  | west =>
      simp only [primalVertexSideEdge] at he
      split at he
      · contradiction
      · simp only [Option.some.injEq] at he
        subst e
        simp only [rectanglePrimal, horizontalPrimalLeft, horizontalPrimalRight,
          Sym2.mem_iff]
        right
        apply Prod.ext
        · apply Fin.ext
          change p.1.1 = p.1.1 - 1 + 1
          omega
        · rfl

/-- The two dual faces of a displayed primal side edge are exactly its two
successive sectors around the central primal vertex. -/
theorem primalVertexSideEdge_dual_ends
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    (p : Fin (R + 1) × Fin (S + 1)) (d : FaceSide)
    {e : RectangleEdge (R + 1) (S + 1)}
    (he : primalVertexSideEdge p d = some e) :
    (rectangleDual (R + 1) (S + 1)).ends e =
      faceSidePair (primalVertexSouthWestFace p)
        (primalVertexSouthEastFace p) (primalVertexNorthEastFace p)
        (primalVertexNorthWestFace p) d := by
  cases d with
  | south =>
      simp only [primalVertexSideEdge] at he
      split at he
      · contradiction
      · rename_i hy
        simp only [Option.some.injEq] at he
        subst e
        by_cases hx0 : p.1.1 = 0
        · have hx : p.1.1 < R := by omega
          have hxright : p.1.1 + 1 < R + 1 := by omega
          have hpzero : p.1 = 0 := Fin.ext hx0
          have hRpos : 0 < R := by omega
          simp [rectangleDual, faceSidePair, verticalLeft, verticalRight,
            primalVertexSouthWestFace, primalVertexSouthEastFace,
            hpzero, hRpos, hy]
        · by_cases hx : p.1.1 < R
          · have hpnonzero : p.1 ≠ 0 := by
              intro hp
              apply hx0
              simpa using congrArg Fin.val hp
            simp [rectangleDual, faceSidePair, verticalLeft, verticalRight,
              primalVertexSouthWestFace, primalVertexSouthEastFace,
              hx0, hx, hpnonzero, hy]
          · have hpnonzero : p.1 ≠ 0 := by
              intro hp
              apply hx0
              simpa using congrArg Fin.val hp
            simp [rectangleDual, faceSidePair, verticalLeft, verticalRight,
              primalVertexSouthWestFace, primalVertexSouthEastFace,
              hx0, hx, hpnonzero, hy]
  | east =>
      simp only [primalVertexSideEdge] at he
      split at he
      · rename_i hx
        simp only [Option.some.injEq] at he
        subst e
        by_cases hy0 : p.2.1 = 0
        · have hy : p.2.1 < S := by omega
          have hyabove : p.2.1 + 1 < S + 1 := by omega
          have hpzero : p.2 = 0 := Fin.ext hy0
          have hSpos : 0 < S := by omega
          simp [rectangleDual, faceSidePair, horizontalBelow, horizontalAbove,
            primalVertexSouthEastFace, primalVertexNorthEastFace,
            hx, hpzero, hSpos]
        · by_cases hy : p.2.1 < S
          · have hpnonzero : p.2 ≠ 0 := by
              intro hp
              apply hy0
              simpa using congrArg Fin.val hp
            simp [rectangleDual, faceSidePair, horizontalBelow, horizontalAbove,
              primalVertexSouthEastFace, primalVertexNorthEastFace,
              hx, hy0, hy, hpnonzero]
          · have hpnonzero : p.2 ≠ 0 := by
              intro hp
              apply hy0
              simpa using congrArg Fin.val hp
            simp [rectangleDual, faceSidePair, horizontalBelow, horizontalAbove,
              primalVertexSouthEastFace, primalVertexNorthEastFace,
              hx, hy0, hy, hpnonzero]
      · contradiction
  | north =>
      simp only [primalVertexSideEdge] at he
      split at he
      · rename_i hy
        simp only [Option.some.injEq] at he
        subst e
        by_cases hx0 : p.1.1 = 0
        · have hx : p.1.1 < R := by omega
          have hxright : p.1.1 + 1 < R + 1 := by omega
          have hpzero : p.1 = 0 := Fin.ext hx0
          have hRpos : 0 < R := by omega
          simp [rectangleDual, faceSidePair, verticalLeft, verticalRight,
            primalVertexNorthEastFace, primalVertexNorthWestFace,
            hpzero, hRpos, hy]
        · by_cases hx : p.1.1 < R
          · have hpnonzero : p.1 ≠ 0 := by
              intro hp
              apply hx0
              simpa using congrArg Fin.val hp
            simp [rectangleDual, faceSidePair, verticalLeft, verticalRight,
              primalVertexNorthEastFace, primalVertexNorthWestFace,
              hx0, hx, hpnonzero, hy]
          · have hpnonzero : p.1 ≠ 0 := by
              intro hp
              apply hx0
              simpa using congrArg Fin.val hp
            simp [rectangleDual, faceSidePair, verticalLeft, verticalRight,
              primalVertexNorthEastFace, primalVertexNorthWestFace,
              hx0, hx, hpnonzero, hy]
      · contradiction
  | west =>
      simp only [primalVertexSideEdge] at he
      split at he
      · contradiction
      · rename_i hx0
        simp only [Option.some.injEq] at he
        subst e
        by_cases hy0 : p.2.1 = 0
        · have hy : p.2.1 < S := by omega
          have hyabove : p.2.1 + 1 < S + 1 := by omega
          have hpzero : p.2 = 0 := Fin.ext hy0
          have hSpos : 0 < S := by omega
          simp [rectangleDual, faceSidePair, horizontalBelow, horizontalAbove,
            primalVertexNorthWestFace, primalVertexSouthWestFace,
            hx0, hpzero, hSpos]
        · by_cases hy : p.2.1 < S
          · have hpnonzero : p.2 ≠ 0 := by
              intro hp
              apply hy0
              simpa using congrArg Fin.val hp
            simp [rectangleDual, faceSidePair, horizontalBelow, horizontalAbove,
              primalVertexNorthWestFace, primalVertexSouthWestFace,
              hx0, hy0, hy, hpnonzero]
          · have hpnonzero : p.2 ≠ 0 := by
              intro hp
              apply hy0
              simpa using congrArg Fin.val hp
            simp [rectangleDual, faceSidePair, horizontalBelow, horizontalAbove,
              primalVertexNorthWestFace, primalVertexSouthWestFace,
              hx0, hy0, hy, hpnonzero]

/-- A missing boundary side has the exterior face on both of its virtual
sides, so it can never cross a dual vertex cut. -/
theorem primalVertexSideEdge_none_pair
    {R S : ℕ}
    (p : Fin (R + 1) × Fin (S + 1)) (d : FaceSide)
    (he : primalVertexSideEdge p d = none) :
    faceSidePair (primalVertexSouthWestFace p)
        (primalVertexSouthEastFace p) (primalVertexNorthEastFace p)
        (primalVertexNorthWestFace p) d = s(none, none) := by
  cases d with
  | south =>
      simp only [primalVertexSideEdge] at he
      split at he
      · rename_i hy0
        have hpzero : p.2 = 0 := Fin.ext hy0
        simp [faceSidePair, primalVertexSouthWestFace,
          primalVertexSouthEastFace, hpzero]
      · contradiction
  | east =>
      simp only [primalVertexSideEdge] at he
      split at he
      · contradiction
      · rename_i hx
        simp [faceSidePair, primalVertexSouthEastFace,
          primalVertexNorthEastFace, hx]
  | north =>
      simp only [primalVertexSideEdge] at he
      split at he
      · contradiction
      · rename_i hy
        simp [faceSidePair, primalVertexNorthEastFace,
          primalVertexNorthWestFace, hy]
  | west =>
      simp only [primalVertexSideEdge] at he
      split at he
      · rename_i hx0
        have hpzero : p.1 = 0 := Fin.ext hx0
        simp [faceSidePair, primalVertexNorthWestFace,
          primalVertexSouthWestFace, hpzero]
      · contradiction

/-- A crossing virtual side must correspond to an actual primal edge. -/
theorem primalVertexSideEdge_isSome_of_crosses
    {R S : ℕ}
    (C : Set (Option (BoundedFace (R + 1) (S + 1))))
    (p : Fin (R + 1) × Fin (S + 1)) (d : FaceSide)
    (hcross : sym2CrossesSet C
      (faceSidePair (primalVertexSouthWestFace p)
        (primalVertexSouthEastFace p) (primalVertexNorthEastFace p)
        (primalVertexNorthWestFace p) d)) :
    (primalVertexSideEdge p d).isSome := by
  cases he : primalVertexSideEdge p d with
  | none =>
      rw [primalVertexSideEdge_none_pair p d he] at hcross
      simp [sym2CrossesSet] at hcross
  | some e => simp

/-- Two displayed directions cannot name the same primal edge. -/
theorem primalVertexSideEdge_some_injective
    {R S : ℕ} (p : Fin (R + 1) × Fin (S + 1))
    {d d' : FaceSide} {e : RectangleEdge (R + 1) (S + 1)}
    (hd : primalVertexSideEdge p d = some e)
    (hd' : primalVertexSideEdge p d' = some e) : d = d' := by
  cases d <;> cases d' <;>
    try rfl
  all_goals simp_all [primalVertexSideEdge]
  all_goals
    rcases hd with ⟨hdir, rfl⟩
    rcases hd' with ⟨hdir', h⟩
    simp at h
  case south.north =>
    have hp : p.2.1 ≠ 0 := by
      intro hp
      exact hdir (Fin.ext hp)
    omega
  case north.south =>
    have hp : p.2.1 ≠ 0 := by
      intro hp
      exact hdir' (Fin.ext hp)
    omega
  case west.east =>
    have hp : p.1.1 ≠ 0 := by
      intro hp
      exact hdir (Fin.ext hp)
    omega
  case east.west =>
    have hp : p.1.1 ≠ 0 := by
      intro hp
      exact hdir' (Fin.ext hp)
    omega

/-- Every label incident with a primal grid vertex occurs in exactly one of
the four possibly missing directions. -/
theorem primalVertexSideEdge_surjective_incident
    {R S : ℕ} (p : Fin (R + 1) × Fin (S + 1))
    (e : IncidentLabel (rectanglePrimal (R + 1) (S + 1)) p) :
    ∃ d, primalVertexSideEdge p d = some e.1 := by
  rcases e with ⟨e, he⟩
  cases e with
  | horizontal e =>
      change p ∈ s(horizontalPrimalLeft e, horizontalPrimalRight e) at he
      rcases Sym2.mem_iff.mp he with hp | hp
      · subst p
        refine ⟨FaceSide.east, ?_⟩
        have hx : e.x.1 < R := by have := e.x.2; omega
        simp [primalVertexSideEdge, horizontalPrimalLeft, hx]
      · subst p
        refine ⟨FaceSide.west, ?_⟩
        simp [primalVertexSideEdge, horizontalPrimalRight]
  | vertical e =>
      change p ∈ s(verticalPrimalBottom e, verticalPrimalTop e) at he
      rcases Sym2.mem_iff.mp he with hp | hp
      · subst p
        refine ⟨FaceSide.north, ?_⟩
        have hy : e.y.1 < S := by have := e.y.2; omega
        simp [primalVertexSideEdge, verticalPrimalBottom, hy]
      · subst p
        refine ⟨FaceSide.south, ?_⟩
        simp [primalVertexSideEdge, verticalPrimalTop]

/-- The directions at a primal vertex for which the corresponding grid edge
is present. -/
abbrev PrimalVertexPresentSide {R S : ℕ}
    (p : Fin (R + 1) × Fin (S + 1)) :=
  {d : FaceSide // (primalVertexSideEdge p d).isSome}

/-- Present cyclic directions enumerate the incident primal edge labels. -/
noncomputable def primalVertexSideEquivIncidentLabel
    {R S : ℕ} (p : Fin (R + 1) × Fin (S + 1)) :
    PrimalVertexPresentSide p ≃
      IncidentLabel (rectanglePrimal (R + 1) (S + 1)) p :=
  Equiv.ofBijective
    (fun d => ⟨(primalVertexSideEdge p d.1).get d.2,
      primalVertexSideEdge_incident p d.1 (Option.some_get d.2).symm⟩)
    ⟨by
      intro d d' h
      apply Subtype.ext
      have hval : (primalVertexSideEdge p d.1).get d.2 =
          (primalVertexSideEdge p d'.1).get d'.2 :=
        congrArg Subtype.val h
      apply primalVertexSideEdge_some_injective p
        (e := (primalVertexSideEdge p d.1).get d.2)
      · exact (Option.some_get d.2).symm
      · rw [hval]
        exact (Option.some_get d'.2).symm,
    by
      intro e
      rcases primalVertexSideEdge_surjective_incident p e with ⟨d, hd⟩
      have hpresent : (primalVertexSideEdge p d).isSome := by simp [hd]
      let q : PrimalVertexPresentSide p := ⟨d, hpresent⟩
      refine ⟨q, Subtype.ext ?_⟩
      exact Option.some_injective _ ((Option.some_get q.2).trans hd)⟩

/-- The edge selected by the present-side equivalence is the edge displayed
by that side. -/
theorem primalVertexSideEquivIncidentLabel_edge
    {R S : ℕ} (p : Fin (R + 1) × Fin (S + 1))
    (d : PrimalVertexPresentSide p) :
    primalVertexSideEdge p d.1 =
      some (primalVertexSideEquivIncidentLabel p d).1 := by
  exact (Option.some_get d.2).symm

/-- At a primal vertex, labels selected by a dual cut are exactly the cyclic
sector transitions of that cut.  Missing boundary directions disappear
automatically because their two virtual sectors are both exterior. -/
noncomputable def primalVertexCutIncidentEquiv
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    (C : Set (Option (BoundedFace (R + 1) (S + 1))))
    (p : Fin (R + 1) × Fin (S + 1)) :
    SelectedIncidentLabels (rectanglePrimal (R + 1) (S + 1))
        (cutLabels (rectangleDual (R + 1) (S + 1)) C) p ≃
      {d : FaceSide // sym2CrossesSet C
        (faceSidePair (primalVertexSouthWestFace p)
          (primalVertexSouthEastFace p) (primalVertexNorthEastFace p)
          (primalVertexNorthWestFace p) d)} := by
  let e₁ := selectedIncidentLabelsEquivSubtypeIncident
    (rectanglePrimal (R + 1) (S + 1))
    (cutLabels (rectangleDual (R + 1) (S + 1)) C) p
  let e₂ := Equiv.subtypeEquivOfSubtype
    (primalVertexSideEquivIncidentLabel p)
    (p := fun e => e.1 ∈ cutLabels (rectangleDual (R + 1) (S + 1)) C)
  let e₃ :
      {d : PrimalVertexPresentSide p //
        (primalVertexSideEquivIncidentLabel p d).1 ∈
          cutLabels (rectangleDual (R + 1) (S + 1)) C} ≃
      {d : PrimalVertexPresentSide p // sym2CrossesSet C
        (faceSidePair (primalVertexSouthWestFace p)
          (primalVertexSouthEastFace p) (primalVertexNorthEastFace p)
          (primalVertexNorthWestFace p) d.1)} :=
    Equiv.subtypeEquiv (Equiv.refl (PrimalVertexPresentSide p)) (by
      intro d
      rw [mem_cutLabels]
      change sym2CrossesSet C
          ((rectangleDual (R + 1) (S + 1)).ends
            (primalVertexSideEquivIncidentLabel p d).1) ↔
        sym2CrossesSet C
          (faceSidePair (primalVertexSouthWestFace p)
            (primalVertexSouthEastFace p) (primalVertexNorthEastFace p)
            (primalVertexNorthWestFace p) d.1)
      rw [primalVertexSideEdge_dual_ends hR hS p d.1
        (primalVertexSideEquivIncidentLabel_edge p d)])
  let e₄ :
      {d : PrimalVertexPresentSide p // sym2CrossesSet C
        (faceSidePair (primalVertexSouthWestFace p)
          (primalVertexSouthEastFace p) (primalVertexNorthEastFace p)
          (primalVertexNorthWestFace p) d.1)} ≃
      {d : FaceSide // sym2CrossesSet C
        (faceSidePair (primalVertexSouthWestFace p)
          (primalVertexSouthEastFace p) (primalVertexNorthEastFace p)
          (primalVertexNorthWestFace p) d)} :=
    Equiv.subtypeSubtypeEquivSubtype (fun {d} hd =>
      primalVertexSideEdge_isSome_of_crosses C p d hd)
  exact e₁.trans (e₂.symm.trans (e₃.trans e₄))

/-- The labelled cut degree at every primal grid vertex is even. -/
theorem rectanglePrimal_vertex_cutBoundaryEven
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    (C : Set (Option (BoundedFace (R + 1) (S + 1))))
    (p : Fin (R + 1) × Fin (S + 1)) :
    Even (Nat.card
      (SelectedIncidentLabels (rectanglePrimal (R + 1) (S + 1))
        (cutLabels (rectangleDual (R + 1) (S + 1)) C) p)) := by
  rw [Nat.card_congr (primalVertexCutIncidentEquiv hR hS C p)]
  exact even_natCard_faceSide_crossesSet C
    (primalVertexSouthWestFace p) (primalVertexSouthEastFace p)
    (primalVertexNorthEastFace p) (primalVertexNorthWestFace p)

/-- Every dual cut has even labelled boundary at every primal vertex. -/
theorem rectanglePrimal_dualCutBoundaryEven
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) :
    CutBoundaryEven
      (rectanglePrimal (R + 1) (S + 1))
      (rectangleDual (R + 1) (S + 1)) := by
  intro C p
  exact rectanglePrimal_vertex_cutBoundaryEven hR hS C p

/-- Complementing common edge labels gives the explicit primal/dual
spanning-tree equivalence for every nondegenerate rectangle. -/
theorem canonicalRectangleTreeComplementLaw
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) :
    RectangleTreeComplementLaw (R + 1) (S + 1) := by
  apply rectangleTreeComplementLaw_of_cutBoundaryEven (by omega) (by omega)
  · exact rectanglePrimal_dualCutBoundaryEven hR hS
  · exact rectangleDual_primalCutBoundaryEven hR hS

/-! ## Connectivity of deletion/contraction cotrees -/

section DeletionContractionConnectivity

noncomputable local instance planarComplementNonLoopEdgeFintype
    {V E : Type*} [Fintype E] (H : LabeledMultigraph V E) :
    Fintype H.NonLoopEdge :=
  Fintype.ofFinite _

/-- Surviving contracted labels complementary to a displayed primal label
set. -/
noncomputable def contractedComplementEdges
    {V E : Type*} [Fintype E] (H : LabeledMultigraph V E)
    (D F : Finset E) :
    Finset (H.contractWithLoops D).NonLoopEdge := by
  classical
  exact Finset.univ.filter fun e => e.1 ∉ F

@[simp] theorem mem_contractedComplementEdges
    {V E : Type*} [Fintype E] (H : LabeledMultigraph V E)
    (D F : Finset E) (e : (H.contractWithLoops D).NonLoopEdge) :
    e ∈ contractedComplementEdges H D F ↔ e.1 ∉ F := by
  classical
  simp [contractedComplementEdges]

/-- A cut in a contracted graph is the pullback cut under the component
map, label for label. -/
theorem mem_cutLabels_contract_iff
    {V E : Type*} [Fintype E] (H : LabeledMultigraph V E)
    (D : Finset E)
    (C : Set ((H.simpleGraphOn (D : Set E)).ConnectedComponent))
    (e : (H.contractWithLoops D).NonLoopEdge) :
    e ∈ cutLabels (H.contract D) C ↔
      e.1 ∈ cutLabels H (H.contractionMap D ⁻¹' C) := by
  rw [mem_cutLabels, mem_cutLabels]
  change sym2CrossesSet C
      (Sym2.map (H.contractionMap D) (H.ends e.1)) ↔
    sym2CrossesSet (H.contractionMap D ⁻¹' C) (H.ends e.1)
  induction hends : H.ends e.1 using Sym2.inductionOn with
  | _ u v => simp [sym2CrossesSet]

/-- A label crossing a pullback cut cannot collapse to a loop in the
contraction. -/
theorem not_contractWithLoops_isLoop_of_mem_pullback_cut
    {V E : Type*} [Fintype E] (H : LabeledMultigraph V E)
    (D : Finset E)
    (C : Set ((H.simpleGraphOn (D : Set E)).ConnectedComponent))
    {e : E} (he : e ∈ cutLabels H (H.contractionMap D ⁻¹' C)) :
    ¬(H.contractWithLoops D).IsLoop e := by
  rw [mem_cutLabels] at he
  induction hends : H.ends e using Sym2.inductionOn with
  | _ u v =>
      simp [hends, sym2CrossesSet] at he
      intro hloop
      change (Sym2.map (H.contractionMap D) (H.ends e)).IsDiag at hloop
      rw [hends, Sym2.map_mk, Sym2.mk_isDiag_iff] at hloop
      rcases he with h | h
      · exact h.2 (hloop ▸ h.1)
      · exact h.2 (hloop.symm ▸ h.1)

/-- With globally unique nonloop labels, selected incident labels are the
neighbors of the corresponding selected simple graph. -/
noncomputable def selectedIncidentEquivNeighborSetOfEndsInjective
    {V E : Type*} [Fintype V] [Fintype E]
    (G : LabeledMultigraph V E)
    (hloop : ∀ e, ¬G.IsLoop e)
    (hends : Function.Injective G.ends)
    (B : Finset E) (v : V) :
    SelectedIncidentLabels G B v ≃
      (G.simpleGraphOn (B : Set E)).neighborSet v := by
  classical
  let toIncidence : SelectedIncidentLabels G B v →
      (G.simpleGraphOn (B : Set E)).incidenceSet v := fun e =>
    ⟨G.ends e.1,
      (G.selectedEndpoint B (fun e _ => hloop e) ⟨e.1, e.2.1⟩).2,
      e.2.2⟩
  have hinj : Function.Injective toIncidence := by
    intro e f hef
    apply Subtype.ext
    apply hends
    exact congrArg
      (fun p : (G.simpleGraphOn (B : Set E)).incidenceSet v => p.1) hef
  have hsurj : Function.Surjective toIncidence := by
    intro p
    let pEdge : (G.simpleGraphOn (B : Set E)).edgeSet := ⟨p.1, p.2.1⟩
    rcases G.selectedEndpoint_surjective B (fun e _ => hloop e) pEdge with ⟨e, he⟩
    have hendsEq : G.ends e.1 = p.1 := congrArg Subtype.val he
    let e' : SelectedIncidentLabels G B v :=
      ⟨e.1, e.2, hendsEq.symm ▸ p.2.2⟩
    refine ⟨e', ?_⟩
    apply Subtype.ext
    exact hendsEq
  exact (Equiv.ofBijective toIncidence ⟨hinj, hsurj⟩).trans
    ((G.simpleGraphOn (B : Set E)).incidenceSetEquivNeighborSet v)

/-- The complement of an acyclic uniquely-labelled primal set is connected
after contracting arbitrary dual labels.  This is the deletion/contraction
connectivity half of planar basis duality; it needs no rank formula. -/
theorem contractedComplementEdges_connected_of_cutBoundaryEven
    {VG VH E : Type*} [Fintype VG] [Fintype VH] [Fintype E]
    (G : LabeledMultigraph VG E) (H : LabeledMultigraph VH E)
    (hGloop : ∀ e, ¬G.IsLoop e)
    (hGends : Function.Injective G.ends)
    (hHconn : H.Connected)
    (hEven : CutBoundaryEven G H)
    (D F : Finset E)
    (hFacyclic : (G.simpleGraphOn (F : Set E)).IsAcyclic) :
    ((H.contract D).simpleGraphOn
      (contractedComplementEdges H D F :
        Set (H.contractWithLoops D).NonLoopEdge)).Connected := by
  classical
  let S := contractedComplementEdges H D F
  let K := (H.contract D).simpleGraphOn
    (S : Set (H.contractWithLoops D).NonLoopEdge)
  letI : Nonempty VH := hHconn.nonempty
  letI : Nonempty ((H.simpleGraphOn (D : Set E)).ConnectedComponent) :=
    ⟨H.contractionMap D (Classical.choice inferInstance)⟩
  refine { preconnected := ?_ }
  intro a b
  by_contra hab
  let c := K.connectedComponentMk a
  have haC : a ∈ c.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hbC : b ∉ c.supp := by
    intro hb
    exact hab (c.reachable_of_mem_supp haC hb)
  let C : Set VH := H.contractionMap D ⁻¹' c.supp
  have hC : C.Nonempty := by
    refine ⟨H.contractionRep D a, ?_⟩
    change H.contractionMap D (H.contractionRep D a) ∈ c.supp
    rw [H.contractionMap_contractionRep]
    exact haC
  have hCcompl : Cᶜ.Nonempty := by
    refine ⟨H.contractionRep D b, ?_⟩
    change H.contractionMap D (H.contractionRep D b) ∉ c.supp
    rw [H.contractionMap_contractionRep]
    exact hbC
  have hcutNonempty : (cutLabels H C).Nonempty :=
    cutLabels_nonempty_of_connected H hHconn C hC hCcompl
  have hcutSubset : cutLabels H C ⊆ F := by
    intro e heCut
    have hsurvive : ¬(H.contractWithLoops D).IsLoop e :=
      not_contractWithLoops_isLoop_of_mem_pullback_cut H D c.supp heCut
    let e' : (H.contractWithLoops D).NonLoopEdge := ⟨e, hsurvive⟩
    have heCut' : e' ∈ cutLabels (H.contract D) c.supp :=
      (mem_cutLabels_contract_iff H D c.supp e').mpr heCut
    by_contra heF
    have heS : e' ∈ S :=
      (mem_contractedComplementEdges H D F e').mpr heF
    exact Finset.disjoint_left.mp
      (cutLabels_component_disjoint (H.contract D) S c) heCut' heS
  let B := G.simpleGraphOn (cutLabels H C : Set E)
  have hBne : B ≠ ⊥ := by
    rcases hcutNonempty with ⟨e, he⟩
    induction hends : G.ends e using Sym2.inductionOn with
    | _ u v =>
        have huv : u ≠ v := by
          intro huv
          subst v
          exact hGloop e
            ((G.isLoop_iff_exists_isLoopAt e).mpr ⟨u, hends⟩)
        intro hbot
        have hadj : B.Adj u v := ⟨huv, e, he, hends⟩
        rw [hbot] at hadj
        exact hadj
  have hBeven : ∀ v, Even (B.degree v) := by
    intro v
    rw [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card]
    rw [← Nat.card_congr
      (selectedIncidentEquivNeighborSetOfEndsInjective
        G hGloop hGends (cutLabels H C) v)]
    exact hEven C v
  have hBacyclic : B.IsAcyclic := by
    apply SimpleGraph.IsAcyclic.anti
      (G.simpleGraphOn_mono hcutSubset)
    exact hFacyclic
  exact (not_isAcyclic_of_nonempty_even_degree B hBne hBeven) hBacyclic

end DeletionContractionConnectivity

/-- The source graph is isomorphic to the mapped graph induced on the range
of the vertex embedding. -/
noncomputable def mapInduceRangeIso
    {V W : Type*} (G : SimpleGraph V) (f : V ↪ W) :
    G ≃g (G.map f).induce (Set.range f) where
  toEquiv := Equiv.ofInjective f f.injective
  map_rel_iff' := by
    intro u v
    simp [SimpleGraph.map_adj]

/-- Mapping a simple graph along a vertex embedding preserves acyclicity;
the ambient target vertices outside the image are merely isolated. -/
theorem SimpleGraph.IsAcyclic.map_embedding
    {V W : Type*} {G : SimpleGraph V} (hG : G.IsAcyclic)
    (f : V ↪ W) : (G.map f).IsAcyclic := by
  intro w c hc
  have hsupp : ∀ x ∈ c.support, x ∈ Set.range f := by
    intro x hx
    rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hc.not_nil] at hx
    rcases hx with ⟨e, he, hxe⟩
    have heGraph := c.edges_subset_edgeSet he
    induction e using Sym2.inductionOn with
    | _ a b =>
        have hab : (G.map f).Adj a b := heGraph
        rw [SimpleGraph.map_adj] at hab
        rcases hab with ⟨u, v, huv, hua, hvb⟩
        rw [Sym2.mem_iff] at hxe
        rcases hxe with rfl | rfl
        · exact ⟨u, hua⟩
        · exact ⟨v, hvb⟩
  let cRange := c.induce (Set.range f) hsupp
  have hcRange : cRange.IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_map
      (f := (SimpleGraph.Embedding.induce (G := G.map f)
        (Set.range f)).toHom)
    simpa [cRange] using hc
  exact ((mapInduceRangeIso G f).isAcyclic_iff.mp hG) cRange hcRange

/-- The canonical boundary-deletion embedding preserves and reflects grid
adjacency. -/
noncomputable def canonicalBoundaryDeletionPrimalGraphEmbedding
    (R S : ℕ) (A : Finset Point) :
    inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalBoundary R S A) ↪g
      (rectanglePrimal (R + 1) (S + 1)).toSimpleGraph where
  toEmbedding := canonicalBoundaryDeletionToPrimal R S A
  map_rel_iff' := by
    intro p q
    let pFull : {x : Point // x ∈ rectangle 0 0 (R + 1) (S + 1)} :=
      ⟨p.1, (Finset.mem_sdiff.mp p.2).1⟩
    let qFull : {x : Point // x ∈ rectangle 0 0 (R + 1) (S + 1)} :=
      ⟨q.1, (Finset.mem_sdiff.mp q.2).1⟩
    have h := (standardRectangleGridIso (R + 1) (S + 1)).map_rel_iff
      (a := pFull) (b := qFull)
    simpa [canonicalBoundaryDeletionToPrimal, pFull, qFull,
      inducedGrid_adj_iff, rectanglePrimal_toSimpleGraph,
      standardRectangleGridIso] using h

/-- The mapped simple tree is exactly the simple graph selected by its
recovered ambient primal labels. -/
theorem simpleGraphOn_canonicalBoundaryPrimalTreeLabels
    (R S : ℕ) (A : Finset Point)
    (T : SimpleSpanningTreeType
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A))) :
    (rectanglePrimal (R + 1) (S + 1)).simpleGraphOn
        (canonicalBoundaryPrimalTreeLabels R S A T :
          Set (RectangleEdge (R + 1) (S + 1))) =
      T.1.map (canonicalBoundaryDeletionToPrimal R S A) := by
  apply simpleGraphOn_labelsOfSimpleSubgraph
  intro u v huv
  rw [SimpleGraph.map_adj] at huv
  rcases huv with ⟨p, q, hpq, rfl, rfl⟩
  exact (canonicalBoundaryDeletionPrimalGraphEmbedding R S A).toHom.map_adj
    (T.2.1 hpq)

/-- Ambient primal labels recovered from a boundary-deleted tree are
acyclic. -/
theorem canonicalBoundaryPrimalTreeLabels_isAcyclic
    (R S : ℕ) (A : Finset Point)
    (T : SimpleSpanningTreeType
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A))) :
    ((rectanglePrimal (R + 1) (S + 1)).simpleGraphOn
      (canonicalBoundaryPrimalTreeLabels R S A T :
        Set (RectangleEdge (R + 1) (S + 1)))).IsAcyclic := by
  rw [simpleGraphOn_canonicalBoundaryPrimalTreeLabels]
  exact SimpleGraph.IsAcyclic.map_embedding T.2.2.isAcyclic
    (canonicalBoundaryDeletionToPrimal R S A)

/-- The explicit contracted cotree of every boundary-deleted primal tree is
connected.  Thus only the finite rank/basis part of deletion--contraction
duality remains for the tree equivalence. -/
theorem canonicalBoundaryContractedCotree_connected
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (A : Finset Point)
    (T : SimpleSpanningTreeType
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A))) :
    ((canonicalBoundaryContractedDual R S A).simpleGraphOn
      (canonicalBoundaryContractedCotree R S A T :
        Set ((rectangleDual (R + 1) (S + 1)).contractWithLoops
          (canonicalBoundaryDualEdges R S A)).NonLoopEdge)).Connected := by
  have hconn :=
    contractedComplementEdges_connected_of_cutBoundaryEven
      (rectanglePrimal (R + 1) (S + 1))
      (rectangleDual (R + 1) (S + 1))
      rectanglePrimal_not_isLoop
      (rectanglePrimal_ends_injective (R + 1) (S + 1))
      (rectangleDual_connected (by omega) (by omega))
      (rectanglePrimal_dualCutBoundaryEven hR hS)
      (canonicalBoundaryDualEdges R S A)
      (canonicalBoundaryPrimalTreeLabels R S A T)
      (canonicalBoundaryPrimalTreeLabels_isAcyclic R S A T)
  have hEdges :
      contractedComplementEdges
          (rectangleDual (R + 1) (S + 1))
          (canonicalBoundaryDualEdges R S A)
          (canonicalBoundaryPrimalTreeLabels R S A T) =
        canonicalBoundaryContractedCotree R S A T := by
    ext e
    rw [mem_contractedComplementEdges,
      mem_canonicalBoundaryContractedCotree]
  rw [hEdges] at hconn
  simpa only [canonicalBoundaryContractedDual] using hconn

/-! ## The finite Euler rank of the boundary cotree -/

/-- Incidence in the primal rectangle is exactly membership in the labelled
unordered endpoint pair. -/
@[simp] theorem primalIncident_iff_mem_rectanglePrimal_ends
    {r s : ℕ} (p : Fin r × Fin s) (e : RectangleEdge r s) :
    PrimalIncident p e ↔ p ∈ (rectanglePrimal r s).ends e := by
  cases e with
  | horizontal e =>
      simp [PrimalIncident, rectanglePrimal]
  | vertical e =>
      simp [PrimalIncident, rectanglePrimal]

/-- A vertex of the boundary-deleted integer grid maps to a primal vertex
outside the canonical vacancy set. -/
theorem canonicalBoundaryDeletionToPrimal_not_mem
    (R S : ℕ) (A : Finset Point)
    (p : {p : Point // p ∈ rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalBoundary R S A}) :
    canonicalBoundaryDeletionToPrimal R S A p ∉
      canonicalBoundaryPrimal R S A := by
  intro hpX
  have hzB : finPoint (canonicalBoundaryDeletionToPrimal R S A p) ∈
      canonicalBoundaryNaturalVacancies R S A :=
    mem_canonicalBoundaryPrimal.mp hpX
  have hpRect := (Finset.mem_sdiff.mp p.2).1
  have hpBounds :
      ((0 : ℤ) ≤ p.1.1 ∧ p.1.1 < (R + 1 : ℕ)) ∧
      ((0 : ℤ) ≤ p.1.2 ∧ p.1.2 < (S + 1 : ℕ)) := by
    simpa [rectangle] using hpRect
  have hpoint : Boundary.ofNatPoint
      (finPoint (canonicalBoundaryDeletionToPrimal R S A p)) = p.1 := by
    apply Prod.ext <;>
      simp [canonicalBoundaryDeletionToPrimal, finPoint,
        Boundary.ofNatPoint, hpBounds.1.1, hpBounds.2.1]
  apply (Finset.mem_sdiff.mp p.2).2
  change p.1 ∈
    (canonicalBoundaryNaturalVacancies R S A).image Boundary.ofNatPoint
  exact Finset.mem_image.mpr ⟨_, hzB, hpoint⟩

/-- Every primal label recovered from a boundary-deleted tree avoids the
labels incident with the deleted vertices. -/
theorem canonicalBoundaryPrimalTreeLabels_not_mem_dualEdges
    (R S : ℕ) (A : Finset Point)
    (T : SimpleSpanningTreeType
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A)))
    {e : RectangleEdge (R + 1) (S + 1)}
    (heT : e ∈ canonicalBoundaryPrimalTreeLabels R S A T) :
    e ∉ canonicalBoundaryDualEdges R S A := by
  intro heD
  have heEdge := (mem_labelsOfSimpleSubgraph
    (rectanglePrimal (R + 1) (S + 1))
    (T.1.map (canonicalBoundaryDeletionToPrimal R S A)) e).mp heT
  induction hends : (rectanglePrimal (R + 1) (S + 1)).ends e using
      Sym2.inductionOn with
  | _ u v =>
      have huvMap : (T.1.map (canonicalBoundaryDeletionToPrimal R S A)).Adj u v := by
        rw [← SimpleGraph.mem_edgeSet, ← hends]
        exact heEdge
      rw [SimpleGraph.map_adj] at huvMap
      rcases huvMap with ⟨p, q, hpq, rfl, rfl⟩
      rw [canonicalBoundaryDualEdges, mem_vacancyDualEdges] at heD
      rcases heD with ⟨x, hxX, hxe⟩
      have hxEnds := (primalIncident_iff_mem_rectanglePrimal_ends x e).mp hxe
      rw [hends, Sym2.mem_iff] at hxEnds
      rcases hxEnds with hx | hx
      · subst x
        exact canonicalBoundaryDeletionToPrimal_not_mem R S A p hxX
      · subst x
        exact canonicalBoundaryDeletionToPrimal_not_mem R S A q hxX

/-- A surviving edge of the dual contraction was not one of the labels
explicitly contracted. -/
theorem canonicalBoundaryNonLoopEdge_not_mem_dualEdges
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (A : Finset Point)
    (e : (rectangleDual (R + 1) (S + 1)).contractWithLoops
      (canonicalBoundaryDualEdges R S A) |>.NonLoopEdge) :
    e.1 ∉ canonicalBoundaryDualEdges R S A := by
  intro heD
  exact e.2 ((rectangleDual (R + 1) (S + 1)).contractWithLoops_isLoop_of_mem
    heD (rectangleDual_not_isLoop (by omega) (by omega) e.1))

/-- Convert an undeleted explicit primal vertex back to the corresponding
integer-coordinate vertex of the boundary-deleted grid. -/
noncomputable def canonicalBoundaryRemainingToDeletion
    (R S : ℕ) (A : Finset Point)
    (u : Fin (R + 1) × Fin (S + 1))
    (hu : u ∉ canonicalBoundaryPrimal R S A) :
    {p : Point // p ∈ rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalBoundary R S A} := by
  let z := finPoint u
  refine ⟨Boundary.ofNatPoint z, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
  · exact Boundary.ofNatPoint_mem_standardRectangle.mpr
      ⟨Nat.le_of_lt_succ u.1.2, Nat.le_of_lt_succ u.2.2⟩
  · intro hzImage
    change Boundary.ofNatPoint z ∈
      (canonicalBoundaryNaturalVacancies R S A).image Boundary.ofNatPoint at hzImage
    rcases Finset.mem_image.mp hzImage with ⟨w, hwB, hwz⟩
    have hw : w = z := Boundary.ofNatPoint_injective hwz
    subst w
    apply hu
    exact mem_canonicalBoundaryPrimal.mpr (by simpa [z] using hwB)

@[simp] theorem canonicalBoundaryDeletionToPrimal_remainingToDeletion
    (R S : ℕ) (A : Finset Point)
    (u : Fin (R + 1) × Fin (S + 1))
    (hu : u ∉ canonicalBoundaryPrimal R S A) :
    canonicalBoundaryDeletionToPrimal R S A
      (canonicalBoundaryRemainingToDeletion R S A u hu) = u := by
  apply finPoint_injective
  simp [canonicalBoundaryDeletionToPrimal,
    canonicalBoundaryRemainingToDeletion, finPoint, Boundary.ofNatPoint]

/-- Every ambient primal label not incident with a deleted vertex determines
an unordered edge of the boundary-deleted integer grid. -/
noncomputable def canonicalBoundaryAvailableEdgeToDeletion
    (R S : ℕ) (A : Finset Point)
    (e : {e : RectangleEdge (R + 1) (S + 1) //
      e ∉ canonicalBoundaryDualEdges R S A}) :
    (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalBoundary R S A)).edgeSet := by
  let uv := ((rectanglePrimal (R + 1) (S + 1)).ends e.1).out
  let u := uv.1
  let v := uv.2
  have hends : (rectanglePrimal (R + 1) (S + 1)).ends e.1 = s(u, v) := by
    exact (Quot.out_eq _).symm
  have huX : u ∉ canonicalBoundaryPrimal R S A := by
    intro hu
    apply e.2
    change e.1 ∈ vacancyDualEdges (canonicalBoundaryPrimal R S A)
    exact mem_vacancyDualEdges.mpr ⟨u, hu,
      (primalIncident_iff_mem_rectanglePrimal_ends u e.1).mpr
        (hends.symm ▸ Sym2.mem_mk_left u v)⟩
  have hvX : v ∉ canonicalBoundaryPrimal R S A := by
    intro hv
    apply e.2
    change e.1 ∈ vacancyDualEdges (canonicalBoundaryPrimal R S A)
    exact mem_vacancyDualEdges.mpr ⟨v, hv,
      (primalIncident_iff_mem_rectanglePrimal_ends v e.1).mpr
        (hends.symm ▸ Sym2.mem_mk_right u v)⟩
  let pu := canonicalBoundaryRemainingToDeletion R S A u huX
  let pv := canonicalBoundaryRemainingToDeletion R S A v hvX
  have huv : (rectanglePrimal (R + 1) (S + 1)).toSimpleGraph.Adj u v := by
    refine ⟨?_, e.1, hends⟩
    intro huvEq
    apply rectanglePrimal_not_isLoop e.1
    change ((rectanglePrimal (R + 1) (S + 1)).ends e.1).IsDiag
    rw [hends, huvEq]
    exact Sym2.diag_isDiag _
  have hpupv :
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A)).Adj pu pv := by
    apply (canonicalBoundaryDeletionPrimalGraphEmbedding R S A).map_rel_iff.mp
    change (rectanglePrimal (R + 1) (S + 1)).toSimpleGraph.Adj
      (canonicalBoundaryDeletionToPrimal R S A pu)
      (canonicalBoundaryDeletionToPrimal R S A pv)
    rw [canonicalBoundaryDeletionToPrimal_remainingToDeletion,
      canonicalBoundaryDeletionToPrimal_remainingToDeletion]
    exact huv
  exact ⟨s(pu, pv), by
    rw [SimpleGraph.mem_edgeSet]
    exact hpupv⟩

/-- Mapping the recovered deleted-grid edge forward returns the original
ambient unordered endpoint pair. -/
theorem map_canonicalBoundaryAvailableEdgeToDeletion
    (R S : ℕ) (A : Finset Point)
    (e : {e : RectangleEdge (R + 1) (S + 1) //
      e ∉ canonicalBoundaryDualEdges R S A}) :
    Sym2.map (canonicalBoundaryDeletionToPrimal R S A)
        (canonicalBoundaryAvailableEdgeToDeletion R S A e).1 =
      (rectanglePrimal (R + 1) (S + 1)).ends e.1 := by
  change Sym2.map (canonicalBoundaryDeletionToPrimal R S A)
      s(canonicalBoundaryRemainingToDeletion R S A _ _,
        canonicalBoundaryRemainingToDeletion R S A _ _) = _
  rw [Sym2.map_mk,
    canonicalBoundaryDeletionToPrimal_remainingToDeletion,
    canonicalBoundaryDeletionToPrimal_remainingToDeletion]
  exact Quot.out_eq _

/-- Distinct available rectangle labels give distinct deleted-grid edges. -/
theorem canonicalBoundaryAvailableEdgeToDeletion_injective
    (R S : ℕ) (A : Finset Point) :
    Function.Injective (canonicalBoundaryAvailableEdgeToDeletion R S A) := by
  intro e f hef
  apply Subtype.ext
  apply rectanglePrimal_ends_injective (R + 1) (S + 1)
  have hmapped := congrArg
    (Sym2.map (canonicalBoundaryDeletionToPrimal R S A))
    (congrArg Subtype.val hef)
  simpa [map_canonicalBoundaryAvailableEdgeToDeletion] using hmapped

/-- Cotree labels and deleted-primal tree labels map disjointly and
injectively into the edges of the boundary-deleted grid. -/
noncomputable def canonicalBoundaryCotreeTreeSumToDeletionEdge
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (A : Finset Point)
    (T : SimpleSpanningTreeType
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A))) :
    (↑(canonicalBoundaryContractedCotree R S A T) ⊕
      ↑(canonicalBoundaryPrimalTreeLabels R S A T)) →
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A)).edgeSet
  | Sum.inl e =>
      canonicalBoundaryAvailableEdgeToDeletion R S A
        ⟨e.1.1, canonicalBoundaryNonLoopEdge_not_mem_dualEdges
          hR hS A e.1⟩
  | Sum.inr e =>
      canonicalBoundaryAvailableEdgeToDeletion R S A
        ⟨e.1, canonicalBoundaryPrimalTreeLabels_not_mem_dualEdges
          R S A T e.2⟩

theorem canonicalBoundaryCotreeTreeSumToDeletionEdge_injective
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (A : Finset Point)
    (T : SimpleSpanningTreeType
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A))) :
    Function.Injective
      (canonicalBoundaryCotreeTreeSumToDeletionEdge hR hS A T) := by
  intro e f hef
  cases e with
  | inl e =>
      cases f with
      | inl f =>
          apply congrArg Sum.inl
          apply Subtype.ext
          apply Subtype.ext
          have havail :=
            canonicalBoundaryAvailableEdgeToDeletion_injective R S A hef
          exact congrArg (fun x => x.1) havail
      | inr f =>
          have havail := canonicalBoundaryAvailableEdgeToDeletion_injective
            R S A hef
          have hev : e.1.1 = f.1 := congrArg Subtype.val havail
          have hnot := (mem_canonicalBoundaryContractedCotree R S A T e.1).mp e.2
          exact False.elim (hnot (hev ▸ f.2))
  | inr e =>
      cases f with
      | inl f =>
          have havail := canonicalBoundaryAvailableEdgeToDeletion_injective
            R S A hef
          have hev : e.1 = f.1.1 := congrArg Subtype.val havail
          have hnot := (mem_canonicalBoundaryContractedCotree R S A T f.1).mp f.2
          exact False.elim (hnot (hev.symm ▸ e.2))
      | inr f =>
          apply congrArg Sum.inr
          apply Subtype.ext
          have havail :=
            canonicalBoundaryAvailableEdgeToDeletion_injective R S A hef
          exact congrArg (fun x => x.1) havail

/-- The cotree labels together with the primal-tree labels fit injectively
inside the finite deleted-grid edge set. -/
theorem canonicalBoundary_cotree_card_add_tree_card_le_deleted_edges
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (A : Finset Point)
    (T : SimpleSpanningTreeType
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A))) :
    (canonicalBoundaryContractedCotree R S A T).card +
        (canonicalBoundaryPrimalTreeLabels R S A T).card ≤
      Nat.card (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A)).edgeSet := by
  have hinj := canonicalBoundaryCotreeTreeSumToDeletionEdge_injective
    hR hS A T
  have hcard := Nat.card_le_card_of_injective
    (canonicalBoundaryCotreeTreeSumToDeletionEdge hR hS A T) hinj
  rw [Nat.card_sum, Nat.card_eq_finsetCard, Nat.card_eq_finsetCard] at hcard
  exact hcard

/-- Choose one label representing an unordered edge of the underlying simple
graph. -/
noncomputable def edgeLabelOfToSimpleGraphEdge
    {V E : Type*} (G : LabeledMultigraph V E)
    (p : G.toSimpleGraph.edgeSet) : E := by
  apply Classical.choose
  induction hp : p.1 using Sym2.inductionOn with
  | _ u v =>
      have huv : G.toSimpleGraph.Adj u v := by
        rw [← SimpleGraph.mem_edgeSet, ← hp]
        exact p.2
      rcases huv with ⟨_, e, he⟩
      exact ⟨e, he.trans hp.symm⟩

theorem edgeLabelOfToSimpleGraphEdge_spec
    {V E : Type*} (G : LabeledMultigraph V E)
    (p : G.toSimpleGraph.edgeSet) :
    G.ends (edgeLabelOfToSimpleGraphEdge G p) = p.1 := by
  exact Classical.choose_spec (show ∃ e, G.ends e = p.1 by
    induction hp : p.1 using Sym2.inductionOn with
    | _ u v =>
        have huv : G.toSimpleGraph.Adj u v := by
          rw [← SimpleGraph.mem_edgeSet, ← hp]
          exact p.2
        rcases huv with ⟨_, e, he⟩
        exact ⟨e, he⟩)

theorem edgeLabelOfToSimpleGraphEdge_injective
    {V E : Type*} (G : LabeledMultigraph V E) :
    Function.Injective (edgeLabelOfToSimpleGraphEdge G) := by
  intro p q hpq
  apply Subtype.ext
  calc
    p.1 = G.ends (edgeLabelOfToSimpleGraphEdge G p) :=
      (edgeLabelOfToSimpleGraphEdge_spec G p).symm
    _ = G.ends (edgeLabelOfToSimpleGraphEdge G q) := congrArg G.ends hpq
    _ = q.1 := edgeLabelOfToSimpleGraphEdge_spec G q

/-- A labelled multigraph has no more underlying unordered simple edges than
labels, even when it has loops or parallel labels. -/
theorem natCard_toSimpleGraph_edgeSet_le_card_labels
    {V E : Type*} [Fintype E] (G : LabeledMultigraph V E) :
    Nat.card G.toSimpleGraph.edgeSet ≤ Fintype.card E := by
  have h := Nat.card_le_card_of_injective
    (edgeLabelOfToSimpleGraphEdge G)
    (edgeLabelOfToSimpleGraphEdge_injective G)
  simpa [Nat.card_eq_fintype_card] using h

/-- Natural occupied vertices are exactly the integer-coordinate vertices
left after deleting the canonical boundary vacancies. -/
noncomputable def canonicalBoundaryOccupiedEquiv
    (R S : ℕ) (A : Finset Point) :
    Boundary.BoundaryOccupiedVertex R S A ≃
      {p : Point // p ∈ rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A} where
  toFun z := by
    have hz := Finset.mem_sdiff.mp z.2
    refine ⟨Boundary.ofNatPoint z.1, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
    · exact Boundary.ofNatPoint_mem_standardRectangle.mpr
        (Boundary.mem_grid.mp hz.1)
    · intro hzImage
      change Boundary.ofNatPoint z.1 ∈
        (canonicalBoundaryNaturalVacancies R S A).image
          Boundary.ofNatPoint at hzImage
      rcases Finset.mem_image.mp hzImage with ⟨w, hw, hzw⟩
      exact hz.2 (Boundary.ofNatPoint_injective hzw.symm ▸ hw)
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
    intro hzBoundary
    apply hp.2
    change p.1 ∈ (canonicalBoundaryNaturalVacancies R S A).image
      Boundary.ofNatPoint
    rw [← hzval]
    exact Finset.mem_image.mpr ⟨z, hzBoundary, rfl⟩
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

/-- The preceding coordinate equivalence preserves nearest-neighbor
adjacency. -/
noncomputable def canonicalBoundaryOccupiedGraphIso
    (R S : ℕ) (A : Finset Point) :
    Boundary.boundaryOccupiedFaceGraph R S A ≃g
      inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A) where
  toEquiv := canonicalBoundaryOccupiedEquiv R S A
  map_rel_iff' := by
    intro z w
    change manhattanDist (Boundary.ofNatPoint z.1)
        (Boundary.ofNatPoint w.1) = 1 ↔
      Boundary.natManhattanDist z.1 w.1 = 1
    rw [Boundary.manhattanDist_ofNatPoint]

/-- The deleted-grid simple edge count is bounded by the number of occupied
horizontal and vertical unit-edge labels. -/
theorem natCard_canonicalBoundary_deleted_edgeSet_le_occupiedEdges
    (R S : ℕ) (A : Finset Point) :
    Nat.card (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A)).edgeSet ≤
      (Boundary.horizontalOccupiedEdges R S
          (canonicalBoundaryNaturalVacancies R S A)).card +
        (Boundary.verticalOccupiedEdges R S
          (canonicalBoundaryNaturalVacancies R S A)).card := by
  let B := canonicalBoundaryNaturalVacancies R S A
  let G := Boundary.occupiedGridMultigraph R S B
  have hiso : Nat.card
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A)).edgeSet =
      Nat.card (Boundary.boundaryOccupiedFaceGraph R S A).edgeSet := by
    exact (Nat.card_congr
      (canonicalBoundaryOccupiedGraphIso R S A).mapEdgeSet).symm
  rw [hiso]
  have hgraph : G.toSimpleGraph =
      Boundary.boundaryOccupiedFaceGraph R S A := by
    simpa [G, B, Boundary.boundaryOccupiedFaceGraph] using
      (Boundary.occupiedGrid_toSimpleGraph_eq_faceLattice R S B)
  rw [← hgraph]
  have hlabels := natCard_toSimpleGraph_edgeSet_le_card_labels G
  simpa [G, B, Boundary.OccupiedEdge] using hlabels

/-- Recovering ambient primal labels does not change the number of edges in
the displayed deleted-grid tree. -/
theorem card_canonicalBoundaryPrimalTreeLabels_add_one
    (R S : ℕ) (A : Finset Point)
    (T : SimpleSpanningTreeType
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A))) :
    (canonicalBoundaryPrimalTreeLabels R S A T).card + 1 =
      (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A).card := by
  classical
  letI : Fintype {p : Point //
      p ∈ rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A} := Fintype.ofFinite _
  let M := T.1.map (canonicalBoundaryDeletionToPrimal R S A)
  have hle : M ≤ (rectanglePrimal (R + 1) (S + 1)).toSimpleGraph := by
    intro u v huv
    rw [SimpleGraph.map_adj] at huv
    rcases huv with ⟨p, q, hpq, rfl, rfl⟩
    exact (canonicalBoundaryDeletionPrimalGraphEmbedding R S A).toHom.map_adj
      (T.2.1 hpq)
  have hlabels : (canonicalBoundaryPrimalTreeLabels R S A T).card =
      M.edgeFinset.card := by
    rw [← Fintype.card_coe, SimpleGraph.edgeFinset_card]
    exact Fintype.card_congr
      (labelsOfSimpleSubgraphEdgeEquiv
        (rectanglePrimal (R + 1) (S + 1))
        (rectanglePrimal_ends_injective (R + 1) (S + 1)) M hle)
  have hmap : M.edgeFinset.card = T.1.edgeFinset.card := by
    change (T.1.map (canonicalBoundaryDeletionToPrimal R S A)).edgeFinset.card =
      T.1.edgeFinset.card
    exact SimpleGraph.card_edgeFinset_map
      (canonicalBoundaryDeletionToPrimal R S A) T.1
  rw [hlabels, hmap]
  simpa [Fintype.card_coe] using T.2.2.card_edgeFinset

/-- The deleted integer-coordinate vertex count is the occupied natural-grid
vertex count. -/
theorem card_canonicalBoundary_deletedVertices
    (R S : ℕ) (A : Finset Point) :
    (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A).card =
      (Boundary.occupiedVertices R S
        (canonicalBoundaryNaturalVacancies R S A)).card := by
  classical
  letI : Fintype {p : Point //
      p ∈ rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A} := Fintype.ofFinite _
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (canonicalBoundaryOccupiedEquiv R S A).symm

/-- The explicit contraction presentation gives one root component plus one
component for each unmarked bounded face. -/
theorem card_canonicalBoundaryContractedVertex
    (R S : ℕ) (A : Finset Point) :
    Fintype.card (CanonicalBoundaryContractedVertex R S A) =
      (Boundary.unmarkedFaces R S
        (canonicalBoundaryNaturalVacancies R S A)).card + 1 := by
  rw [Fintype.card_congr
    (canonicalBoundaryComponentEquiv R S A
      (canonicalBoundaryMarkedFaceWiring R S A))]
  simp [CanonicalBoundaryUnmarkedFace]

/-- A connected selected labelled graph has at most as many simple edges as
selected labels. -/
theorem natCard_simpleGraphOn_edgeSet_le_card
    {V E : Type*} (G : LabeledMultigraph V E) (F : Finset E)
    (hloop : ∀ e ∈ F, ¬G.IsLoop e) :
    Nat.card (G.simpleGraphOn (F : Set E)).edgeSet ≤ F.card := by
  have hsurj := G.selectedEndpoint_surjective F hloop
  have hcard := Nat.card_le_card_of_surjective
    (G.selectedEndpoint F hloop) hsurj
  simpa [Nat.card_eq_finsetCard] using hcard

/-- Euler's finite identity supplies the exact rank of the connected
contracted cotree. -/
theorem canonicalBoundaryContractedCotree_card_add_one
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (T : SimpleSpanningTreeType
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A))) :
    (canonicalBoundaryContractedCotree R S A T).card + 1 =
      Fintype.card (CanonicalBoundaryContractedVertex R S A) := by
  have hsumEdge := canonicalBoundary_cotree_card_add_tree_card_le_deleted_edges
    hR hS A T
  have hdeletedEdge :=
    natCard_canonicalBoundary_deleted_edgeSet_le_occupiedEdges R S A
  have hP := card_canonicalBoundaryPrimalTreeLabels_add_one R S A T
  rw [card_canonicalBoundary_deletedVertices R S A] at hP
  have hEuler := Boundary.encodedBoundaryEulerIdentity_of_connected hHull hconn
  change (Boundary.occupiedVertices R S
      (canonicalBoundaryNaturalVacancies R S A)).card +
      (Boundary.unmarkedFaces R S
        (canonicalBoundaryNaturalVacancies R S A)).card =
    (Boundary.horizontalOccupiedEdges R S
      (canonicalBoundaryNaturalVacancies R S A)).card +
      (Boundary.verticalOccupiedEdges R S
        (canonicalBoundaryNaturalVacancies R S A)).card + 1 at hEuler
  have hvertex := card_canonicalBoundaryContractedVertex R S A
  have hupper : (canonicalBoundaryContractedCotree R S A T).card + 1 ≤
      Fintype.card (CanonicalBoundaryContractedVertex R S A) := by
    rw [hvertex]
    omega
  have hselectedConnected :=
    canonicalBoundaryContractedCotree_connected hR hS A T
  have hvert_le := hselectedConnected.card_vert_le_card_edgeSet_add_one
  have hedge_le : Nat.card
      ((canonicalBoundaryContractedDual R S A).simpleGraphOn
        (canonicalBoundaryContractedCotree R S A T :
          Set ((rectangleDual (R + 1) (S + 1)).contractWithLoops
          (canonicalBoundaryDualEdges R S A)).NonLoopEdge)).edgeSet ≤
      (canonicalBoundaryContractedCotree R S A T).card := by
    apply natCard_simpleGraphOn_edgeSet_le_card
    intro e _
    exact (rectangleDual (R + 1) (S + 1)).contractWithLoops
      (canonicalBoundaryDualEdges R S A) |>.deleteLoops_loopless e
  have hlower : Fintype.card (CanonicalBoundaryContractedVertex R S A) ≤
      (canonicalBoundaryContractedCotree R S A T).card + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact hvert_le.trans (Nat.add_le_add_right hedge_le 1)
  omega

/-- The explicit complementary cotree is therefore a labelled spanning tree;
no deletion/contraction rank hypothesis remains. -/
theorem canonicalBoundaryContractedCotree_isSpanningTree
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (T : SimpleSpanningTreeType
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A))) :
    (canonicalBoundaryContractedDual R S A).IsSpanningTree
      (canonicalBoundaryContractedCotree R S A T) := by
  refine ⟨?_, canonicalBoundaryContractedCotree_connected hR hS A T,
    canonicalBoundaryContractedCotree_card_add_one hR hS hHull hconn T⟩
  intro e _
  exact (rectangleDual (R + 1) (S + 1)).contractWithLoops
    (canonicalBoundaryDualEdges R S A) |>.deleteLoops_loopless e

/-- Euler rank upgrades the disjoint edge injection to a bijection: every
deleted-grid edge is either a primal-tree edge or the primal mate of exactly
one contracted-cotree edge. -/
theorem canonicalBoundaryCotreeTreeSumToDeletionEdge_bijective
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (T : SimpleSpanningTreeType
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A))) :
    Function.Bijective
      (canonicalBoundaryCotreeTreeSumToDeletionEdge hR hS A T) := by
  apply (Nat.bijective_iff_injective_and_card
    (canonicalBoundaryCotreeTreeSumToDeletionEdge hR hS A T)).mpr
  refine ⟨canonicalBoundaryCotreeTreeSumToDeletionEdge_injective
    hR hS A T, ?_⟩
  rw [Nat.card_sum, Nat.card_eq_finsetCard, Nat.card_eq_finsetCard]
  have hsumEdge := canonicalBoundary_cotree_card_add_tree_card_le_deleted_edges
    hR hS A T
  have hdeletedEdge :=
    natCard_canonicalBoundary_deleted_edgeSet_le_occupiedEdges R S A
  have hP := card_canonicalBoundaryPrimalTreeLabels_add_one R S A T
  rw [card_canonicalBoundary_deletedVertices R S A] at hP
  have hQ := canonicalBoundaryContractedCotree_card_add_one
    hR hS hHull hconn T
  rw [card_canonicalBoundaryContractedVertex R S A] at hQ
  have hEuler := Boundary.encodedBoundaryEulerIdentity_of_connected hHull hconn
  change (Boundary.occupiedVertices R S
      (canonicalBoundaryNaturalVacancies R S A)).card +
      (Boundary.unmarkedFaces R S
        (canonicalBoundaryNaturalVacancies R S A)).card =
    (Boundary.horizontalOccupiedEdges R S
      (canonicalBoundaryNaturalVacancies R S A)).card +
      (Boundary.verticalOccupiedEdges R S
        (canonicalBoundaryNaturalVacancies R S A)).card + 1 at hEuler
  omega

/-- The explicit cotree finset determines the deleted-grid tree uniquely. -/
theorem canonicalBoundaryContractedCotree_injective
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    Function.Injective (canonicalBoundaryContractedCotree R S A) := by
  intro T U hQU
  have hsurjU := (canonicalBoundaryCotreeTreeSumToDeletionEdge_bijective
    hR hS hHull hconn U).2
  have hsubset : canonicalBoundaryPrimalTreeLabels R S A T ⊆
      canonicalBoundaryPrimalTreeLabels R S A U := by
    intro e heT
    let eAvail : {e : RectangleEdge (R + 1) (S + 1) //
        e ∉ canonicalBoundaryDualEdges R S A} :=
      ⟨e, canonicalBoundaryPrimalTreeLabels_not_mem_dualEdges
        R S A T heT⟩
    obtain ⟨x, hx⟩ := hsurjU
      (canonicalBoundaryAvailableEdgeToDeletion R S A eAvail)
    cases x with
    | inl q =>
        change canonicalBoundaryAvailableEdgeToDeletion R S A _ =
          canonicalBoundaryAvailableEdgeToDeletion R S A eAvail at hx
        have havail := canonicalBoundaryAvailableEdgeToDeletion_injective
          R S A hx
        have hqe : q.1.1 = e := congrArg (fun z => z.1) havail
        have hqT : q.1 ∈ canonicalBoundaryContractedCotree R S A T := by
          rw [hQU]
          exact q.2
        have hnot :=
          (mem_canonicalBoundaryContractedCotree R S A T q.1).mp hqT
        exact False.elim (hnot (hqe ▸ heT))
    | inr p =>
        change canonicalBoundaryAvailableEdgeToDeletion R S A _ =
          canonicalBoundaryAvailableEdgeToDeletion R S A eAvail at hx
        have havail := canonicalBoundaryAvailableEdgeToDeletion_injective
          R S A hx
        have hpe : p.1 = e := congrArg (fun z => z.1) havail
        exact hpe ▸ p.2
  have hPcardT := card_canonicalBoundaryPrimalTreeLabels_add_one R S A T
  have hPcardU := card_canonicalBoundaryPrimalTreeLabels_add_one R S A U
  have hPU : canonicalBoundaryPrimalTreeLabels R S A T =
      canonicalBoundaryPrimalTreeLabels R S A U := by
    apply Finset.eq_of_subset_of_card_le hsubset
    omega
  apply Subtype.ext
  apply SimpleGraph.map_injective (canonicalBoundaryDeletionToPrimal R S A)
  rw [← simpleGraphOn_canonicalBoundaryPrimalTreeLabels R S A T,
    ← simpleGraphOn_canonicalBoundaryPrimalTreeLabels R S A U, hPU]

/-- The coordinate model of the primal graph left after the canonical
boundary deletion is connected. -/
theorem canonicalBoundaryDeletedGrid_connected
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalBoundary R S A)).Connected := by
  exact (canonicalBoundaryOccupiedGraphIso R S A).connected_iff.mp
    (Boundary.boundaryOccupiedFaceGraph_connected hHull hconn)

/-- Every edge of the boundary-deleted grid has a unique ambient rectangle
label avoiding the contracted vacancy labels.  Surjectivity is obtained by
partitioning the edge set with any one deleted-primal spanning tree and its
already proved complementary contracted cotree. -/
theorem canonicalBoundaryAvailableEdgeToDeletion_surjective
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    Function.Surjective
      (canonicalBoundaryAvailableEdgeToDeletion R S A) := by
  classical
  let G := inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
    Boundary.canonicalBoundary R S A)
  have hG : G.Connected := canonicalBoundaryDeletedGrid_connected hHull hconn
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  let T₀ : SimpleSpanningTreeType G := ⟨T, hTG, hT⟩
  intro p
  obtain ⟨x, hx⟩ :=
    (canonicalBoundaryCotreeTreeSumToDeletionEdge_bijective
      hR hS hHull hconn T₀).2 p
  cases x with
  | inl q =>
      refine ⟨⟨q.1.1, canonicalBoundaryNonLoopEdge_not_mem_dualEdges
        hR hS A q.1⟩, ?_⟩
      exact hx
  | inr e =>
      refine ⟨⟨e.1, canonicalBoundaryPrimalTreeLabels_not_mem_dualEdges
        R S A T₀ e.2⟩, ?_⟩
      exact hx

/-- Available rectangle labels are canonically equivalent to the unordered
edges of the boundary-deleted primal graph. -/
noncomputable def canonicalBoundaryAvailableEdgeEquivDeletionEdge
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    {e : RectangleEdge (R + 1) (S + 1) //
        e ∉ canonicalBoundaryDualEdges R S A} ≃
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A)).edgeSet :=
  Equiv.ofBijective (canonicalBoundaryAvailableEdgeToDeletion R S A)
    ⟨canonicalBoundaryAvailableEdgeToDeletion_injective R S A,
      canonicalBoundaryAvailableEdgeToDeletion_surjective
        hR hS hHull hconn⟩

/-! ## Cut parity inherited by a labelled contraction -/

/-- Double-count selected incidences whose vertex lies in a displayed set. -/
def sigmaSelectedIncidentLabelsInSetEquiv
    {V E : Type*} (G : LabeledMultigraph V E) (B : Finset E)
    (C : Set V) :
    (Σ v : {v : V // v ∈ C}, SelectedIncidentLabels G B v.1) ≃
      (Σ e : {e : E // e ∈ B},
        {v : V // v ∈ G.ends e.1 ∧ v ∈ C}) where
  toFun x := ⟨⟨x.2.1, x.2.2.1⟩, ⟨x.1.1, x.2.2.2, x.1.2⟩⟩
  invFun x := ⟨⟨x.2.1, x.2.2.2⟩,
    ⟨x.1.1, x.1.2, x.2.2.1⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A nonloop unordered pair meets a vertex set in a number of endpoints
whose parity is exactly its cut-crossing indicator. -/
noncomputable def endpointInSetEquivFinset
    {V : Type*} [DecidableEq V] (C : Set V)
    [DecidablePred fun v => v ∈ C] (q : Sym2 V) :
    {v : V // v ∈ q ∧ v ∈ C} ≃
      ↑(q.toFinset.filter fun v => v ∈ C) :=
  Equiv.subtypeEquiv (Equiv.refl V) (by
    intro v
    change (v ∈ q ∧ v ∈ C) ↔
      v ∈ q.toFinset.filter (fun w => w ∈ C)
    simp)

theorem even_endpointInSet_card_add_crossIndicator
    {V : Type*} [Fintype V] (C : Set V) (q : Sym2 V)
    (hq : ¬q.IsDiag) :
    Even (Nat.card {v : V // v ∈ q ∧ v ∈ C} +
      Nat.card {_u : Unit // sym2CrossesSet C q}) := by
  classical
  rw [Nat.card_congr (endpointInSetEquivFinset C q),
    Nat.card_eq_finsetCard]
  induction hq' : q using Sym2.inductionOn with
  | _ u v =>
      have huv : u ≠ v := by
        simpa [hq', Sym2.mk_isDiag_iff] using hq
      rw [Sym2.toFinset_mk_eq]
      by_cases hu : u ∈ C
      · by_cases hv : v ∈ C
        · have hf : {x ∈ ({u, v} : Finset V) | x ∈ C} = {u, v} := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_insert,
              Finset.mem_singleton]
            aesop
          rw [hf]
          simp [sym2CrossesSet, hu, hv, huv]
        · have hf : {x ∈ ({u, v} : Finset V) | x ∈ C} = {u} := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_insert,
              Finset.mem_singleton]
            aesop
          rw [hf]
          simp [sym2CrossesSet, hu, hv]
      · by_cases hv : v ∈ C
        · have hf : {x ∈ ({u, v} : Finset V) | x ∈ C} = {v} := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_insert,
              Finset.mem_singleton]
            aesop
          rw [hf]
          simp [sym2CrossesSet, hu, hv]
        · have hf : {x ∈ ({u, v} : Finset V) | x ∈ C} = ∅ := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_insert,
              Finset.mem_singleton]
            aesop
          rw [hf]
          simp [sym2CrossesSet, hu, hv]

/-- Choosing a selected label together with the unique inhabitant of its
crossing indicator is the same as choosing a selected cut label. -/
def sigmaCrossIndicatorEquivSelectedCutLabels
    {V E : Type*} [Fintype E] [DecidableEq E]
    (G : LabeledMultigraph V E) (B : Finset E) (C : Set V) :
    (Σ e : {e : E // e ∈ B},
      {_u : Unit // sym2CrossesSet C (G.ends e.1)}) ≃
      ↑(B ∩ cutLabels G C) where
  toFun x := ⟨x.1.1, Finset.mem_inter.mpr
    ⟨x.1.2, (mem_cutLabels G C x.1.1).mpr x.2.2⟩⟩
  invFun e := ⟨⟨e.1, (Finset.mem_inter.mp e.2).1⟩,
    ⟨(), (mem_cutLabels G C e.1).mp (Finset.mem_inter.mp e.2).2⟩⟩
  left_inv x := by
    rcases x with ⟨e, u⟩
    rcases u.1
    rfl
  right_inv _ := rfl

/-- Labelled handshaking restricted to a vertex set: if every selected
labelled degree is even, then the selected cut has even cardinality.  This
form deliberately retains parallel labels. -/
theorem selectedCutLabels_card_even
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LabeledMultigraph V E) (B : Finset E) (C : Set V)
    (hloop : ∀ e ∈ B, ¬G.IsLoop e)
    (heven : ∀ v, Even (Nat.card (SelectedIncidentLabels G B v))) :
    Even ((B ∩ cutLabels G C).card) := by
  classical
  letI : Fintype {v : V // v ∈ C} := Fintype.ofFinite _
  have hincidence :
      (∑ v : {v : V // v ∈ C},
          Nat.card (SelectedIncidentLabels G B v.1)) =
        ∑ e : {e : E // e ∈ B},
          Nat.card {v : V // v ∈ G.ends e.1 ∧ v ∈ C} := by
    rw [← Nat.card_sigma,
      Nat.card_congr (sigmaSelectedIncidentLabelsInSetEquiv G B C),
      Nat.card_sigma]
  have hleftEven : Even (∑ v : {v : V // v ∈ C},
      Nat.card (SelectedIncidentLabels G B v.1)) := by
    apply Finset.even_sum
    intro v _
    exact heven v.1
  have htotalEven : Even
      (∑ e : {e : E // e ∈ B},
        (Nat.card {v : V // v ∈ G.ends e.1 ∧ v ∈ C} +
          Nat.card {_u : Unit // sym2CrossesSet C (G.ends e.1)})) := by
    apply Finset.even_sum
    intro e _
    exact even_endpointInSet_card_add_crossIndicator C (G.ends e.1)
      (hloop e.1 e.2)
  rw [Finset.sum_add_distrib, ← hincidence] at htotalEven
  have hindicator :
      (∑ e : {e : E // e ∈ B},
          Nat.card {_u : Unit // sym2CrossesSet C (G.ends e.1)}) =
        (B ∩ cutLabels G C).card := by
    rw [← Nat.card_sigma,
      Nat.card_congr (sigmaCrossIndicatorEquivSelectedCutLabels G B C),
      Nat.card_eq_finsetCard]
  rw [hindicator] at htotalEven
  exact (Nat.even_add.mp htotalEven).mp hleftEven

/-- For two endpoints which remain distinct after passing to connected
components, crossing the support of one component is equivalent to that
component being incident with the mapped pair. -/
theorem sym2CrossesSet_componentSupport_iff_mem_map
    {V : Type*} (K : SimpleGraph V) (q : Sym2 V)
    (c : K.ConnectedComponent)
    (hq : ¬(Sym2.map K.connectedComponentMk q).IsDiag) :
    sym2CrossesSet c.supp q ↔
      c ∈ Sym2.map K.connectedComponentMk q := by
  induction hq' : q using Sym2.inductionOn with
  | _ u v =>
      have huv : K.connectedComponentMk u ≠ K.connectedComponentMk v := by
        simpa [hq', Sym2.mk_isDiag_iff] using hq
      rw [sym2CrossesSet_mk, Sym2.map_mk, Sym2.mem_iff,
        SimpleGraph.ConnectedComponent.mem_supp_iff,
        SimpleGraph.ConnectedComponent.mem_supp_iff]
      constructor
      · aesop
      · intro hc
        rcases hc with hc | hc
        · left
          refine ⟨hc.symm, ?_⟩
          intro hcv
          exact huv (hc.symm.trans hcv.symm)
        · right
          refine ⟨hc.symm, ?_⟩
          intro hcu
          exact huv (hcu.trans hc)

/-- Bundle a selected family of original labels which all survive a
contraction as selected nonloop labels of the contracted graph. -/
noncomputable def survivingLabelEmbedding
    {V E : Type*} (H : LabeledMultigraph V E) (D B : Finset E)
    (hsurvive : ∀ e ∈ B, ¬(H.contractWithLoops D).IsLoop e) :
    ↑B ↪ (H.contractWithLoops D).NonLoopEdge where
  toFun e := ⟨e.1, hsurvive e.1 e.2⟩
  inj' := by
    intro e f hef
    apply Subtype.ext
    exact congrArg
      (fun z : (H.contractWithLoops D).NonLoopEdge => z.1) hef

noncomputable def contractedSelectedLabelsOfSurvive
    {V E : Type*} (H : LabeledMultigraph V E) (D B : Finset E)
    (hsurvive : ∀ e ∈ B, ¬(H.contractWithLoops D).IsLoop e) :
    Finset (H.contractWithLoops D).NonLoopEdge := by
  classical
  exact B.attach.map (survivingLabelEmbedding H D B hsurvive)

@[simp] theorem mem_contractedSelectedLabelsOfSurvive
    {V E : Type*} (H : LabeledMultigraph V E) (D B : Finset E)
    (hsurvive : ∀ e ∈ B, ¬(H.contractWithLoops D).IsLoop e)
    (e : (H.contractWithLoops D).NonLoopEdge) :
    e ∈ contractedSelectedLabelsOfSurvive H D B hsurvive ↔ e.1 ∈ B := by
  classical
  constructor
  · intro he
    rw [contractedSelectedLabelsOfSurvive, Finset.mem_map] at he
    rcases he with ⟨f, hf, hfe⟩
    have : f.1 = e.1 := congrArg Subtype.val hfe
    exact this ▸ f.2
  · intro he
    rw [contractedSelectedLabelsOfSurvive, Finset.mem_map]
    refine ⟨⟨e.1, he⟩, by simp, ?_⟩
    apply Subtype.ext
    rfl

/-- At one contraction component, surviving selected incident labels are
exactly the original selected labels crossing that component's support. -/
noncomputable def contractedSelectedIncidentEquivOriginalCut
    {V E : Type*} [Fintype E] [DecidableEq E]
    (H : LabeledMultigraph V E) (D B : Finset E)
    (hsurvive : ∀ e ∈ B, ¬(H.contractWithLoops D).IsLoop e)
    (c : (H.simpleGraphOn (D : Set E)).ConnectedComponent) :
    SelectedIncidentLabels (H.contract D)
        (contractedSelectedLabelsOfSurvive H D B hsurvive) c ≃
      ↑(B ∩ cutLabels H c.supp) where
  toFun e := by
    refine ⟨e.1.1, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · exact (mem_contractedSelectedLabelsOfSurvive H D B hsurvive e.1).mp
        e.2.1
    · apply (mem_cutLabels H c.supp e.1.1).mpr
      apply (sym2CrossesSet_componentSupport_iff_mem_map
        (H.simpleGraphOn (D : Set E)) (H.ends e.1.1) c e.1.2).mpr
      exact e.2.2
  invFun e := by
    have heB : e.1 ∈ B := (Finset.mem_inter.mp e.2).1
    let e' : (H.contractWithLoops D).NonLoopEdge :=
      ⟨e.1, hsurvive e.1 heB⟩
    refine ⟨e', ?_, ?_⟩
    · exact (mem_contractedSelectedLabelsOfSurvive
        H D B hsurvive e').mpr heB
    · apply (sym2CrossesSet_componentSupport_iff_mem_map
        (H.simpleGraphOn (D : Set E)) (H.ends e.1) c e'.2).mp
      exact (mem_cutLabels H c.supp e.1).mp
        (Finset.mem_inter.mp e.2).2
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    rfl

/-- Even labelled degrees descend to every contraction component for any
selected family whose labels survive the contraction. -/
theorem contractedSelectedIncident_even
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (H : LabeledMultigraph V E) (D B : Finset E)
    (hloop : ∀ e ∈ B, ¬H.IsLoop e)
    (heven : ∀ v, Even (Nat.card (SelectedIncidentLabels H B v)))
    (hsurvive : ∀ e ∈ B, ¬(H.contractWithLoops D).IsLoop e)
    (c : (H.simpleGraphOn (D : Set E)).ConnectedComponent) :
    Even (Nat.card (SelectedIncidentLabels (H.contract D)
      (contractedSelectedLabelsOfSurvive H D B hsurvive) c)) := by
  rw [Nat.card_congr
    (contractedSelectedIncidentEquivOriginalCut H D B hsurvive c)]
  rw [Nat.card_eq_finsetCard]
  exact selectedCutLabels_card_even H B c.supp hloop heven

/-! ## Reverse boundary cotree construction -/

/-- Crossing a set is invariant under mapping both endpoints along an
embedding and replacing the set by its image. -/
theorem sym2CrossesSet_image_map_embedding
    {V W : Type*} (f : V ↪ W) (C : Set V) (q : Sym2 V) :
    sym2CrossesSet (f '' C) (Sym2.map f q) ↔
      sym2CrossesSet C q := by
  induction q using Sym2.inductionOn with
  | _ u v =>
      simp only [Sym2.map_mk, sym2CrossesSet_mk, Set.mem_image]
      have hmem : ∀ x, (∃ y ∈ C, f y = f x) ↔ x ∈ C := by
        intro x
        constructor
        · rintro ⟨y, hy, h⟩
          exact f.injective h ▸ hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      rw [hmem u, hmem v]

/-- A contracted nonloop dual label determines its primal mate in the
boundary-deleted grid. -/
noncomputable def canonicalBoundaryContractedEdgeToDeletionEmbedding
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (A : Finset Point) :
    ((rectangleDual (R + 1) (S + 1)).contractWithLoops
      (canonicalBoundaryDualEdges R S A)).NonLoopEdge ↪
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A)).edgeSet where
  toFun e := canonicalBoundaryAvailableEdgeToDeletion R S A
    ⟨e.1, canonicalBoundaryNonLoopEdge_not_mem_dualEdges hR hS A e⟩
  inj' := by
    intro e f hef
    have havail := canonicalBoundaryAvailableEdgeToDeletion_injective
      R S A hef
    apply Subtype.ext
    exact congrArg
      (fun z : {e : RectangleEdge (R + 1) (S + 1) //
        e ∉ canonicalBoundaryDualEdges R S A} => z.1) havail

/-- Regard the deleted primal graph as uniquely labelled by its own
unordered edges. -/
def canonicalBoundaryDeletedEdgeLabeledGraph
    (R S : ℕ) (A : Finset Point) :
    LabeledMultigraph
      {p : Point // p ∈ rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A}
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A)).edgeSet where
  ends e := e.1

@[simp] theorem canonicalBoundaryDeletedEdgeLabeledGraph_ends
    (R S : ℕ) (A : Finset Point)
    (e : (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalBoundary R S A)).edgeSet) :
    (canonicalBoundaryDeletedEdgeLabeledGraph R S A).ends e = e.1 := rfl

@[simp] theorem canonicalBoundaryDeletedEdgeLabeledGraph_toSimpleGraph
    (R S : ℕ) (A : Finset Point) :
    (canonicalBoundaryDeletedEdgeLabeledGraph R S A).toSimpleGraph =
      inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A) := by
  ext u v
  constructor
  · rintro ⟨_, e, he⟩
    have he' := e.2
    change e.1 = s(u, v) at he
    rw [he, SimpleGraph.mem_edgeSet] at he'
    exact he'
  · intro huv
    refine ⟨huv.ne, ⟨s(u, v), ?_⟩, rfl⟩
    rw [SimpleGraph.mem_edgeSet]
    exact huv

/-- The deleted-grid labels represented by a displayed contracted-dual
tree. -/
noncomputable def canonicalBoundaryContractedTreeDeletionEdges
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (A : Finset Point)
    (T : (canonicalBoundaryContractedDual R S A).SpanningTree) :
    Finset (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalBoundary R S A)).edgeSet :=
  T.1.map (canonicalBoundaryContractedEdgeToDeletionEmbedding hR hS A)

/-- Remove precisely the primal mates of a contracted-dual tree from the
boundary-deleted grid.  The theorem below proves that what remains is a
tree. -/
noncomputable def canonicalBoundaryPrimalComplementGraph
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (A : Finset Point)
    (T : (canonicalBoundaryContractedDual R S A).SpanningTree) :
    SimpleGraph {p : Point // p ∈ rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalBoundary R S A} := by
  classical
  letI : Fintype
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A)).edgeSet := Fintype.ofFinite _
  exact (canonicalBoundaryDeletedEdgeLabeledGraph R S A).simpleGraphOn
    ((Finset.univ \
      canonicalBoundaryContractedTreeDeletionEdges hR hS A T :
        Finset (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
          Boundary.canonicalBoundary R S A)).edgeSet) : Set _)

/-- Those labels of a contracted-dual tree whose primal mates cross a
displayed cut of the boundary-deleted graph. -/
noncomputable def canonicalBoundaryContractedTreeCutLabels
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (A : Finset Point)
    (T : (canonicalBoundaryContractedDual R S A).SpanningTree)
    (C : Set {p : Point // p ∈ rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalBoundary R S A}) :
    Finset ((rectangleDual (R + 1) (S + 1)).contractWithLoops
      (canonicalBoundaryDualEdges R S A)).NonLoopEdge := by
  classical
  exact T.1.filter fun e => sym2CrossesSet C
    (canonicalBoundaryContractedEdgeToDeletionEmbedding hR hS A e).1

@[simp] theorem mem_canonicalBoundaryContractedTreeCutLabels
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (A : Finset Point)
    (T : (canonicalBoundaryContractedDual R S A).SpanningTree)
    (C : Set {p : Point // p ∈ rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalBoundary R S A})
    (e : ((rectangleDual (R + 1) (S + 1)).contractWithLoops
      (canonicalBoundaryDualEdges R S A)).NonLoopEdge) :
    e ∈ canonicalBoundaryContractedTreeCutLabels hR hS A T C ↔
      e ∈ T.1 ∧ sym2CrossesSet C
        (canonicalBoundaryContractedEdgeToDeletionEmbedding hR hS A e).1 := by
  classical
  simp [canonicalBoundaryContractedTreeCutLabels]

/-- At every unmarked (hence isolated before contraction) bounded face, the
contracted-dual labels above a deleted-primal cut have even labelled degree.
The cut-subset hypothesis is exactly what arises from a component of the
putative primal complement. -/
theorem canonicalBoundaryUnmarked_cutDegreeEven
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (A : Finset Point)
    (T : (canonicalBoundaryContractedDual R S A).SpanningTree)
    (C : Set {p : Point // p ∈ rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalBoundary R S A})
    (hcutSubset : ∀ p :
        (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
          Boundary.canonicalBoundary R S A)).edgeSet,
      sym2CrossesSet C p.1 →
        p ∈ canonicalBoundaryContractedTreeDeletionEdges hR hS A T)
    (z : CanonicalBoundaryUnmarkedFace R S A) :
    Even (Nat.card (SelectedIncidentLabels
      (canonicalBoundaryContractedDual R S A)
      (canonicalBoundaryContractedTreeCutLabels hR hS A T C)
      (canonicalBoundaryUnmarkedComponent R S A z))) := by
  classical
  let D := canonicalBoundaryDualEdges R S A
  let H := rectangleDual (R + 1) (S + 1)
  let u := canonicalBoundaryUnmarkedDualVertex R S A z
  let B := canonicalBoundaryContractedTreeCutLabels hR hS A T C
  let Cfull : Set (Fin (R + 1) × Fin (S + 1)) :=
    canonicalBoundaryDeletionToPrimal R S A '' C
  let P := cutLabels (rectanglePrimal (R + 1) (S + 1)) Cfull
  let base : IncidentLabel (H.contract D)
        (canonicalBoundaryUnmarkedComponent R S A z) ≃
      IncidentLabel H u :=
    contractIncidentLabelEquivOfIsolated H D u
      (rectangleDual_not_isLoop (by omega) (by omega))
      (canonicalBoundaryUnmarkedDualVertex_isIsolated R S A z)
  let e₁ := selectedIncidentLabelsEquivSubtypeIncident
    (H.contract D) B (canonicalBoundaryUnmarkedComponent R S A z)
  let e₃ := selectedIncidentLabelsEquivSubtypeIncident H P u
  have hpred : ∀ a : IncidentLabel (H.contract D)
      (canonicalBoundaryUnmarkedComponent R S A z),
      a.1 ∈ B ↔ (base a).1 ∈ P := by
    intro a
    have hmap := map_canonicalBoundaryAvailableEdgeToDeletion R S A
      (⟨a.1.1, canonicalBoundaryNonLoopEdge_not_mem_dualEdges
        hR hS A a.1⟩ : {e : RectangleEdge (R + 1) (S + 1) //
          e ∉ D})
    have hmap' :
        Sym2.map (canonicalBoundaryDeletionToPrimal R S A)
            (canonicalBoundaryContractedEdgeToDeletionEmbedding
              hR hS A a.1).1 =
          (rectanglePrimal (R + 1) (S + 1)).ends a.1.1 := by
      simpa [canonicalBoundaryContractedEdgeToDeletionEmbedding] using hmap
    have hcross :
        sym2CrossesSet C
            (canonicalBoundaryContractedEdgeToDeletionEmbedding
              hR hS A a.1).1 ↔
          sym2CrossesSet Cfull
            ((rectanglePrimal (R + 1) (S + 1)).ends a.1.1) := by
      have himage := sym2CrossesSet_image_map_embedding
        (canonicalBoundaryDeletionToPrimal R S A) C
        (canonicalBoundaryContractedEdgeToDeletionEmbedding
          hR hS A a.1).1
      rw [hmap'] at himage
      exact himage.symm
    constructor
    · intro ha
      have ha' := (mem_canonicalBoundaryContractedTreeCutLabels
        hR hS A T C a.1).mp ha
      change a.1.1 ∈ P
      exact (mem_cutLabels (rectanglePrimal (R + 1) (S + 1))
        Cfull a.1.1).mpr (hcross.mp ha'.2)
    · intro ha
      have haCut : a.1.1 ∈ P := by exact ha
      have hcross' := hcross.mpr
        ((mem_cutLabels (rectanglePrimal (R + 1) (S + 1))
          Cfull a.1.1).mp haCut)
      have hpTree := hcutSubset
        (canonicalBoundaryContractedEdgeToDeletionEmbedding hR hS A a.1)
        hcross'
      rw [canonicalBoundaryContractedTreeDeletionEdges,
        Finset.mem_map] at hpTree
      rcases hpTree with ⟨b, hbT, hba⟩
      have hba' :=
        (canonicalBoundaryContractedEdgeToDeletionEmbedding
          hR hS A).injective hba
      apply (mem_canonicalBoundaryContractedTreeCutLabels
        hR hS A T C a.1).mpr
      exact ⟨hba' ▸ hbT, hcross'⟩
  let e₂ : {a : IncidentLabel (H.contract D)
      (canonicalBoundaryUnmarkedComponent R S A z) // a.1 ∈ B} ≃
      {a : IncidentLabel H u // a.1 ∈ P} :=
    Equiv.subtypeEquiv base hpred
  have hcard : Nat.card (SelectedIncidentLabels
      (canonicalBoundaryContractedDual R S A) B
      (canonicalBoundaryUnmarkedComponent R S A z)) =
      Nat.card (SelectedIncidentLabels H P u) := by
    exact Nat.card_congr (e₁.trans (e₂.trans e₃.symm))
  rw [hcard]
  change Even (Nat.card (SelectedIncidentLabels
    (rectangleDual (R + 1) (S + 1)) P
    (some ((boundedFaceEquivFaceIndices R S).symm
      ⟨z.1, (Boundary.mem_unmarkedFaces.mp z.2).1⟩))))
  exact rectangleDual_boundedFace_cutBoundaryEven Cfull
    ((boundedFaceEquivFaceIndices R S).symm
      ⟨z.1, (Boundary.mem_unmarkedFaces.mp z.2).1⟩)

/-- The cut degree is even at every contracted-dual vertex.  The unmarked
faces use the local square parity above; the exterior/marked component then
follows from labelled handshaking, which also handles parallel labels. -/
theorem canonicalBoundaryContractedTreeCutDegreeEven
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (A : Finset Point)
    (T : (canonicalBoundaryContractedDual R S A).SpanningTree)
    (C : Set {p : Point // p ∈ rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalBoundary R S A})
    (hcutSubset : ∀ p :
        (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
          Boundary.canonicalBoundary R S A)).edgeSet,
      sym2CrossesSet C p.1 →
        p ∈ canonicalBoundaryContractedTreeDeletionEdges hR hS A T)
    (c : CanonicalBoundaryContractedVertex R S A) :
    Even (Nat.card (SelectedIncidentLabels
      (canonicalBoundaryContractedDual R S A)
      (canonicalBoundaryContractedTreeCutLabels hR hS A T C) c)) := by
  classical
  let B := canonicalBoundaryContractedTreeCutLabels hR hS A T C
  let count : CanonicalBoundaryContractedVertex R S A → ℕ := fun v =>
    Nat.card (SelectedIncidentLabels
      (canonicalBoundaryContractedDual R S A) B v)
  let e := canonicalBoundaryComponentEquiv R S A
    (canonicalBoundaryMarkedFaceWiring R S A)
  have htotal : (∑ v, count v) = 2 * B.card := by
    exact sum_natCard_selectedIncidentLabels_eq_twice_card
      (canonicalBoundaryContractedDual R S A) B
      (fun q _ => (rectangleDual (R + 1) (S + 1)).contractWithLoops
        (canonicalBoundaryDualEdges R S A) |>.deleteLoops_loopless q)
  have htotalEven : Even (∑ v, count v) := by
    rw [htotal]
    exact even_two_mul B.card
  have eroot : e.symm none = canonicalBoundaryContractionRoot R S A := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (canonicalBoundaryComponentEquiv_root R S A
      (canonicalBoundaryMarkedFaceWiring R S A)).symm
  have eunmarked : ∀ z, e.symm (some z) =
      canonicalBoundaryUnmarkedComponent R S A z := by
    intro z
    apply e.injective
    rw [e.apply_symm_apply]
    exact (canonicalBoundaryComponentEquiv_unmarkedComponent R S A
      (canonicalBoundaryMarkedFaceWiring R S A) z).symm
  have htotalOption : Even
      (∑ o : Option (CanonicalBoundaryUnmarkedFace R S A),
        count (e.symm o)) := by
    rw [e.symm.sum_comp count]
    exact htotalEven
  rw [Fintype.sum_option] at htotalOption
  have hfacesEven : Even
      (∑ z : CanonicalBoundaryUnmarkedFace R S A,
        count (e.symm (some z))) := by
    apply Finset.even_sum
    intro z _
    rw [eunmarked z]
    exact canonicalBoundaryUnmarked_cutDegreeEven
      hR hS A T C hcutSubset z
  have hrootEven : Even (count (canonicalBoundaryContractionRoot R S A)) := by
    rw [← eroot]
    exact (Nat.even_add.mp htotalOption).mpr hfacesEven
  cases hc : e c with
  | none =>
      have hcroot : c = canonicalBoundaryContractionRoot R S A := by
        apply e.injective
        rw [hc]
        exact (canonicalBoundaryComponentEquiv_root R S A
          (canonicalBoundaryMarkedFaceWiring R S A)).symm
      rw [hcroot]
      exact hrootEven
  | some z =>
      have hcz : c = canonicalBoundaryUnmarkedComponent R S A z := by
        apply e.injective
        rw [hc]
        exact (canonicalBoundaryComponentEquiv_unmarkedComponent R S A
          (canonicalBoundaryMarkedFaceWiring R S A) z).symm
      rw [hcz]
      exact canonicalBoundaryUnmarked_cutDegreeEven
        hR hS A T C hcutSubset z

/-- The primal mates complementary to an arbitrary contracted-dual tree are
connected in the boundary-deleted grid.  If not, the cut of one component
would give a nonempty even labelled subgraph of the contracted tree, hence a
cycle. -/
theorem canonicalBoundaryPrimalComplementGraph_connected
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (T : (canonicalBoundaryContractedDual R S A).SpanningTree) :
    (canonicalBoundaryPrimalComplementGraph hR hS A T).Connected := by
  classical
  let V := {p : Point // p ∈ rectangle 0 0 (R + 1) (S + 1) \
    Boundary.canonicalBoundary R S A}
  let G := canonicalBoundaryDeletedEdgeLabeledGraph R S A
  let F := canonicalBoundaryContractedTreeDeletionEdges hR hS A T
  letI : Fintype
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A)).edgeSet := Fintype.ofFinite _
  let K := G.simpleGraphOn ((Finset.univ \ F : Finset _) : Set _)
  have hGconn : G.Connected := by
    rw [LabeledMultigraph.Connected,
      canonicalBoundaryDeletedEdgeLabeledGraph_toSimpleGraph]
    exact canonicalBoundaryDeletedGrid_connected hHull hconn
  letI : Nonempty V := hGconn.nonempty
  have hK : canonicalBoundaryPrimalComplementGraph hR hS A T = K := by
    rfl
  rw [hK]
  refine { preconnected := ?_ }
  intro a b
  by_contra hab
  let c := K.connectedComponentMk a
  have haC : a ∈ c.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hbC : b ∉ c.supp := by
    intro hb
    exact hab (c.reachable_of_mem_supp haC hb)
  have hcutNonempty : (cutLabels G c.supp).Nonempty :=
    cutLabels_nonempty_of_connected G hGconn c.supp
      ⟨a, haC⟩ ⟨b, hbC⟩
  have hcutSubset : ∀ p :
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A)).edgeSet,
      sym2CrossesSet c.supp p.1 → p ∈ F := by
    intro p hp
    have hpCut : p ∈ cutLabels G c.supp := by
      exact (mem_cutLabels G c.supp p).mpr hp
    by_contra hpF
    have hpComp : p ∈ (Finset.univ \ F : Finset _) := by
      simp [hpF]
    exact Finset.disjoint_left.mp
      (cutLabels_component_disjoint G (Finset.univ \ F) c)
      hpCut hpComp
  let B := canonicalBoundaryContractedTreeCutLabels hR hS A T c.supp
  have hBnonempty : B.Nonempty := by
    rcases hcutNonempty with ⟨p, hp⟩
    have hpCross := (mem_cutLabels G c.supp p).mp hp
    have hpF := hcutSubset p hpCross
    change p ∈ canonicalBoundaryContractedTreeDeletionEdges hR hS A T at hpF
    rw [canonicalBoundaryContractedTreeDeletionEdges,
      Finset.mem_map] at hpF
    rcases hpF with ⟨e, heT, hep⟩
    refine ⟨e, (mem_canonicalBoundaryContractedTreeCutLabels
      hR hS A T c.supp e).mpr ⟨heT, ?_⟩⟩
    exact hep ▸ hpCross
  have hBsubset : B ⊆ T.1 := by
    intro e he
    exact (mem_canonicalBoundaryContractedTreeCutLabels
      hR hS A T c.supp e).mp he |>.1
  let Q := (canonicalBoundaryContractedDual R S A).simpleGraphOn
    (B : Set ((rectangleDual (R + 1) (S + 1)).contractWithLoops
      (canonicalBoundaryDualEdges R S A)).NonLoopEdge)
  have hQne : Q ≠ ⊥ := by
    rcases hBnonempty with ⟨e, heB⟩
    induction hends : (canonicalBoundaryContractedDual R S A).ends e using
        Sym2.inductionOn with
    | _ u v =>
        have huv : u ≠ v := by
          intro huv
          subst v
          exact (rectangleDual (R + 1) (S + 1)).contractWithLoops
            (canonicalBoundaryDualEdges R S A) |>.deleteLoops_loopless e
            ((canonicalBoundaryContractedDual R S A).isLoop_iff_exists_isLoopAt
              e |>.mpr ⟨u, hends⟩)
        intro hbot
        have hadj : Q.Adj u v := ⟨huv, e, heB, hends⟩
        rw [hbot] at hadj
        exact hadj
  have hQeven : ∀ v, Even (Q.degree v) := by
    intro v
    rw [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card]
    rw [← Nat.card_congr
      (selectedIncidentEquivNeighborSetOfSubsetTree
        (canonicalBoundaryContractedDual R S A) T.1 B
        T.2 hBsubset v)]
    exact canonicalBoundaryContractedTreeCutDegreeEven
      hR hS A T c.supp hcutSubset v
  have hQacyclic : Q.IsAcyclic := by
    apply SimpleGraph.IsAcyclic.anti
      ((canonicalBoundaryContractedDual R S A).simpleGraphOn_mono hBsubset)
    exact T.2.toSimpleGraph_isTree.isAcyclic
  exact (not_isAcyclic_of_nonempty_even_degree Q hQne hQeven) hQacyclic

/-- With globally unique selected endpoint pairs, the selected simple graph
has exactly as many edges as selected labels. -/
theorem natCard_simpleGraphOn_edgeSet_eq_card_of_ends_injective
    {V E : Type*} [Fintype E]
    (G : LabeledMultigraph V E) (F : Finset E)
    (hloop : ∀ e ∈ F, ¬G.IsLoop e)
    (hends : Function.Injective G.ends) :
    Nat.card (G.simpleGraphOn (F : Set E)).edgeSet = F.card := by
  let f := G.selectedEndpoint F hloop
  have hsurj : Function.Surjective f := G.selectedEndpoint_surjective F hloop
  have hinj : Function.Injective f := by
    intro e q heq
    apply Subtype.ext
    apply hends
    exact congrArg Subtype.val heq
  calc
    Nat.card (G.simpleGraphOn (F : Set E)).edgeSet =
        Nat.card (SelectedEdge F) :=
      Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩).symm
    _ = F.card := Nat.card_eq_finsetCard F

/-- The boundary-deleted grid has exactly the Euler-predicted number of
occupied unit edges. -/
theorem natCard_canonicalBoundary_deleted_edgeSet_eq_occupiedEdges
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    Nat.card (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A)).edgeSet =
      (Boundary.horizontalOccupiedEdges R S
          (canonicalBoundaryNaturalVacancies R S A)).card +
        (Boundary.verticalOccupiedEdges R S
          (canonicalBoundaryNaturalVacancies R S A)).card := by
  classical
  let G := inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
    Boundary.canonicalBoundary R S A)
  obtain ⟨U, hUG, hUtree⟩ :=
    (canonicalBoundaryDeletedGrid_connected hHull hconn).exists_isTree_le
  let U₀ : SimpleSpanningTreeType G := ⟨U, hUG, hUtree⟩
  have hcard := Nat.card_congr
    (Equiv.ofBijective
      (canonicalBoundaryCotreeTreeSumToDeletionEdge hR hS A U₀)
      (canonicalBoundaryCotreeTreeSumToDeletionEdge_bijective
        hR hS hHull hconn U₀))
  rw [Nat.card_sum, Nat.card_eq_finsetCard,
    Nat.card_eq_finsetCard] at hcard
  have hP := card_canonicalBoundaryPrimalTreeLabels_add_one R S A U₀
  rw [card_canonicalBoundary_deletedVertices R S A] at hP
  have hQ := canonicalBoundaryContractedCotree_card_add_one
    hR hS hHull hconn U₀
  rw [card_canonicalBoundaryContractedVertex R S A] at hQ
  have hEuler := Boundary.encodedBoundaryEulerIdentity_of_connected hHull hconn
  change (Boundary.occupiedVertices R S
      (canonicalBoundaryNaturalVacancies R S A)).card +
      (Boundary.unmarkedFaces R S
        (canonicalBoundaryNaturalVacancies R S A)).card =
    (Boundary.horizontalOccupiedEdges R S
      (canonicalBoundaryNaturalVacancies R S A)).card +
      (Boundary.verticalOccupiedEdges R S
        (canonicalBoundaryNaturalVacancies R S A)).card + 1 at hEuler
  omega

/-- The connected primal complement has the exact tree rank. -/
theorem canonicalBoundaryPrimalComplementGraph_card_add_one
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (T : (canonicalBoundaryContractedDual R S A).SpanningTree) :
    Nat.card (canonicalBoundaryPrimalComplementGraph hR hS A T).edgeSet + 1 =
      Nat.card {p : Point // p ∈ rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A} := by
  classical
  let G₀ := inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
    Boundary.canonicalBoundary R S A)
  let H := canonicalBoundaryDeletedEdgeLabeledGraph R S A
  let F := canonicalBoundaryContractedTreeDeletionEdges hR hS A T
  letI : Fintype G₀.edgeSet := Fintype.ofFinite _
  let Fc : Finset G₀.edgeSet := Finset.univ \ F
  have hloop : ∀ e ∈ Fc, ¬H.IsLoop e := by
    intro e _ he
    exact G₀.not_isDiag_of_mem_edgeSet e.2 he
  have hends : Function.Injective H.ends := by
    intro e q heq
    apply Subtype.ext
    exact heq
  have hselected :
      Nat.card (H.simpleGraphOn (Fc : Set G₀.edgeSet)).edgeSet =
        Fc.card :=
    natCard_simpleGraphOn_edgeSet_eq_card_of_ends_injective
      H Fc hloop hends
  have hgraph : canonicalBoundaryPrimalComplementGraph hR hS A T =
      H.simpleGraphOn (Fc : Set G₀.edgeSet) := by
    rfl
  have hFcard : F.card = T.1.card := by
    simp [F, canonicalBoundaryContractedTreeDeletionEdges]
  have hFcomp : Fc.card + F.card = Fintype.card G₀.edgeSet := by
    dsimp [Fc]
    rw [Finset.card_sdiff]
    have hle : F.card ≤ Fintype.card G₀.edgeSet := by
      simpa using Finset.card_le_card (Finset.subset_univ F)
    simp only [Finset.inter_univ, Finset.card_univ]
    omega
  have htotal :=
    natCard_canonicalBoundary_deleted_edgeSet_eq_occupiedEdges
      hR hS hHull hconn
  have hTcard := T.2.card_edges_add_one
  rw [card_canonicalBoundaryContractedVertex R S A] at hTcard
  have hEuler := Boundary.encodedBoundaryEulerIdentity_of_connected hHull hconn
  change (Boundary.occupiedVertices R S
      (canonicalBoundaryNaturalVacancies R S A)).card +
      (Boundary.unmarkedFaces R S
        (canonicalBoundaryNaturalVacancies R S A)).card =
    (Boundary.horizontalOccupiedEdges R S
      (canonicalBoundaryNaturalVacancies R S A)).card +
      (Boundary.verticalOccupiedEdges R S
        (canonicalBoundaryNaturalVacancies R S A)).card + 1 at hEuler
  have hvertices := card_canonicalBoundary_deletedVertices R S A
  have hT_eq : T.1.card =
      (Boundary.unmarkedFaces R S
        (canonicalBoundaryNaturalVacancies R S A)).card := by
    omega
  have hF_eq : F.card =
      (Boundary.unmarkedFaces R S
        (canonicalBoundaryNaturalVacancies R S A)).card :=
    hFcard.trans hT_eq
  have htotal' : Fintype.card G₀.edgeSet =
      (Boundary.horizontalOccupiedEdges R S
          (canonicalBoundaryNaturalVacancies R S A)).card +
        (Boundary.verticalOccupiedEdges R S
          (canonicalBoundaryNaturalVacancies R S A)).card := by
    rw [← Nat.card_eq_fintype_card]
    exact htotal
  have hFc : Fc.card + 1 =
      (Boundary.occupiedVertices R S
        (canonicalBoundaryNaturalVacancies R S A)).card := by
    omega
  rw [hgraph, hselected, Nat.card_eq_finsetCard, hvertices]
  exact hFc

/-- The primal complement is therefore a concrete simple spanning tree of
the boundary-deleted grid. -/
noncomputable def canonicalBoundaryPrimalComplementTree
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (T : (canonicalBoundaryContractedDual R S A).SpanningTree) :
    SimpleSpanningTreeType
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A)) := by
  let K := canonicalBoundaryPrimalComplementGraph hR hS A T
  refine ⟨K, ?_, ?_⟩
  · intro u v huv
    change ((canonicalBoundaryDeletedEdgeLabeledGraph R S A).simpleGraphOn
      _).Adj u v at huv
    rcases huv with ⟨hne, e, _, he⟩
    have hsimple :
        (canonicalBoundaryDeletedEdgeLabeledGraph R S A).toSimpleGraph.Adj
          u v := ⟨hne, e, he⟩
    rw [canonicalBoundaryDeletedEdgeLabeledGraph_toSimpleGraph] at hsimple
    exact hsimple
  · apply SimpleGraph.isTree_iff_connected_and_card.mpr
    exact ⟨canonicalBoundaryPrimalComplementGraph_connected
      hR hS hHull hconn T,
      canonicalBoundaryPrimalComplementGraph_card_add_one
        hR hS hHull hconn T⟩

/-- Edge membership in the primal complement is literal complementation of
the mapped contracted-tree labels. -/
theorem mem_canonicalBoundaryPrimalComplementGraph_edgeSet
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (A : Finset Point)
    (T : (canonicalBoundaryContractedDual R S A).SpanningTree)
    (p : (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalBoundary R S A)).edgeSet) :
    p.1 ∈ (canonicalBoundaryPrimalComplementGraph hR hS A T).edgeSet ↔
      p ∉ canonicalBoundaryContractedTreeDeletionEdges hR hS A T := by
  classical
  letI : Fintype
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A)).edgeSet := Fintype.ofFinite _
  change p.1 ∈ ((canonicalBoundaryDeletedEdgeLabeledGraph R S A).simpleGraphOn
    ((Finset.univ \
      canonicalBoundaryContractedTreeDeletionEdges hR hS A T :
        Finset (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
          Boundary.canonicalBoundary R S A)).edgeSet) : Set _)).edgeSet ↔ _
  induction hp : p.1 using Sym2.inductionOn with
  | _ u v =>
      rw [SimpleGraph.mem_edgeSet]
      constructor
      · rintro ⟨_, q, hq, hends⟩
        change q.1 = s(u, v) at hends
        have hqp : q = p := by
          apply Subtype.ext
          exact hends.trans hp.symm
        subst q
        simpa using hq
      · intro hpT
        have hpSel : p ∈ (Finset.univ \
            canonicalBoundaryContractedTreeDeletionEdges hR hS A T :
              Finset (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
                Boundary.canonicalBoundary R S A)).edgeSet) := by
          simp [hpT]
        have huv : (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
            Boundary.canonicalBoundary R S A)).Adj u v := by
          rw [← SimpleGraph.mem_edgeSet, ← hp]
          exact p.2
        exact ⟨huv.ne, p, hpSel, hp⟩

/-- A surviving dual label belongs to the recovered primal complement
exactly when it does not belong to the original contracted-dual tree. -/
theorem canonicalBoundaryNonLoop_mem_primalComplementLabels_iff
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (T : (canonicalBoundaryContractedDual R S A).SpanningTree)
    (e : ((rectangleDual (R + 1) (S + 1)).contractWithLoops
      (canonicalBoundaryDualEdges R S A)).NonLoopEdge) :
    e.1 ∈ canonicalBoundaryPrimalTreeLabels R S A
        (canonicalBoundaryPrimalComplementTree hR hS hHull hconn T) ↔
      e ∉ T.1 := by
  classical
  let U := canonicalBoundaryPrimalComplementTree hR hS hHull hconn T
  let p := canonicalBoundaryContractedEdgeToDeletionEmbedding hR hS A e
  rw [canonicalBoundaryPrimalTreeLabels,
    mem_labelsOfSimpleSubgraph]
  have hmap :
      Sym2.map (canonicalBoundaryDeletionToPrimal R S A) p.1 =
        (rectanglePrimal (R + 1) (S + 1)).ends e.1 := by
    simpa [p, canonicalBoundaryContractedEdgeToDeletionEmbedding] using
      (map_canonicalBoundaryAvailableEdgeToDeletion R S A
        (⟨e.1, canonicalBoundaryNonLoopEdge_not_mem_dualEdges
          hR hS A e⟩ : {q : RectangleEdge (R + 1) (S + 1) //
            q ∉ canonicalBoundaryDualEdges R S A}))
  rw [← hmap]
  have hedgeIff :
      Sym2.map (canonicalBoundaryDeletionToPrimal R S A) p.1 ∈
          (U.1.map (canonicalBoundaryDeletionToPrimal R S A)).edgeSet ↔
        p.1 ∈ U.1.edgeSet := by
    exact (SimpleGraph.Embedding.map
      (canonicalBoundaryDeletionToPrimal R S A) U.1).map_mem_edgeSet_iff
  rw [hedgeIff]
  change p.1 ∈
    (canonicalBoundaryPrimalComplementGraph hR hS A T).edgeSet ↔ _
  rw [mem_canonicalBoundaryPrimalComplementGraph_edgeSet]
  constructor
  · intro hp heT
    apply hp
    rw [canonicalBoundaryContractedTreeDeletionEdges, Finset.mem_map]
    exact ⟨e, heT, rfl⟩
  · intro heT hp
    rw [canonicalBoundaryContractedTreeDeletionEdges, Finset.mem_map] at hp
    rcases hp with ⟨q, hqT, hqp⟩
    have hqe := (canonicalBoundaryContractedEdgeToDeletionEmbedding
      hR hS A).injective hqp
    exact heT (hqe ▸ hqT)

/-- Recovering a primal complement and complementing once more returns the
original contracted-dual tree label for label. -/
theorem canonicalBoundaryContractedCotree_primalComplementTree
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (T : (canonicalBoundaryContractedDual R S A).SpanningTree) :
    canonicalBoundaryContractedCotree R S A
      (canonicalBoundaryPrimalComplementTree hR hS hHull hconn T) = T.1 := by
  ext e
  rw [mem_canonicalBoundaryContractedCotree,
    canonicalBoundaryNonLoop_mem_primalComplementLabels_iff]
  simp

/-- The surjectivity proposition for the explicit boundary cotree map.  It
is retained as a convenient interface and discharged below. -/
def BoundaryVacancyCotreeSurjectivity
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) : Prop :=
  Function.Surjective (fun T =>
    (⟨canonicalBoundaryContractedCotree R S A T,
      canonicalBoundaryContractedCotree_isSpanningTree
        hR hS hHull hconn T⟩ :
      (canonicalBoundaryContractedDual R S A).SpanningTree))

/-- Surjectivity alone now constructs the former two-field complement law;
the tree and injectivity fields are theorems. -/
theorem boundaryVacancyTreeComplementLawOfSurjectivity
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (hsurj : BoundaryVacancyCotreeSurjectivity hR hS hHull hconn) :
    BoundaryVacancyTreeComplementLaw R S A where
  cotree_isTree := canonicalBoundaryContractedCotree_isSpanningTree
    hR hS hHull hconn
  cotree_bijective := by
    constructor
    · intro T U hTU
      apply canonicalBoundaryContractedCotree_injective hR hS hHull hconn
      exact congrArg Subtype.val hTU
    · exact hsurj

/-- End-to-end boundary planar data from the one remaining deletion-minor
surjectivity statement.  Full-rectangle complementation and contraction
geometry are unconditional. -/
noncomputable def canonicalBoundaryPlanarTreeComplementOfSurjectivity
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (hsurj : BoundaryVacancyCotreeSurjectivity hR hS hHull hconn) :
    BoundaryPlanarTreeComplement R S A :=
  boundaryPlanarTreeComplementOfComplementLaws R S A
    (canonicalRectangleTreeComplementLaw hR hS)
    (boundaryVacancyTreeComplementLawOfSurjectivity
      hR hS hHull hconn hsurj)

/-- The explicit primal-complement construction is a right inverse, hence
the boundary cotree map is surjective without any additional assumption. -/
theorem canonicalBoundaryVacancyCotreeSurjectivity
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    BoundaryVacancyCotreeSurjectivity hR hS hHull hconn := by
  intro T
  refine ⟨canonicalBoundaryPrimalComplementTree
    hR hS hHull hconn T, ?_⟩
  apply Subtype.ext
  exact canonicalBoundaryContractedCotree_primalComplementTree
    hR hS hHull hconn T

/-- The complete boundary deletion/contraction tree-complement law. -/
theorem canonicalBoundaryVacancyTreeComplementLaw
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    BoundaryVacancyTreeComplementLaw R S A :=
  boundaryVacancyTreeComplementLawOfSurjectivity
    hR hS hHull hconn
      (canonicalBoundaryVacancyCotreeSurjectivity hR hS hHull hconn)

/-- End-to-end explicit planar tree-complement data for the canonical
boundary deletion.  No planar bijection hypothesis remains. -/
noncomputable def canonicalBoundaryPlanarTreeComplement
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    BoundaryPlanarTreeComplement R S A :=
  boundaryPlanarTreeComplementOfComplementLaws R S A
    (canonicalRectangleTreeComplementLaw hR hS)
    (canonicalBoundaryVacancyTreeComplementLaw hR hS hHull hconn)

/-! ## Generic vacancy deletion: coordinate and reverse-connectivity layer -/

/-- Embed the retained integer-coordinate vertices into the natural primal
rectangle. -/
noncomputable def vacancyDeletionToPrimal
    {R S : ℕ} {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1)) :
    {p : Point // p ∈ D} ↪ (Fin (R + 1) × Fin (S + 1)) where
  toFun p := standardRectangleEquivFin (R + 1) (S + 1) ⟨p.1, hD p.2⟩
  inj' := by
    intro p q hpq
    apply Subtype.ext
    have hfull := (standardRectangleEquivFin (R + 1) (S + 1)).injective hpq
    exact congrArg
      (fun z : {p : Point // p ∈ rectangle 0 0 (R + 1) (S + 1)} => z.1)
      hfull

/-- Converting a retained coordinate to `Fin` coordinates and back returns
the original integer point. -/
theorem ofNatPoint_finPoint_vacancyDeletionToPrimal
    {R S : ℕ} {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (p : {p : Point // p ∈ D}) :
    Boundary.ofNatPoint (finPoint (vacancyDeletionToPrimal hD p)) = p.1 := by
  have hpRect := hD p.2
  have hpBounds :
      ((0 : ℤ) ≤ p.1.1 ∧ p.1.1 < (R + 1 : ℕ)) ∧
      ((0 : ℤ) ≤ p.1.2 ∧ p.1.2 < (S + 1 : ℕ)) := by
    simpa [rectangle] using hpRect
  apply Prod.ext <;>
    simp [vacancyDeletionToPrimal, finPoint, Boundary.ofNatPoint,
      hpBounds.1.1, hpBounds.2.1]

/-- A retained primal vertex converts back to the corresponding vertex of
the displayed integer-coordinate deletion. -/
noncomputable def vacancyRemainingToDeletion
    {R S : ℕ} {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (_hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (u : Fin (R + 1) × Fin (S + 1)) (hu : u ∉ X) :
    {p : Point // p ∈ D} := by
  let z := Boundary.ofNatPoint (finPoint u)
  have hzD : z ∈ D := by
    by_contra hz
    exact hu ((hdelete u).mpr hz)
  exact ⟨z, hzD⟩

@[simp] theorem vacancyDeletionToPrimal_remainingToDeletion
    {R S : ℕ} {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (u : Fin (R + 1) × Fin (S + 1)) (hu : u ∉ X) :
    vacancyDeletionToPrimal hD
      (vacancyRemainingToDeletion hD hdelete u hu) = u := by
  apply finPoint_injective
  simp [vacancyDeletionToPrimal, vacancyRemainingToDeletion,
    finPoint, Boundary.ofNatPoint]

/-- The coordinate embedding preserves and reflects nearest-neighbor
adjacency. -/
noncomputable def vacancyDeletionPrimalGraphEmbedding
    {R S : ℕ} {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1)) :
    inducedGrid D ↪g
      (rectanglePrimal (R + 1) (S + 1)).toSimpleGraph where
  toEmbedding := vacancyDeletionToPrimal hD
  map_rel_iff' := by
    intro p q
    let pFull : {x : Point // x ∈ rectangle 0 0 (R + 1) (S + 1)} :=
      ⟨p.1, hD p.2⟩
    let qFull : {x : Point // x ∈ rectangle 0 0 (R + 1) (S + 1)} :=
      ⟨q.1, hD q.2⟩
    have h := (standardRectangleGridIso (R + 1) (S + 1)).map_rel_iff
      (a := pFull) (b := qFull)
    simpa [vacancyDeletionToPrimal, pFull, qFull,
      inducedGrid_adj_iff, rectanglePrimal_toSimpleGraph,
      standardRectangleGridIso] using h

/-- An ambient rectangle label not incident with a deleted primal vertex
determines an unordered edge of the retained grid. -/
noncomputable def vacancyAvailableEdgeToDeletion
    {R S : ℕ} {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (e : {e : RectangleEdge (R + 1) (S + 1) //
      e ∉ vacancyDualEdges X}) :
    (inducedGrid D).edgeSet := by
  let uv := ((rectanglePrimal (R + 1) (S + 1)).ends e.1).out
  let u := uv.1
  let v := uv.2
  have hends : (rectanglePrimal (R + 1) (S + 1)).ends e.1 = s(u, v) :=
    (Quot.out_eq _).symm
  have huX : u ∉ X := by
    intro hu
    apply e.2
    exact mem_vacancyDualEdges.mpr ⟨u, hu,
      (primalIncident_iff_mem_rectanglePrimal_ends u e.1).mpr
        (hends.symm ▸ Sym2.mem_mk_left u v)⟩
  have hvX : v ∉ X := by
    intro hv
    apply e.2
    exact mem_vacancyDualEdges.mpr ⟨v, hv,
      (primalIncident_iff_mem_rectanglePrimal_ends v e.1).mpr
        (hends.symm ▸ Sym2.mem_mk_right u v)⟩
  let pu := vacancyRemainingToDeletion hD hdelete u huX
  let pv := vacancyRemainingToDeletion hD hdelete v hvX
  have huv : (rectanglePrimal (R + 1) (S + 1)).toSimpleGraph.Adj u v := by
    refine ⟨?_, e.1, hends⟩
    intro huvEq
    apply rectanglePrimal_not_isLoop e.1
    change ((rectanglePrimal (R + 1) (S + 1)).ends e.1).IsDiag
    rw [hends, huvEq]
    exact Sym2.diag_isDiag _
  have hpupv : (inducedGrid D).Adj pu pv := by
    apply (vacancyDeletionPrimalGraphEmbedding hD).map_rel_iff.mp
    change (rectanglePrimal (R + 1) (S + 1)).toSimpleGraph.Adj
      (vacancyDeletionToPrimal hD pu) (vacancyDeletionToPrimal hD pv)
    rw [vacancyDeletionToPrimal_remainingToDeletion,
      vacancyDeletionToPrimal_remainingToDeletion]
    exact huv
  exact ⟨s(pu, pv), by
    rw [SimpleGraph.mem_edgeSet]
    exact hpupv⟩

/-- Mapping the retained edge forward recovers the original ambient primal
endpoint pair. -/
theorem map_vacancyAvailableEdgeToDeletion
    {R S : ℕ} {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (e : {e : RectangleEdge (R + 1) (S + 1) //
      e ∉ vacancyDualEdges X}) :
    Sym2.map (vacancyDeletionToPrimal hD)
        (vacancyAvailableEdgeToDeletion hD hdelete e).1 =
      (rectanglePrimal (R + 1) (S + 1)).ends e.1 := by
  change Sym2.map (vacancyDeletionToPrimal hD)
      s(vacancyRemainingToDeletion hD hdelete _ _,
        vacancyRemainingToDeletion hD hdelete _ _) = _
  rw [Sym2.map_mk, vacancyDeletionToPrimal_remainingToDeletion,
    vacancyDeletionToPrimal_remainingToDeletion]
  exact Quot.out_eq _

/-- Distinct available rectangle labels yield distinct retained-grid edges. -/
theorem vacancyAvailableEdgeToDeletion_injective
    {R S : ℕ} {X : Finset (Fin (R + 1) × Fin (S + 1))}
    {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D) :
    Function.Injective (vacancyAvailableEdgeToDeletion hD hdelete) := by
  intro e f hef
  apply Subtype.ext
  apply rectanglePrimal_ends_injective (R + 1) (S + 1)
  have hmapped := congrArg (Sym2.map (vacancyDeletionToPrimal hD))
    (congrArg Subtype.val hef)
  simpa [map_vacancyAvailableEdgeToDeletion] using hmapped

/-- A surviving edge of an arbitrary vacancy contraction was not among the
contracted labels. -/
theorem vacancyContractedNonLoopEdge_not_mem
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    (X : Finset (Fin (R + 1) × Fin (S + 1)))
    (e : ((rectangleDual (R + 1) (S + 1)).contractWithLoops
      (vacancyDualEdges X)).NonLoopEdge) :
    e.1 ∉ vacancyDualEdges X := by
  intro he
  exact e.2 ((rectangleDual (R + 1) (S + 1)).contractWithLoops_isLoop_of_mem
    he (rectangleDual_not_isLoop (by omega) (by omega) e.1))

/-- A contracted nonloop label determines its retained primal edge. -/
noncomputable def vacancyContractedEdgeToDeletionEmbedding
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))} {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D) :
    ((rectangleDual (R + 1) (S + 1)).contractWithLoops
      (vacancyDualEdges X)).NonLoopEdge ↪ (inducedGrid D).edgeSet where
  toFun e := vacancyAvailableEdgeToDeletion hD hdelete
    ⟨e.1, vacancyContractedNonLoopEdge_not_mem hR hS X e⟩
  inj' := by
    intro e q heq
    have havail := vacancyAvailableEdgeToDeletion_injective hD hdelete heq
    apply Subtype.ext
    exact congrArg
      (fun z : {a : RectangleEdge (R + 1) (S + 1) //
        a ∉ vacancyDualEdges X} => z.1) havail

noncomputable def vacancyContractedTreeDeletionEdges
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))} {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (T : ((rectangleDual (R + 1) (S + 1)).contract
      (vacancyDualEdges X)).SpanningTree) :
    Finset (inducedGrid D).edgeSet :=
  T.1.map (vacancyContractedEdgeToDeletionEmbedding
    hR hS hD hdelete)

/-- Regard a simple graph as uniquely labelled by its own unordered edge
set. -/
def edgeSetLabeledGraph {V : Type*} (G : SimpleGraph V) :
    LabeledMultigraph V G.edgeSet where
  ends e := e.1

noncomputable def vacancyPrimalComplementGraph
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))} {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (T : ((rectangleDual (R + 1) (S + 1)).contract
      (vacancyDualEdges X)).SpanningTree) :
    SimpleGraph {p : Point // p ∈ D} := by
  classical
  letI : Fintype (inducedGrid D).edgeSet := Fintype.ofFinite _
  exact (edgeSetLabeledGraph (inducedGrid D)).simpleGraphOn
    ((Finset.univ \
      vacancyContractedTreeDeletionEdges hR hS hD hdelete T :
        Finset (inducedGrid D).edgeSet) : Set _)

/-- A mapped endpoint pair which crosses a connected component support
cannot collapse to a diagonal pair of components. -/
theorem not_isDiag_map_connectedComponentMk_of_crosses
    {V : Type*} (K : SimpleGraph V) (q : Sym2 V)
    (c : K.ConnectedComponent) (hq : sym2CrossesSet c.supp q) :
    ¬(Sym2.map K.connectedComponentMk q).IsDiag := by
  induction hq' : q using Sym2.inductionOn with
  | _ u v =>
      have hcross :
          (u ∈ c.supp ∧ v ∉ c.supp) ∨
            (v ∈ c.supp ∧ u ∉ c.supp) := by
        simpa [hq'] using hq
      rw [Sym2.map_mk, Sym2.mk_isDiag_iff]
      intro huv
      rcases hcross with h | h
      · exact h.2 ((SimpleGraph.ConnectedComponent.mem_supp_iff c v).mpr
          (huv.symm.trans
            ((SimpleGraph.ConnectedComponent.mem_supp_iff c u).mp h.1)))
      · exact h.2 ((SimpleGraph.ConnectedComponent.mem_supp_iff c u).mpr
          (huv.trans
            ((SimpleGraph.ConnectedComponent.mem_supp_iff c v).mp h.1)))

/-- Labels of a contracted tree whose retained primal mates cross a
displayed retained-vertex cut. -/
noncomputable def vacancyContractedTreeCutLabels
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))} {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (T : ((rectangleDual (R + 1) (S + 1)).contract
      (vacancyDualEdges X)).SpanningTree)
    (C : Set {p : Point // p ∈ D}) :
    Finset ((rectangleDual (R + 1) (S + 1)).contractWithLoops
      (vacancyDualEdges X)).NonLoopEdge := by
  classical
  exact T.1.filter fun e => sym2CrossesSet C
    (vacancyContractedEdgeToDeletionEmbedding hR hS hD hdelete e).1

@[simp] theorem mem_vacancyContractedTreeCutLabels
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))} {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (T : ((rectangleDual (R + 1) (S + 1)).contract
      (vacancyDualEdges X)).SpanningTree)
    (C : Set {p : Point // p ∈ D})
    (e : ((rectangleDual (R + 1) (S + 1)).contractWithLoops
      (vacancyDualEdges X)).NonLoopEdge) :
    e ∈ vacancyContractedTreeCutLabels hR hS hD hdelete T C ↔
      e ∈ T.1 ∧ sym2CrossesSet C
        (vacancyContractedEdgeToDeletionEmbedding hR hS hD hdelete e).1 := by
  classical
  simp [vacancyContractedTreeCutLabels]

/-- For a component cut of the putative retained primal complement,
contracted selected incidences are exactly the full-rectangle primal-cut
labels crossing that contraction component.  Labels in the contracted set
cannot occur on the latter cut. -/
noncomputable def vacancyContractedTreeCutIncidentEquivFullCut
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))} {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (T : ((rectangleDual (R + 1) (S + 1)).contract
      (vacancyDualEdges X)).SpanningTree)
    (C : Set {p : Point // p ∈ D})
    (hcutSubset : ∀ p : (inducedGrid D).edgeSet,
      sym2CrossesSet C p.1 →
        p ∈ vacancyContractedTreeDeletionEdges hR hS hD hdelete T)
    (c : ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
      (vacancyDualEdges X : Set (RectangleEdge (R + 1) (S + 1)))).ConnectedComponent) :
    SelectedIncidentLabels
        ((rectangleDual (R + 1) (S + 1)).contract (vacancyDualEdges X))
        (vacancyContractedTreeCutLabels hR hS hD hdelete T C) c ≃
      ↑((cutLabels (rectanglePrimal (R + 1) (S + 1))
          (vacancyDeletionToPrimal hD '' C)) ∩
        cutLabels (rectangleDual (R + 1) (S + 1)) c.supp) where
  toFun a := by
    refine ⟨a.1.1, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · apply (mem_cutLabels (rectanglePrimal (R + 1) (S + 1))
        (vacancyDeletionToPrimal hD '' C) a.1.1).mpr
      have ha := (mem_vacancyContractedTreeCutLabels
        hR hS hD hdelete T C a.1).mp a.2.1
      have himage := sym2CrossesSet_image_map_embedding
        (vacancyDeletionToPrimal hD) C
        (vacancyContractedEdgeToDeletionEmbedding
          hR hS hD hdelete a.1).1
      have hmap := map_vacancyAvailableEdgeToDeletion hD hdelete
        (⟨a.1.1, vacancyContractedNonLoopEdge_not_mem
          hR hS X a.1⟩ : {e : RectangleEdge (R + 1) (S + 1) //
            e ∉ vacancyDualEdges X})
      have hmap' : Sym2.map (vacancyDeletionToPrimal hD)
          (vacancyContractedEdgeToDeletionEmbedding
            hR hS hD hdelete a.1).1 =
          (rectanglePrimal (R + 1) (S + 1)).ends a.1.1 := by
        simpa [vacancyContractedEdgeToDeletionEmbedding] using hmap
      rw [hmap'] at himage
      exact himage.mpr ha.2
    · apply (mem_cutLabels (rectangleDual (R + 1) (S + 1))
        c.supp a.1.1).mpr
      apply (sym2CrossesSet_componentSupport_iff_mem_map
        ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
          (vacancyDualEdges X : Set _))
        ((rectangleDual (R + 1) (S + 1)).ends a.1.1) c a.1.2).mpr
      exact a.2.2
  invFun q := by
    have hqPrimal := (mem_cutLabels
      (rectanglePrimal (R + 1) (S + 1))
      (vacancyDeletionToPrimal hD '' C) q.1).mp
        (Finset.mem_inter.mp q.2).1
    have hqDual := (mem_cutLabels
      (rectangleDual (R + 1) (S + 1)) c.supp q.1).mp
        (Finset.mem_inter.mp q.2).2
    have hsurvive : ¬((rectangleDual (R + 1) (S + 1)).contractWithLoops
        (vacancyDualEdges X)).IsLoop q.1 :=
      not_isDiag_map_connectedComponentMk_of_crosses
        ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
          (vacancyDualEdges X : Set _))
        ((rectangleDual (R + 1) (S + 1)).ends q.1) c hqDual
    let e : ((rectangleDual (R + 1) (S + 1)).contractWithLoops
        (vacancyDualEdges X)).NonLoopEdge := ⟨q.1, hsurvive⟩
    have hqNotX : q.1 ∉ vacancyDualEdges X := by
      intro hqX
      exact hsurvive
        ((rectangleDual (R + 1) (S + 1)).contractWithLoops_isLoop_of_mem
          hqX (rectangleDual_not_isLoop (by omega) (by omega) q.1))
    let p := vacancyAvailableEdgeToDeletion hD hdelete
      (⟨q.1, hqNotX⟩ : {a : RectangleEdge (R + 1) (S + 1) //
        a ∉ vacancyDualEdges X})
    have hmap := map_vacancyAvailableEdgeToDeletion hD hdelete
      (⟨q.1, hqNotX⟩ : {a : RectangleEdge (R + 1) (S + 1) //
        a ∉ vacancyDualEdges X})
    have himage := sym2CrossesSet_image_map_embedding
      (vacancyDeletionToPrimal hD) C p.1
    rw [hmap] at himage
    have hpCross : sym2CrossesSet C p.1 := himage.mp hqPrimal
    have hpTree := hcutSubset p hpCross
    rw [vacancyContractedTreeDeletionEdges, Finset.mem_map] at hpTree
    let e' := Classical.choose hpTree
    have he'T := (Classical.choose_spec hpTree).1
    have he'p := (Classical.choose_spec hpTree).2
    have hep : vacancyContractedEdgeToDeletionEmbedding
        hR hS hD hdelete e = p := by
      apply Subtype.ext
      rfl
    have he'e := (vacancyContractedEdgeToDeletionEmbedding
      hR hS hD hdelete).injective (he'p.trans hep.symm)
    refine ⟨e, ?_, ?_⟩
    · apply (mem_vacancyContractedTreeCutLabels
        hR hS hD hdelete T C e).mpr
      exact ⟨he'e ▸ he'T, hpCross⟩
    · apply (sym2CrossesSet_componentSupport_iff_mem_map
        ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
          (vacancyDualEdges X : Set _))
        ((rectangleDual (R + 1) (S + 1)).ends q.1) c hsurvive).mp
      exact hqDual
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv q := by
    apply Subtype.ext
    rfl

/-- Every contracted vertex has even degree in the tree labels over such a
retained-primal cut. -/
theorem vacancyContractedTreeCutDegreeEven
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))} {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (T : ((rectangleDual (R + 1) (S + 1)).contract
      (vacancyDualEdges X)).SpanningTree)
    (C : Set {p : Point // p ∈ D})
    (hcutSubset : ∀ p : (inducedGrid D).edgeSet,
      sym2CrossesSet C p.1 →
        p ∈ vacancyContractedTreeDeletionEdges hR hS hD hdelete T)
    (c : ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
      (vacancyDualEdges X : Set (RectangleEdge (R + 1) (S + 1)))).ConnectedComponent) :
    Even (Nat.card (SelectedIncidentLabels
      ((rectangleDual (R + 1) (S + 1)).contract (vacancyDualEdges X))
      (vacancyContractedTreeCutLabels hR hS hD hdelete T C) c)) := by
  rw [Nat.card_congr
    (vacancyContractedTreeCutIncidentEquivFullCut
      hR hS hD hdelete T C hcutSubset c)]
  rw [Nat.card_eq_finsetCard]
  apply selectedCutLabels_card_even
  · intro e _
    exact rectangleDual_not_isLoop (by omega) (by omega) e
  · exact (rectangleDual_primalCutBoundaryEven hR hS)
      (vacancyDeletionToPrimal hD '' C)

@[simp] theorem edgeSetLabeledGraph_toSimpleGraph
    {V : Type*} (G : SimpleGraph V) :
    (edgeSetLabeledGraph G).toSimpleGraph = G := by
  ext u v
  constructor
  · rintro ⟨_, e, he⟩
    have he' := e.2
    change e.1 = s(u, v) at he
    rw [he, SimpleGraph.mem_edgeSet] at he'
    exact he'
  · intro huv
    refine ⟨huv.ne, ⟨s(u, v), ?_⟩, rfl⟩
    rw [SimpleGraph.mem_edgeSet]
    exact huv

/-- The retained primal mates complementary to an arbitrary tree of the
dual contraction are connected.  This is the deletion/contraction analogue
of the reverse half of rectangle tree-complement duality: a disconnected
complement would exhibit a nonempty even subgraph of the dual tree. -/
theorem vacancyPrimalComplementGraph_connected
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))} {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (hconn : (inducedGrid D).Connected)
    (T : ((rectangleDual (R + 1) (S + 1)).contract
      (vacancyDualEdges X)).SpanningTree) :
    (vacancyPrimalComplementGraph hR hS hD hdelete T).Connected := by
  classical
  letI : Fintype
      (((rectangleDual (R + 1) (S + 1)).simpleGraphOn
        (vacancyDualEdges X : Set _)).ConnectedComponent) :=
    (rectangleDual (R + 1) (S + 1)).contractionComponentFintype
      (vacancyDualEdges X)
  let G := edgeSetLabeledGraph (inducedGrid D)
  let F := vacancyContractedTreeDeletionEdges hR hS hD hdelete T
  letI : Fintype (inducedGrid D).edgeSet := Fintype.ofFinite _
  let K := G.simpleGraphOn ((Finset.univ \ F : Finset _) : Set _)
  have hGconn : G.Connected := by
    rw [LabeledMultigraph.Connected, edgeSetLabeledGraph_toSimpleGraph]
    exact hconn
  letI : Nonempty {p : Point // p ∈ D} := hGconn.nonempty
  have hK : vacancyPrimalComplementGraph hR hS hD hdelete T = K := by
    rfl
  rw [hK]
  refine { preconnected := ?_ }
  intro a b
  by_contra hab
  let c := K.connectedComponentMk a
  have haC : a ∈ c.supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hbC : b ∉ c.supp := by
    intro hb
    exact hab (c.reachable_of_mem_supp haC hb)
  have hcutNonempty : (cutLabels G c.supp).Nonempty :=
    cutLabels_nonempty_of_connected G hGconn c.supp
      ⟨a, haC⟩ ⟨b, hbC⟩
  have hcutSubset : ∀ p : (inducedGrid D).edgeSet,
      sym2CrossesSet c.supp p.1 → p ∈ F := by
    intro p hp
    have hpCut : p ∈ cutLabels G c.supp := by
      exact (mem_cutLabels G c.supp p).mpr hp
    by_contra hpF
    have hpComp : p ∈ (Finset.univ \ F : Finset _) := by
      simp [hpF]
    exact Finset.disjoint_left.mp
      (cutLabels_component_disjoint G (Finset.univ \ F) c)
      hpCut hpComp
  let B := vacancyContractedTreeCutLabels hR hS hD hdelete T c.supp
  have hBnonempty : B.Nonempty := by
    rcases hcutNonempty with ⟨p, hp⟩
    have hpCross := (mem_cutLabels G c.supp p).mp hp
    have hpF := hcutSubset p hpCross
    change p ∈ vacancyContractedTreeDeletionEdges
      hR hS hD hdelete T at hpF
    rw [vacancyContractedTreeDeletionEdges, Finset.mem_map] at hpF
    rcases hpF with ⟨e, heT, hep⟩
    refine ⟨e, (mem_vacancyContractedTreeCutLabels
      hR hS hD hdelete T c.supp e).mpr ⟨heT, ?_⟩⟩
    exact hep ▸ hpCross
  have hBsubset : B ⊆ T.1 := by
    intro e he
    exact (mem_vacancyContractedTreeCutLabels
      hR hS hD hdelete T c.supp e).mp he |>.1
  let H := (rectangleDual (R + 1) (S + 1)).contract
    (vacancyDualEdges X)
  let Q := H.simpleGraphOn (B : Set
    ((rectangleDual (R + 1) (S + 1)).contractWithLoops
      (vacancyDualEdges X)).NonLoopEdge)
  have hQne : Q ≠ ⊥ := by
    rcases hBnonempty with ⟨e, heB⟩
    induction hends : H.ends e using Sym2.inductionOn with
    | _ u v =>
        have huv : u ≠ v := by
          intro huv
          subst v
          exact (rectangleDual (R + 1) (S + 1)).contractWithLoops
            (vacancyDualEdges X) |>.deleteLoops_loopless e
            (H.isLoop_iff_exists_isLoopAt e |>.mpr ⟨u, hends⟩)
        intro hbot
        have hadj : Q.Adj u v := ⟨huv, e, heB, hends⟩
        rw [hbot] at hadj
        exact hadj
  have hQeven : ∀ v, Even (Q.degree v) := by
    intro v
    rw [← SimpleGraph.card_neighborSet_eq_degree,
      ← Nat.card_eq_fintype_card]
    rw [← Nat.card_congr
      (selectedIncidentEquivNeighborSetOfSubsetTree
        H T.1 B T.2 hBsubset v)]
    exact vacancyContractedTreeCutDegreeEven
      hR hS hD hdelete T c.supp hcutSubset v
  have hQacyclic : Q.IsAcyclic := by
    apply SimpleGraph.IsAcyclic.anti (H.simpleGraphOn_mono hBsubset)
    exact T.2.toSimpleGraph_isTree.isAcyclic
  exact (not_isAcyclic_of_nonempty_even_degree Q hQne hQeven) hQacyclic

/-- Edge membership in the generic retained primal complement is literal
complementation of the mapped contracted-tree labels. -/
theorem mem_vacancyPrimalComplementGraph_edgeSet
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))} {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (T : ((rectangleDual (R + 1) (S + 1)).contract
      (vacancyDualEdges X)).SpanningTree)
    (p : (inducedGrid D).edgeSet) :
    p.1 ∈ (vacancyPrimalComplementGraph
      hR hS hD hdelete T).edgeSet ↔
      p ∉ vacancyContractedTreeDeletionEdges hR hS hD hdelete T := by
  classical
  letI : Fintype (inducedGrid D).edgeSet := Fintype.ofFinite _
  change p.1 ∈ ((edgeSetLabeledGraph (inducedGrid D)).simpleGraphOn
    ((Finset.univ \
      vacancyContractedTreeDeletionEdges hR hS hD hdelete T :
        Finset (inducedGrid D).edgeSet) : Set _)).edgeSet ↔ _
  induction hp : p.1 using Sym2.inductionOn with
  | _ u v =>
      rw [SimpleGraph.mem_edgeSet]
      constructor
      · rintro ⟨_, q, hq, hends⟩
        change q.1 = s(u, v) at hends
        have hqp : q = p := by
          apply Subtype.ext
          exact hends.trans hp.symm
        subst q
        simpa using hq
      · intro hpT
        have hpSel : p ∈ (Finset.univ \
            vacancyContractedTreeDeletionEdges hR hS hD hdelete T :
              Finset (inducedGrid D).edgeSet) := by
          simp [hpT]
        have huv : (inducedGrid D).Adj u v := by
          rw [← SimpleGraph.mem_edgeSet, ← hp]
          exact p.2
        exact ⟨huv.ne, p, hpSel, hp⟩

/-- The generic primal complement is a subgraph of the retained induced
grid. -/
theorem vacancyPrimalComplementGraph_le
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))} {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (T : ((rectangleDual (R + 1) (S + 1)).contract
      (vacancyDualEdges X)).SpanningTree) :
    vacancyPrimalComplementGraph hR hS hD hdelete T ≤ inducedGrid D := by
  classical
  letI : Fintype (inducedGrid D).edgeSet := Fintype.ofFinite _
  change (edgeSetLabeledGraph (inducedGrid D)).simpleGraphOn _ ≤ _
  intro u v huv
  have hsimple : (edgeSetLabeledGraph
      (inducedGrid D)).toSimpleGraph.Adj u v := by
    rw [← (edgeSetLabeledGraph (inducedGrid D)).simpleGraphOn_univ]
    exact (edgeSetLabeledGraph (inducedGrid D)).simpleGraphOn_mono
      (Set.subset_univ _) huv
  rw [edgeSetLabeledGraph_toSimpleGraph] at hsimple
  exact hsimple

/-- A contracted-dual tree therefore admits a retained-grid spanning tree
whose every edge is complementary to it.  This existential form avoids any
choice- or finite-instance commitments in downstream minor constructions. -/
theorem exists_vacancyPrimalComplementSpanningTree
    {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {X : Finset (Fin (R + 1) × Fin (S + 1))} {D : Finset Point}
    (hD : D ⊆ rectangle 0 0 (R + 1) (S + 1))
    (hdelete : ∀ p : Fin (R + 1) × Fin (S + 1),
      p ∈ X ↔ Boundary.ofNatPoint (finPoint p) ∉ D)
    (hconn : (inducedGrid D).Connected)
    (T : ((rectangleDual (R + 1) (S + 1)).contract
      (vacancyDualEdges X)).SpanningTree) :
    ∃ U : SimpleSpanningTreeType (inducedGrid D),
      U.1 ≤ vacancyPrimalComplementGraph hR hS hD hdelete T := by
  obtain ⟨U, hUK, hUtree⟩ :=
    (vacancyPrimalComplementGraph_connected
      hR hS hD hdelete hconn T).exists_isTree_le
  exact ⟨⟨U, hUK.trans
    (vacancyPrimalComplementGraph_le hR hS hD hdelete T), hUtree⟩, hUK⟩

end

end Dual
end SquareMaximality
