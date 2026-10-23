module

public import SquareMaximality.Dual.TappSeries

@[expose] public section

/-!
# Rectangular words-on-a-page geometry for the Tapp bulk argument

This module records the finite geometric part of the entropy contradiction
used to prove the half-plane multiplier bound.  A square grid is enumerated
from its top row downwards and from left to right within each row.  Every
non-boundary step is the southeast corner of a complete unit square.

The analytic bulk limit and the final contradiction are kept in a later
module; the statements here are finite.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Dual

/-- Translating both natural-coordinate points preserves words-on-a-page
order. -/
theorem wordsOnPageKey_translate_lt
    {u v : Boundary.LatticePoint} (dx dy : ℕ)
    (h : wordsOnPageKey u < wordsOnPageKey v) :
    wordsOnPageKey (u.1 + dx, u.2 + dy) <
      wordsOnPageKey (v.1 + dx, v.2 + dy) := by
  simp only [wordsOnPageKey, Prod.Lex.lt_iff, ofLex_toLex] at h ⊢
  rcases h with h | h
  · left
    omega
  · right
    constructor <;> omega

/-- Translating both endpoints preserves natural square-lattice
adjacency. -/
theorem faceLattice_translate_adj_iff
    (u v : Boundary.LatticePoint) (dx dy : ℕ) :
    Boundary.faceLattice.Adj (u.1 + dx, u.2 + dy)
        (v.1 + dx, v.2 + dy) ↔
      Boundary.faceLattice.Adj u v := by
  simp only [Boundary.faceLattice, Boundary.natManhattanDist,
    Nat.dist_add_add_right]

/-- The ordinary simple `n x n` grid on finite natural coordinates. -/
def squareGrid (n : ℕ) : SimpleGraph (Fin n × Fin n) :=
  (rectanglePrimal n n).toSimpleGraph

/-- Natural-coordinate embedding of an `n x n` grid. -/
def squareGridCoord (n : ℕ) :
    (Fin n × Fin n) ↪ Boundary.LatticePoint where
  toFun := finPoint
  inj' := finPoint_injective

@[simp] theorem squareGridCoord_apply (n : ℕ) (p : Fin n × Fin n) :
    squareGridCoord n p = (p.1.1, p.2.1) :=
  rfl

/-- The finite square grid is a subgraph of the natural square lattice. -/
theorem squareGrid_le_faceLattice (n : ℕ) :
    squareGrid n ≤ Boundary.faceLattice.comap (squareGridCoord n) := by
  intro p q hpq
  rw [squareGrid, rectanglePrimal_toSimpleGraph] at hpq
  change Boundary.natManhattanDist (finPoint p) (finPoint q) = 1
  rcases hpq with hpq | hpq
  · rcases hpq with ⟨hpq, hsecond⟩
    rw [SimpleGraph.pathGraph_adj] at hpq
    simp only [Boundary.natManhattanDist, finPoint]
    rcases hpq with hpq | hpq <;>
      simp only [hsecond, Nat.dist_self, add_zero] <;>
      simp [Nat.dist] <;> omega
  · rcases hpq with ⟨hpq, hfirst⟩
    rw [SimpleGraph.pathGraph_adj] at hpq
    simp only [Boundary.natManhattanDist, finPoint]
    rcases hpq with hpq | hpq <;>
      simp only [hfirst, Nat.dist_self, zero_add] <;>
      simp [Nat.dist] <;> omega

/-- Finite square-grid adjacency is exactly natural lattice adjacency after
forgetting coordinate bounds. -/
theorem squareGrid_adj_iff_faceLattice
    {n : ℕ} (p q : Fin n × Fin n) :
    (squareGrid n).Adj p q ↔
      Boundary.faceLattice.Adj (squareGridCoord n p) (squareGridCoord n q) := by
  constructor
  · intro hpq
    exact squareGrid_le_faceLattice n hpq
  · intro hpq
    rw [squareGrid, rectanglePrimal_toSimpleGraph]
    change Boundary.natManhattanDist (finPoint p) (finPoint q) = 1 at hpq
    simp only [Boundary.natManhattanDist, finPoint] at hpq
    unfold Nat.dist at hpq
    simp only [SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj]
    by_cases hxy : p.1.1 = q.1.1
    · right
      refine ⟨?_, Fin.ext hxy⟩
      omega
    · left
      refine ⟨?_, ?_⟩
      · omega
      · apply Fin.ext
        omega

/-- A positive square grid is connected. -/
theorem squareGrid_connected {n : ℕ} (hn : 0 < n) :
    (squareGrid n).Connected := by
  change (rectanglePrimal n n).toSimpleGraph.Connected
  exact rectanglePrimal_connected hn hn

/-- The finite-coordinate square grid has the manuscript's rectangular
spanning-tree count. -/
theorem treeCount_squareGrid (n : ℕ) :
    treeCount (squareGrid n) = tauRect n n := by
  rw [squareGrid, rectanglePrimal_toSimpleGraph]
  unfold tauRect tau
  exact (treeCount_congr (standardRectangleGridIso n n)).symm

/-- The product of all words-on-a-page prefix multipliers of a positive
square is exactly its spanning-tree count. -/
theorem product_squareGrid_prefixMultipliers {n : ℕ} (hn : 0 < n) :
    ∏ k ∈ Finset.range (Fintype.card (Fin n × Fin n)),
        wordsPrefixMultiplier (squareGrid n) (squareGridCoord n) k =
      tauRect n n := by
  rw [product_prefixMultipliers]
  rw [spanningForestCount_eq_treeCount (squareGrid_connected hn)]
  exact_mod_cast treeCount_squareGrid n

/-- Index of a square-grid vertex in words-on-a-page order. -/
noncomputable def squareGridIndex {n : ℕ} (p : Fin n × Fin n) : ℕ :=
  ((wordsOnPageOrderIso (squareGridCoord n)).toEquiv.symm p).1

theorem squareGridIndex_lt {n : ℕ} (p : Fin n × Fin n) :
    squareGridIndex p < Fintype.card (Fin n × Fin n) :=
  ((wordsOnPageOrderIso (squareGridCoord n)).toEquiv.symm p).2

/-- Looking up the canonical enumeration at a vertex's index returns that
vertex. -/
theorem squareGridOrderIso_at_index {n : ℕ} (p : Fin n × Fin n) :
    (wordsOnPageOrderIso (squareGridCoord n)).toEquiv
      ⟨squareGridIndex p, squareGridIndex_lt p⟩ = p := by
  exact (wordsOnPageOrderIso (squareGridCoord n)).toEquiv.apply_symm_apply p

/-- Distinct grid vertices have distinct words-on-a-page indices. -/
theorem squareGridIndex_injective {n : ℕ} :
    Function.Injective (squareGridIndex (n := n)) := by
  intro p q hpq
  have hfin :
      (wordsOnPageOrderIso (squareGridCoord n)).toEquiv.symm p =
        (wordsOnPageOrderIso (squareGridCoord n)).toEquiv.symm q := by
    apply Fin.ext
    exact hpq
  exact (wordsOnPageOrderIso (squareGridCoord n)).toEquiv.symm.injective hfin

/-! ## Translated copies of a fixed finite half-plane window -/

/-- Translation parameters which keep an `X x Y` box inside an `n x n`
square. -/
abbrev SquareScanShift (n X Y : ℕ) :=
  Fin (n - X + 1) × Fin (n - Y + 1)

@[simp] theorem card_squareScanShift (n X Y : ℕ) :
    Fintype.card (SquareScanShift n X Y) =
      (n - X + 1) * (n - Y + 1) := by
  simp [SquareScanShift]

/-- The southeast current vertex obtained by translating the window based
at `z` by the displayed scan shift. -/
def squareScanCurrent
    (z : Boundary.LatticePoint) {n X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y)
    (hX : X ≤ n) (hY : Y ≤ n) (d : SquareScanShift n X Y) :
    Fin n × Fin n :=
  (⟨z.1 + 1 + d.1.1, by omega⟩, ⟨z.2 + d.2.1, by omega⟩)

@[simp] theorem squareScanCurrent_coord
    (z : Boundary.LatticePoint) {n X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y)
    (hX : X ≤ n) (hY : Y ≤ n) (d : SquareScanShift n X Y) :
    squareGridCoord n (squareScanCurrent z hx hy hX hY d) =
      (z.1 + 1 + d.1.1, z.2 + d.2.1) :=
  rfl

/-- Different scan translations give different current vertices. -/
theorem squareScanCurrent_injective
    (z : Boundary.LatticePoint) {n X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y)
    (hX : X ≤ n) (hY : Y ≤ n) :
    Function.Injective (squareScanCurrent z hx hy hX hY) := by
  intro d e hde
  have hx' := congrArg (fun p : Fin n × Fin n ↦ p.1.1) hde
  have hy' := congrArg (fun p : Fin n × Fin n ↦ p.2.1) hde
  apply Prod.ext <;> apply Fin.ext
  · simp only [squareScanCurrent] at hx'
    omega
  · simp only [squareScanCurrent] at hy'
    omega

/-- Words-on-a-page index of one translated scan current. -/
noncomputable def squareScanIndex
    (z : Boundary.LatticePoint) {n X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y)
    (hX : X ≤ n) (hY : Y ≤ n) (d : SquareScanShift n X Y) : ℕ :=
  squareGridIndex (squareScanCurrent z hx hy hX hY d)

/-- Set of all prefix indices hit by translations of a fixed window. -/
noncomputable def squareScanIndices
    (z : Boundary.LatticePoint) {n X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y)
    (hX : X ≤ n) (hY : Y ≤ n) : Finset ℕ := by
  classical
  exact Finset.univ.image (squareScanIndex z hx hy hX hY)

/-- Scan indices are distinct because both translation and enumeration are
injective. -/
theorem squareScanIndex_injective
    (z : Boundary.LatticePoint) {n X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y)
    (hX : X ≤ n) (hY : Y ≤ n) :
    Function.Injective (squareScanIndex z hx hy hX hY) :=
  squareGridIndex_injective.comp
    (squareScanCurrent_injective z hx hy hX hY)

@[simp] theorem card_squareScanIndices
    (z : Boundary.LatticePoint) {n X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y)
    (hX : X ≤ n) (hY : Y ≤ n) :
    (squareScanIndices z hx hy hX hY).card =
      (n - X + 1) * (n - Y + 1) := by
  classical
  rw [squareScanIndices,
    Finset.card_image_iff.mpr (squareScanIndex_injective z hx hy hX hY).injOn]
  simp

/-- Every scan index belongs to the full prefix-index range. -/
theorem squareScanIndices_subset_range
    (z : Boundary.LatticePoint) {n X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y)
    (hX : X ≤ n) (hY : Y ≤ n) :
    squareScanIndices z hx hy hX hY ⊆
      Finset.range (Fintype.card (Fin n × Fin n)) := by
  classical
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨d, _hd, rfl⟩
  exact Finset.mem_range.mpr (squareGridIndex_lt _)

/-- Membership in the scan-index set is witnessed by a translated current. -/
theorem mem_squareScanIndices_iff
    (z : Boundary.LatticePoint) {n X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y)
    (hX : X ≤ n) (hY : Y ≤ n) (k : ℕ) :
    k ∈ squareScanIndices z hx hy hX hY ↔
      ∃ d : SquareScanShift n X Y, squareScanIndex z hx hy hX hY d = k := by
  classical
  simp [squareScanIndices]

/-- Southwest corner of the unit square whose southeast corner is `p`. -/
def squareStepSW {n : ℕ} (p : Fin n × Fin n) (hx : 0 < p.1.1) :
    Fin n × Fin n :=
  (⟨p.1.1 - 1, by omega⟩, p.2)

/-- Northwest corner of the unit square whose southeast corner is `p`. -/
def squareStepNW {n : ℕ} (p : Fin n × Fin n)
    (hx : 0 < p.1.1) (hy : p.2.1 + 1 < n) : Fin n × Fin n :=
  (⟨p.1.1 - 1, by omega⟩, ⟨p.2.1 + 1, hy⟩)

/-- Northeast corner of the unit square whose southeast corner is `p`. -/
def squareStepNE {n : ℕ} (p : Fin n × Fin n)
    (hy : p.2.1 + 1 < n) : Fin n × Fin n :=
  (p.1, ⟨p.2.1 + 1, hy⟩)

/-- Every square-grid vertex away from the left and top sides is the
southeast corner of a complete unit square. -/
theorem squareGrid_containsUnitSquare
    {n : ℕ} (p : Fin n × Fin n)
    (hx : 0 < p.1.1) (hy : p.2.1 + 1 < n) :
    ContainsUnitSquare (squareGrid n) (squareGridCoord n)
      (p.1.1 - 1, p.2.1) := by
  let sw := squareStepSW p hx
  let se := p
  let nw := squareStepNW p hx hy
  let ne := squareStepNE p hy
  refine ⟨sw, se, nw, ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Prod.ext
    · simp [sw, squareStepSW]
    · simp [sw, squareStepSW]
  · apply Prod.ext
    · simp [se]
      omega
    · simp [se]
  · apply Prod.ext
    · simp [nw, squareStepNW]
    · simp [nw, squareStepNW]
  · apply Prod.ext
    · simp [ne, squareStepNE]
      omega
    · simp [ne, squareStepNE]
  · rw [squareGrid, rectanglePrimal_toSimpleGraph]
    left
    constructor
    · rw [SimpleGraph.pathGraph_adj]
      left
      simp [sw, se, squareStepSW]
      omega
    · rfl

  · rw [squareGrid, rectanglePrimal_toSimpleGraph]
    right
    constructor
    · rw [SimpleGraph.pathGraph_adj]
      left
      simp [sw, nw, squareStepSW, squareStepNW]
    · rfl
  · rw [squareGrid, rectanglePrimal_toSimpleGraph]
    right
    constructor
    · rw [SimpleGraph.pathGraph_adj]
      left
      simp [se, ne, squareStepNE]
    · rfl
  · rw [squareGrid, rectanglePrimal_toSimpleGraph]
    left
    constructor
    · rw [SimpleGraph.pathGraph_adj]
      left
      simp [nw, ne, squareStepNW, squareStepNE]
      omega
    · rfl

/-- Every scan current has a complete unit square immediately to its
northwest. -/
theorem squareScanCurrent_containsUnitSquare
    (z : Boundary.LatticePoint) {n X Y : ℕ}
    (hx : z.1 + 1 < X) (hy : z.2 + 1 < Y)
    (hX : X ≤ n) (hY : Y ≤ n) (d : SquareScanShift n X Y) :
    ContainsUnitSquare (squareGrid n) (squareGridCoord n)
      (z.1 + d.1.1, z.2 + d.2.1) := by
  let p := squareScanCurrent z hx hy hX hY d
  have hpx : 0 < p.1.1 := by
    simp only [p, squareScanCurrent]
    omega
  have hpy : p.2.1 + 1 < n := by
    simp only [p, squareScanCurrent]
    omega
  have h := squareGrid_containsUnitSquare p hpx hpy
  have hxbase : p.1.1 - 1 = z.1 + d.1.1 := by
    simp only [p, squareScanCurrent]
    omega
  have hybase : p.2.1 = z.2 + d.2.1 := by
    rfl
  rw [hxbase, hybase] at h
  exact h

end Dual
end SquareMaximality
