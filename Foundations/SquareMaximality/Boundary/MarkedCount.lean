import SquareMaximality.Boundary.Faces
import SquareMaximality.Boundary.King
import SquareMaximality.Multigraph.Trees

set_option autoImplicit false

/-!
# Exact marked-face counting

The numerical part of the marked-face identity is a finite Euler count.  This
file proves the one-dimensional run/edge identities, sums them over the rows
and columns, and isolates the genuinely planar input as a finite cellulation
certificate: a spanning tree of the occupied grid together with a bijection
between its cotree edges and the unmarked unit faces.
-/

namespace SquareMaximality

namespace Boundary

open Windows
open Multigraph

/-! ## Exact one-dimensional edge/run count -/

/-- Unit edges of the line whose two endpoints avoid `B`. -/
def occupiedLineEdgeStarts (L : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (Finset.range L).filter fun x => x ∉ B ∧ x + 1 ∉ B

/-- Starts of transitions from the complement of `B` into `B`. -/
private def riseTransitions (L : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (Finset.range L).filter fun x => x ∉ B ∧ x + 1 ∈ B

/-- Starts of transitions from `B` into its complement. -/
private def fallTransitions (L : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (Finset.range L).filter fun x => x ∈ B ∧ x + 1 ∉ B

private def positiveComplementRunStarts (L : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (runStarts L (line L \ B)).erase 0

private theorem card_positiveComplementRunStarts_eq_fall
    (L : ℕ) (B : Finset ℕ) :
    (positiveComplementRunStarts L B).card = (fallTransitions L B).card := by
  classical
  apply Finset.card_bij (fun x _ => x - 1)
  · intro x hx
    have hxRun : x ∈ runStarts L (line L \ B) :=
      (Finset.mem_erase.mp hx).2
    have hxne : x ≠ 0 := (Finset.mem_erase.mp hx).1
    have hs := mem_runStarts.mp hxRun
    simp only [fallTransitions, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_, ?_⟩
    · by_contra hpredB
      have hpredLine : x - 1 ∈ line L := mem_line.mpr (by omega)
      exact hs.2.2.resolve_left hxne
        (Finset.mem_sdiff.mpr ⟨hpredLine, hpredB⟩)
    · have hxComp := Finset.mem_sdiff.mp hs.2.1
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ x)] using hxComp.2
  · intro x₁ hx₁ x₂ hx₂ h
    have hx₁ne : x₁ ≠ 0 := (Finset.mem_erase.mp hx₁).1
    have hx₂ne : x₂ ≠ 0 := (Finset.mem_erase.mp hx₂).1
    omega
  · intro t ht
    have ht' := Finset.mem_filter.mp ht
    have htlt : t < L := Finset.mem_range.mp ht'.1
    refine ⟨t + 1, ?_, by omega⟩
    change t + 1 ∈ (runStarts L (line L \ B)).erase 0
    rw [Finset.mem_erase]
    refine ⟨by omega, mem_runStarts.mpr ?_⟩
    refine ⟨by omega, Finset.mem_sdiff.mpr ⟨mem_line.mpr (by omega), ht'.2.2⟩,
      Or.inr ?_⟩
    intro hcomp
    have htComp : t ∈ line L \ B := by simpa using hcomp
    exact (Finset.mem_sdiff.mp htComp).2 ht'.2.1

private theorem card_runStarts_complement_eq_fall_add_boundary
    (L : ℕ) (B : Finset ℕ) :
    (runStarts L (line L \ B)).card =
      (fallTransitions L B).card + if 0 ∈ B then 0 else 1 := by
  classical
  have hpositive := card_positiveComplementRunStarts_eq_fall L B
  by_cases h0 : 0 ∈ B
  · have h0not : 0 ∉ runStarts L (line L \ B) := by
      intro h
      exact (Finset.mem_sdiff.mp (mem_runStarts.mp h).2.1).2 h0
    simp [positiveComplementRunStarts, h0, h0not] at hpositive ⊢
    exact hpositive
  · have h0Run : 0 ∈ runStarts L (line L \ B) := by
      apply mem_runStarts.mpr
      exact ⟨by omega, Finset.mem_sdiff.mpr ⟨mem_line.mpr (by omega), h0⟩, Or.inl rfl⟩
    have herase := Finset.card_erase_add_one h0Run
    simp only [positiveComplementRunStarts] at hpositive
    simp [h0]
    omega

private def nonterminalRiseTransitions (L : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (riseTransitions L B).filter fun x => x + 1 ∉ rightBoundaryRun L B

private def terminalRiseTransitions (L : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (riseTransitions L B).filter fun x => x + 1 ∈ rightBoundaryRun L B

private theorem card_internalRunStarts_eq_nonterminalRise
    (L : ℕ) (B : Finset ℕ) :
    (internalRunStarts L B).card = (nonterminalRiseTransitions L B).card := by
  classical
  apply Finset.card_bij (fun a _ => a - 1)
  · intro a ha
    have hi := mem_internalRunStarts.mp ha
    simp only [nonterminalRiseTransitions, Finset.mem_filter, riseTransitions,
      Finset.mem_range]
    refine ⟨⟨by omega, hi.2.2.2.1, ?_⟩, ?_⟩
    · simpa [Nat.sub_add_cancel (by omega : 1 ≤ a)] using hi.2.2.1
    · simpa [Nat.sub_add_cancel (by omega : 1 ≤ a)] using hi.2.2.2.2
  · intro a₁ ha₁ a₂ ha₂ h
    have h₁ := (mem_internalRunStarts.mp ha₁).2.1
    have h₂ := (mem_internalRunStarts.mp ha₂).2.1
    omega
  · intro t ht
    have ht' := Finset.mem_filter.mp ht
    have hrise := Finset.mem_filter.mp ht'.1
    have htlt : t < L := Finset.mem_range.mp hrise.1
    refine ⟨t + 1, ?_, by omega⟩
    apply mem_internalRunStarts.mpr
    exact ⟨by omega, by omega, hrise.2.2, by simpa using hrise.2.1, ht'.2⟩

private theorem rise_eq_nonterminal_union_terminal (L : ℕ) (B : Finset ℕ) :
    riseTransitions L B =
      nonterminalRiseTransitions L B ∪ terminalRiseTransitions L B := by
  classical
  ext x
  simp only [nonterminalRiseTransitions, terminalRiseTransitions,
    Finset.mem_union, Finset.mem_filter]
  tauto

private theorem nonterminalRise_disjoint_terminal (L : ℕ) (B : Finset ℕ) :
    Disjoint (nonterminalRiseTransitions L B) (terminalRiseTransitions L B) := by
  classical
  rw [Finset.disjoint_left]
  intro x hx hy
  exact (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2

private theorem terminalRiseTransitions_eq_empty_of_not_mem
    {L : ℕ} {B : Finset ℕ} (hL : L ∉ B) :
    terminalRiseTransitions L B = ∅ := by
  classical
  ext x
  constructor
  · intro hx
    have hright := (Finset.mem_filter.mp hx).2
    have hrightMem := mem_rightBoundaryRun.mp hright
    exact (hL (hrightMem.2 (by simp [hrightMem.1]))).elim
  · intro hx
    simp at hx

private theorem terminalRiseTransitions_card_eq_one_of_mem_of_ne_line
    {L : ℕ} {B : Finset ℕ} (hB : B ⊆ line L)
    (hL : L ∈ B) (hne : B ≠ line L) :
    (terminalRiseTransitions L B).card = 1 := by
  classical
  have hrightNonempty : (rightBoundaryRun L B).Nonempty := by
    refine ⟨L, mem_rightBoundaryRun.mpr ⟨le_rfl, ?_⟩⟩
    simpa using hL
  let a := (rightBoundaryRun L B).min' hrightNonempty
  have haRight : a ∈ rightBoundaryRun L B :=
    (rightBoundaryRun L B).min'_mem hrightNonempty
  have haBounds := mem_rightBoundaryRun.mp haRight
  have haPos : 0 < a := by
    by_contra h
    have ha0 : a = 0 := by omega
    apply hne
    apply Finset.Subset.antisymm hB
    intro x hx
    have hxL := mem_line.mp hx
    exact haBounds.2 (by simpa [ha0] using hx)
  have hpredNot : a - 1 ∉ B := by
    intro hpred
    have hpredRight : a - 1 ∈ rightBoundaryRun L B := by
      apply mem_rightBoundaryRun.mpr
      refine ⟨by omega, ?_⟩
      intro z hz
      simp only [Finset.mem_Icc] at hz
      by_cases hzpred : z = a - 1
      · simpa [hzpred] using hpred
      · exact haBounds.2 (by
          simp only [Finset.mem_Icc]
          omega)
    have hmin := (rightBoundaryRun L B).min'_le (a - 1) hpredRight
    omega
  have hterminal : a - 1 ∈ terminalRiseTransitions L B := by
    simp only [terminalRiseTransitions, Finset.mem_filter, riseTransitions,
      Finset.mem_range]
    refine ⟨⟨by omega, hpredNot, ?_⟩, ?_⟩
    · simpa [Nat.sub_add_cancel (by omega : 1 ≤ a)] using
        rightBoundaryRun_subset L B haRight
    · simpa [Nat.sub_add_cancel (by omega : 1 ≤ a)] using haRight
  apply Finset.card_eq_one.mpr
  refine ⟨a - 1, ?_⟩
  ext x
  constructor
  · intro hx
    simp only [Finset.mem_singleton]
    have hx' := Finset.mem_filter.mp hx
    have hrise := Finset.mem_filter.mp hx'.1
    have hxRight := mem_rightBoundaryRun.mp hx'.2
    have hax : a ≤ x + 1 :=
      (rightBoundaryRun L B).min'_le (x + 1) hx'.2
    have hxa : x + 1 ≤ a := by
      by_contra h
      have ha_le_x : a ≤ x := by omega
      exact hrise.2.1 (haBounds.2 (by
        simp only [Finset.mem_Icc]
        exact ⟨ha_le_x, by omega⟩))
    omega
  · intro hx
    have hxEq : x = a - 1 := Finset.mem_singleton.mp hx
    simpa [hxEq] using hterminal

private theorem card_rise_eq_internal_add_boundary
    (L : ℕ) (B : Finset ℕ) (hB : B ⊆ line L) (hne : B ≠ line L) :
    (riseTransitions L B).card =
      (internalRunStarts L B).card + if L ∈ B then 1 else 0 := by
  classical
  rw [rise_eq_nonterminal_union_terminal,
    Finset.card_union_of_disjoint (nonterminalRise_disjoint_terminal L B),
    ← card_internalRunStarts_eq_nonterminalRise]
  by_cases hL : L ∈ B
  · rw [if_pos hL, terminalRiseTransitions_card_eq_one_of_mem_of_ne_line hB hL hne]
  · rw [if_neg hL, terminalRiseTransitions_eq_empty_of_not_mem hL]
    simp

private theorem int_card_filter (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((s.filter P).card : ℤ) = ∑ x ∈ s, if P x then 1 else 0 := by
  simp

private theorem rise_sub_fall_eq_endpoints (L : ℕ) (B : Finset ℕ) :
    ((riseTransitions L B).card : ℤ) - (fallTransitions L B).card =
      (if L ∈ B then 1 else 0) - (if 0 ∈ B then 1 else 0) := by
  classical
  let b : ℕ → ℤ := fun x => if x ∈ B then 1 else 0
  have hrise : ((riseTransitions L B).card : ℤ) =
      ∑ x ∈ Finset.range L, if x ∉ B ∧ x + 1 ∈ B then 1 else 0 := by
    simp [riseTransitions]
  have hfall : ((fallTransitions L B).card : ℤ) =
      ∑ x ∈ Finset.range L, if x ∈ B ∧ x + 1 ∉ B then 1 else 0 := by
    simp [fallTransitions]
  rw [hrise, hfall, ← Finset.sum_sub_distrib]
  calc
    (∑ x ∈ Finset.range L, ((if x ∉ B ∧ x + 1 ∈ B then (1 : ℤ) else 0) -
          (if x ∈ B ∧ x + 1 ∉ B then (1 : ℤ) else 0))) =
        ∑ x ∈ Finset.range L, (b (x + 1) - b x) := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [b]
      by_cases hx : x ∈ B <;> by_cases hx1 : x + 1 ∈ B <;> simp [hx, hx1]
    _ = b L - b 0 := Finset.sum_range_sub b L
    _ = (if L ∈ B then 1 else 0) - (if 0 ∈ B then 1 else 0) := rfl

private theorem card_complement_runStarts_eq_internal_add_one
    (L : ℕ) (B : Finset ℕ) (hB : B ⊆ line L) (hne : B ≠ line L) :
    (runStarts L (line L \ B)).card = (internalRunStarts L B).card + 1 := by
  classical
  have hrun := card_runStarts_complement_eq_fall_add_boundary L B
  have hrise := card_rise_eq_internal_add_boundary L B hB hne
  have hbalance := rise_sub_fall_eq_endpoints L B
  by_cases h0 : 0 ∈ B <;> by_cases hL : L ∈ B <;>
    simp [h0, hL] at hrun hrise hbalance ⊢ <;> omega

private def predecessorOccupied (L : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (line L \ B).filter fun x => 0 < x ∧ x - 1 ∉ B

private theorem card_occupiedLineEdgeStarts_eq_predecessorOccupied
    (L : ℕ) (B : Finset ℕ) :
    (occupiedLineEdgeStarts L B).card = (predecessorOccupied L B).card := by
  classical
  apply Finset.card_bij (fun x _ => x + 1)
  · intro x hx
    have hx' := Finset.mem_filter.mp hx
    have hxlt : x < L := Finset.mem_range.mp hx'.1
    simp only [predecessorOccupied, Finset.mem_filter, Finset.mem_sdiff, mem_line]
    exact ⟨⟨by omega, hx'.2.2⟩, by omega, by simpa using hx'.2.1⟩
  · intro x₁ hx₁ x₂ hx₂ h
    omega
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hyComp := Finset.mem_sdiff.mp hy'.1
    have hyL := mem_line.mp hyComp.1
    refine ⟨y - 1, ?_, by omega⟩
    simp only [occupiedLineEdgeStarts, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, hy'.2.2, ?_⟩
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ y)] using hyComp.2

private theorem runStarts_union_predecessorOccupied
    (L : ℕ) (B : Finset ℕ) :
    runStarts L (line L \ B) ∪ predecessorOccupied L B = line L \ B := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hrun | hpred
    · exact (mem_runStarts.mp hrun).2.1
    · exact (Finset.mem_filter.mp hpred).1
  · intro hx
    have hx' := Finset.mem_sdiff.mp hx
    by_cases hzero : x = 0
    · apply Finset.mem_union.mpr
      exact Or.inl (mem_runStarts.mpr ⟨mem_line.mp hx'.1, hx, Or.inl hzero⟩)
    · by_cases hpredB : x - 1 ∈ B
      · apply Finset.mem_union.mpr
        exact Or.inl (mem_runStarts.mpr ⟨mem_line.mp hx'.1, hx, Or.inr (by
          intro hcomp
          exact (Finset.mem_sdiff.mp hcomp).2 hpredB)⟩)
      · apply Finset.mem_union.mpr
        exact Or.inr (Finset.mem_filter.mpr ⟨hx, by omega, hpredB⟩)

private theorem runStarts_disjoint_predecessorOccupied (L : ℕ) (B : Finset ℕ) :
    Disjoint (runStarts L (line L \ B)) (predecessorOccupied L B) := by
  classical
  rw [Finset.disjoint_left]
  intro x hrun hpred
  have hs := mem_runStarts.mp hrun
  have hp := Finset.mem_filter.mp hpred
  rcases hs.2.2 with hzero | hnot
  · omega
  · exact hnot (Finset.mem_sdiff.mpr ⟨mem_line.mpr (by omega), hp.2.2⟩)

/-- Exact one-dimensional Euler identity.  The line must have at least one
occupied point; equivalently `B` is not the full line. -/
theorem occupiedLineEdges_add_vacancies_add_internalRuns
    (L : ℕ) (B : Finset ℕ) (hB : B ⊆ line L) (hne : B ≠ line L) :
    (occupiedLineEdgeStarts L B).card + B.card +
        (internalRunStarts L B).card = L := by
  have hcompCard : (line L \ B).card + B.card = L + 1 := by
    rw [Finset.card_sdiff_add_card_eq_card hB]
    simp [line]
  have hpartition :
      (runStarts L (line L \ B)).card + (predecessorOccupied L B).card =
        (line L \ B).card := by
    rw [← Finset.card_union_of_disjoint
      (runStarts_disjoint_predecessorOccupied L B),
      runStarts_union_predecessorOccupied]
  rw [← card_occupiedLineEdgeStarts_eq_predecessorOccupied,
    card_complement_runStarts_eq_internal_add_one L B hB hne] at hpartition
  omega

/-! ## Occupied grid edges -/

/-- Surviving horizontal grid edges, indexed by row and left endpoint. -/
def horizontalOccupiedEdges (R S : ℕ) (V : Finset LatticePoint) :
    Finset (Σ _y : ℕ, ℕ) :=
  (line S).sigma fun y => occupiedLineEdgeStarts R (row R V y)

/-- Surviving vertical grid edges, indexed by column and bottom endpoint. -/
def verticalOccupiedEdges (R S : ℕ) (V : Finset LatticePoint) :
    Finset (Σ _x : ℕ, ℕ) :=
  (line R).sigma fun x => occupiedLineEdgeStarts S (column S V x)

/-- Grid vertices not belonging to the vacancy set. -/
def occupiedVertices (R S : ℕ) (V : Finset LatticePoint) : Finset LatticePoint :=
  grid R S \ V

abbrev OccupiedVertex (R S : ℕ) (V : Finset LatticePoint) :=
  ↑(occupiedVertices R S V)

/-- Edge labels distinguish orientation even before their endpoints are read. -/
abbrev OccupiedEdge (R S : ℕ) (V : Finset LatticePoint) :=
  Sum (↑(horizontalOccupiedEdges R S V)) (↑(verticalOccupiedEdges R S V))

private def horizontalLeftVertex {R S : ℕ} {V : Finset LatticePoint}
    (e : ↑(horizontalOccupiedEdges R S V)) : OccupiedVertex R S V := by
  let x := e.1.2
  let y := e.1.1
  have he := Finset.mem_sigma.mp e.2
  have hx := Finset.mem_filter.mp he.2
  have hxlt : x < R := Finset.mem_range.mp hx.1
  have hyS : y ≤ S := mem_line.mp he.1
  refine ⟨(x, y), Finset.mem_sdiff.mpr ⟨mem_grid.mpr ⟨by omega, hyS⟩, ?_⟩⟩
  intro hV
  exact hx.2.1 (mem_row.mpr ⟨by omega, hV⟩)

private def horizontalRightVertex {R S : ℕ} {V : Finset LatticePoint}
    (e : ↑(horizontalOccupiedEdges R S V)) : OccupiedVertex R S V := by
  let x := e.1.2
  let y := e.1.1
  have he := Finset.mem_sigma.mp e.2
  have hx := Finset.mem_filter.mp he.2
  have hxlt : x < R := Finset.mem_range.mp hx.1
  have hyS : y ≤ S := mem_line.mp he.1
  refine ⟨(x + 1, y), Finset.mem_sdiff.mpr ⟨mem_grid.mpr ⟨by omega, hyS⟩, ?_⟩⟩
  intro hV
  exact hx.2.2 (mem_row.mpr ⟨by omega, hV⟩)

private def verticalBottomVertex {R S : ℕ} {V : Finset LatticePoint}
    (e : ↑(verticalOccupiedEdges R S V)) : OccupiedVertex R S V := by
  let x := e.1.1
  let y := e.1.2
  have he := Finset.mem_sigma.mp e.2
  have hy := Finset.mem_filter.mp he.2
  have hylt : y < S := Finset.mem_range.mp hy.1
  have hxR : x ≤ R := mem_line.mp he.1
  refine ⟨(x, y), Finset.mem_sdiff.mpr ⟨mem_grid.mpr ⟨hxR, by omega⟩, ?_⟩⟩
  intro hV
  exact hy.2.1 (mem_column.mpr ⟨by omega, hV⟩)

private def verticalTopVertex {R S : ℕ} {V : Finset LatticePoint}
    (e : ↑(verticalOccupiedEdges R S V)) : OccupiedVertex R S V := by
  let x := e.1.1
  let y := e.1.2
  have he := Finset.mem_sigma.mp e.2
  have hy := Finset.mem_filter.mp he.2
  have hylt : y < S := Finset.mem_range.mp hy.1
  have hxR : x ≤ R := mem_line.mp he.1
  refine ⟨(x, y + 1), Finset.mem_sdiff.mpr ⟨mem_grid.mpr ⟨hxR, by omega⟩, ?_⟩⟩
  intro hV
  exact hy.2.2 (mem_column.mpr ⟨by omega, hV⟩)

/-- The occupied rectangular grid as an edge-labelled graph. -/
def occupiedGridMultigraph (R S : ℕ) (V : Finset LatticePoint) :
    Multigraph.LabeledMultigraph (OccupiedVertex R S V) (OccupiedEdge R S V) where
  ends
    | Sum.inl e => s(horizontalLeftVertex e, horizontalRightVertex e)
    | Sum.inr e => s(verticalBottomVertex e, verticalTopVertex e)

/-- A finite, constructive form of the planar cellulation statement.

The selected labels form a spanning tree of the occupied grid.  Every label
outside that tree is paired bijectively with one unmarked unit face.  This is
the exact topological input in Euler's formula; it asserts no marked-face
cardinality. -/
structure GridCellulationCertificate (R S : ℕ) (V : Finset LatticePoint) where
  tree : Finset (OccupiedEdge R S V)
  spanning : (occupiedGridMultigraph R S V).IsSpanningTree tree
  cotreeEquiv :
    {e : OccupiedEdge R S V // e ∉ tree} ≃
      {z : LatticePoint // z ∈ unmarkedFaces R S V}

private theorem cellulation_euler
    {R S : ℕ} {V : Finset LatticePoint}
    (c : GridCellulationCertificate R S V) :
    (occupiedVertices R S V).card + (unmarkedFaces R S V).card =
      (horizontalOccupiedEdges R S V).card +
        (verticalOccupiedEdges R S V).card + 1 := by
  classical
  have htree : c.tree.card + 1 = (occupiedVertices R S V).card := by
    simpa [OccupiedVertex] using c.spanning.card_edges_add_one
  have hfaces : Fintype.card {e : OccupiedEdge R S V // e ∉ c.tree} =
      (unmarkedFaces R S V).card := by
    rw [Fintype.card_congr c.cotreeEquiv]
    exact Fintype.card_coe _
  have hselected : Fintype.card {e : OccupiedEdge R S V // e ∈ c.tree} =
      c.tree.card := Fintype.card_coe _
  have hcomplement :
      Fintype.card {e : OccupiedEdge R S V // e ∉ c.tree} =
        Fintype.card (OccupiedEdge R S V) -
          Fintype.card {e : OccupiedEdge R S V // e ∈ c.tree} :=
    Fintype.card_subtype_compl (fun e : OccupiedEdge R S V => e ∈ c.tree)
  have hedges : Fintype.card (OccupiedEdge R S V) =
      (horizontalOccupiedEdges R S V).card +
        (verticalOccupiedEdges R S V).card := by
    simp [OccupiedEdge]
  have hle : c.tree.card ≤ Fintype.card (OccupiedEdge R S V) := by
    simpa using Finset.card_le_univ c.tree
  rw [hselected, hedges] at hcomplement
  omega

private theorem sum_card_columns (R S : ℕ) (V : Finset LatticePoint)
    (hV : V ⊆ grid R S) :
    (∑ x ∈ line R, (column S V x).card) = V.card := by
  classical
  let C : Finset (Σ _x : ℕ, ℕ) := (line R).sigma fun x => column S V x
  have hcard : C.card = V.card := by
    symm
    apply Finset.card_bij (fun z _ => ⟨z.1, z.2⟩)
    · intro z hz
      have hgrid := mem_grid.mp (hV hz)
      simp only [C, Finset.mem_sigma]
      exact ⟨mem_line.mpr hgrid.1, mem_column.mpr ⟨hgrid.2, hz⟩⟩
    · rintro z₁ hz₁ z₂ hz₂ h
      have hx : z₁.1 = z₂.1 := congrArg Sigma.fst h
      have hy : z₁.2 = z₂.2 := congrArg (fun z => z.2) h
      exact Prod.ext hx hy
    · rintro ⟨x, y⟩ h
      simp only [C, Finset.mem_sigma] at h
      exact ⟨(x, y), (mem_column.mp h.2).2, rfl⟩
  simpa [C] using hcard

private theorem card_horizontalOccupiedEdges_add
    {R S : ℕ} {V : Finset LatticePoint}
    (hV : V ⊆ grid R S)
    (hrows : ∀ y ≤ S, row R V y ≠ line R) :
    (horizontalOccupiedEdges R S V).card + V.card +
        horizontalInternalRunCount R S V = R * (S + 1) := by
  have heach : ∀ y ∈ line S,
      (occupiedLineEdgeStarts R (row R V y)).card + (row R V y).card +
          (internalRunStarts R (row R V y)).card = R := by
    intro y hy
    exact occupiedLineEdges_add_vacancies_add_internalRuns R (row R V y)
      (row_subset_line R V y) (hrows y (mem_line.mp hy))
  have hsum := Finset.sum_congr rfl heach
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_card_rows R S V hV] at hsum
  simpa [horizontalOccupiedEdges, horizontalInternalRunCount, line,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum

private theorem card_verticalOccupiedEdges_add
    {R S : ℕ} {V : Finset LatticePoint}
    (hV : V ⊆ grid R S)
    (hcols : ∀ x ≤ R, column S V x ≠ line S) :
    (verticalOccupiedEdges R S V).card + V.card +
        verticalInternalRunCount R S V = (R + 1) * S := by
  have heach : ∀ x ∈ line R,
      (occupiedLineEdgeStarts S (column S V x)).card + (column S V x).card +
          (internalRunStarts S (column S V x)).card = S := by
    intro x hx
    exact occupiedLineEdges_add_vacancies_add_internalRuns S (column S V x)
      (column_subset_line S V x) (hcols x (mem_line.mp hx))
  have hsum := Finset.sum_congr rfl heach
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_card_columns R S V hV] at hsum
  simpa [verticalOccupiedEdges, verticalInternalRunCount, line,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum

private theorem card_occupiedVertices_add_vacancies
    {R S : ℕ} {V : Finset LatticePoint} (hV : V ⊆ grid R S) :
    (occupiedVertices R S V).card + V.card = (R + 1) * (S + 1) := by
  rw [occupiedVertices, Finset.card_sdiff_add_card_eq_card hV]
  simp [grid, line]

/-- Exact marked-face identity from the finite line counts and a planar
cellulation certificate.  The only geometric side conditions say that every
row and column has an occupied vertex. -/
theorem card_markedFaces_eq_vacancies_add_internalRuns
    {R S : ℕ} {V : Finset LatticePoint}
    (hV : V ⊆ grid R S)
    (hrows : ∀ y ≤ S, row R V y ≠ line R)
    (hcols : ∀ x ≤ R, column S V x ≠ line S)
    (hcell : GridCellulationCertificate R S V) :
    (markedFaces R S V).card = V.card +
      horizontalInternalRunCount R S V + verticalInternalRunCount R S V := by
  have hh := card_horizontalOccupiedEdges_add hV hrows
  have hv := card_verticalOccupiedEdges_add hV hcols
  have hvertices := card_occupiedVertices_add_vacancies hV
  have heuler := cellulation_euler hcell
  have hfaces := card_markedFaces_add_card_unmarkedFaces R S V
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at hh hv hvertices
  omega

private theorem row_ne_line_of_subset
    {R : ℕ} {V W : Finset LatticePoint} (hVW : V ⊆ W) {y : ℕ}
    (hW : row R W y ≠ line R) : row R V y ≠ line R := by
  intro hV
  apply hW
  apply Finset.Subset.antisymm (row_subset_line R W y)
  intro x hx
  have hxV : x ∈ row R V y := by simpa [hV] using hx
  have hxData := mem_row.mp hxV
  exact mem_row.mpr ⟨hxData.1, hVW hxData.2⟩

private theorem column_ne_line_of_subset
    {S : ℕ} {V W : Finset LatticePoint} (hVW : V ⊆ W) {x : ℕ}
    (hW : column S W x ≠ line S) : column S V x ≠ line S := by
  intro hV
  apply hW
  apply Finset.Subset.antisymm (column_subset_line S W x)
  intro y hy
  have hyV : y ∈ column S V x := by simpa [hV] using hy
  have hyData := mem_column.mp hyV
  exact mem_column.mpr ⟨hyData.1, hVW hyData.2⟩

/-- The manuscript's normalized setting.  Connected minimality discharges
the row/column side conditions, and boundary attachment supplies the precise
vacancy set.  The finite planar cellulation certificate is the sole remaining
hypothesis. -/
theorem card_markedFaces_encodedBoundaryVacancies_of_cellulation
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    (hcell : GridCellulationCertificate R S
      (boundaryVacancies R S (encodedVacancies R S A))) :
    (markedFaces R S (boundaryVacancies R S (encodedVacancies R S A))).card =
      (boundaryVacancies R S (encodedVacancies R S A)).card +
        horizontalInternalRunCount R S
          (boundaryVacancies R S (encodedVacancies R S A)) +
        verticalInternalRunCount R S
          (boundaryVacancies R S (encodedVacancies R S A)) := by
  let W := encodedVacancies R S A
  let B := boundaryVacancies R S W
  have hWGrid : W ⊆ grid R S := by
    intro z hz
    exact mem_grid.mpr ⟨(mem_encodedVacancies.mp hz).1,
      (mem_encodedVacancies.mp hz).2.1⟩
  have hBGrid : B ⊆ grid R S := fun _ hz =>
    hWGrid (boundaryVacancies_subset R S W hz)
  have hrows : ∀ y ≤ S, row R B y ≠ line R := by
    intro y hy
    exact row_ne_line_of_subset (boundaryVacancies_subset R S W)
      (encodedVacancies_row_ne_line hHull hconn hy)
  have hcols : ∀ x ≤ R, column S B x ≠ line S := by
    intro x hx
    exact column_ne_line_of_subset (boundaryVacancies_subset R S W)
      (encodedVacancies_column_ne_line hHull hconn hx)
  exact card_markedFaces_eq_vacancies_add_internalRuns hBGrid hrows hcols hcell

end Boundary

end SquareMaximality
