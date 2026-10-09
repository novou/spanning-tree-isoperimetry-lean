import SquareMaximality.Boundary.Cellulation
import SquareMaximality.Boundary.KingRuns

set_option autoImplicit false

/-!
# The finite Euler identity for boundary-attached vacancies

For each unmarked unit face we delete its top horizontal edge.  These labels
are distinct.  A deleted horizontal edge can be bypassed around the square
below it; if the bottom edge is also deleted, the same argument descends one
row.  Since no top-face label lies in row zero, the recursion terminates.

Thus deleting one edge per unmarked face preserves connectivity.  The
resulting edge count gives one half of the finite Euler equality without any
planar-embedding theorem.
-/

namespace SquareMaximality
namespace Boundary

open Multigraph
open Windows

noncomputable section

/-- An unmarked face, bundled with its membership proof. -/
abbrev UnmarkedFace (R S : ℕ) (V : Finset LatticePoint) :=
  ↑(unmarkedFaces R S V)

private theorem corner_not_mem_of_unmarked
    {R S : ℕ} {V : Finset LatticePoint}
    {z w : LatticePoint} (hzU : z ∈ unmarkedFaces R S V)
    (hw : w ∈ faceCorners z) : w ∉ V := by
  intro hwV
  have hz := (mem_unmarkedFaces.mp hzU).2
  have : w ∈ faceCorners z ∩ V := Finset.mem_inter.mpr ⟨hw, hwV⟩
  rw [hz] at this
  simp at this

/-- The top horizontal occupied-edge label of an unmarked face. -/
def unmarkedFaceTopLabel
    {R S : ℕ} {V : Finset LatticePoint}
    (z : UnmarkedFace R S V) : OccupiedEdge R S V := by
  let a : Σ _y : ℕ, ℕ := ⟨z.1.2 + 1, z.1.1⟩
  have ha : a ∈ horizontalOccupiedEdges R S V := by
    have hzFace := (mem_unmarkedFaces.mp z.2).1
    have hzBounds := mem_faceIndices.mp hzFace
    simp only [horizontalOccupiedEdges, Finset.mem_sigma]
    refine ⟨Windows.mem_line.mpr hzBounds.2, ?_⟩
    simp only [occupiedLineEdgeStarts, Finset.mem_filter, Finset.mem_range]
    dsimp [a]
    refine ⟨by omega, ?_, ?_⟩
    · intro hrow
      exact (corner_not_mem_of_unmarked z.2
        (w := (z.1.1, z.1.2 + 1))
        (mem_faceCorners.mpr ⟨le_rfl, by omega, by omega, le_rfl⟩))
          (mem_row.mp hrow).2
    · intro hrow
      exact (corner_not_mem_of_unmarked z.2
        (w := (z.1.1 + 1, z.1.2 + 1))
        (mem_faceCorners.mpr ⟨by omega, le_rfl, by omega, le_rfl⟩))
          (mem_row.mp hrow).2
  exact Sum.inl ⟨a, ha⟩

theorem unmarkedFaceTopLabel_injective (R S : ℕ) (V : Finset LatticePoint) :
    Function.Injective
      (unmarkedFaceTopLabel : UnmarkedFace R S V → OccupiedEdge R S V) := by
  intro z w h
  apply Subtype.ext
  have hsigma := Sum.inl.inj h
  have hy : z.1.2 + 1 = w.1.2 + 1 := congrArg (fun e => e.1.1) hsigma
  have hx : z.1.1 = w.1.1 := congrArg (fun e => e.1.2) hsigma
  exact Prod.ext hx (by omega)

/-- Exactly one distinct occupied label is selected per unmarked face. -/
def unmarkedFaceTopLabels (R S : ℕ) (V : Finset LatticePoint) :
    Finset (OccupiedEdge R S V) :=
  Finset.univ.image unmarkedFaceTopLabel

@[simp] theorem card_unmarkedFaceTopLabels (R S : ℕ) (V : Finset LatticePoint) :
    (unmarkedFaceTopLabels R S V).card = (unmarkedFaces R S V).card := by
  rw [unmarkedFaceTopLabels, Finset.card_image_of_injective]
  · simp
  · exact unmarkedFaceTopLabel_injective R S V

@[simp] theorem mem_unmarkedFaceTopLabels_iff
    {R S : ℕ} {V : Finset LatticePoint} {e : OccupiedEdge R S V} :
    e ∈ unmarkedFaceTopLabels R S V ↔
      ∃ z : UnmarkedFace R S V, unmarkedFaceTopLabel z = e := by
  simp [unmarkedFaceTopLabels]

/-- The occupied grid after deleting the selected top-face labels. -/
def occupiedGridWithoutTopLabels (R S : ℕ) (V : Finset LatticePoint) :
    LabeledMultigraph (OccupiedVertex R S V)
      {e : OccupiedEdge R S V // e ∉ unmarkedFaceTopLabels R S V} where
  ends e := (occupiedGridMultigraph R S V).ends e.1

private theorem reduced_adj_of_unselected
    {R S : ℕ} {V : Finset LatticePoint}
    {p q : OccupiedVertex R S V} {e : OccupiedEdge R S V}
    (he : e ∉ unmarkedFaceTopLabels R S V)
    (hne : p ≠ q)
    (hlink : (occupiedGridMultigraph R S V).IsLink e p q) :
    (occupiedGridWithoutTopLabels R S V).toSimpleGraph.Adj p q := by
  exact ⟨hne, ⟨e, he⟩, hlink⟩

private theorem vertical_not_mem_unmarkedFaceTopLabels
    {R S : ℕ} {V : Finset LatticePoint}
    (e : ↑(verticalOccupiedEdges R S V)) :
    (Sum.inr e : OccupiedEdge R S V) ∉ unmarkedFaceTopLabels R S V := by
  intro he
  rw [mem_unmarkedFaceTopLabels_iff] at he
  rcases he with ⟨z, hz⟩
  exact Sum.inl_ne_inr hz

private theorem reduced_horizontal_reachable
    {R S : ℕ} {V : Finset LatticePoint}
    {x y : ℕ}
    (hl : (x, y) ∈ occupiedVertices R S V)
    (hr : (x + 1, y) ∈ occupiedVertices R S V) :
    (occupiedGridWithoutTopLabels R S V).toSimpleGraph.Reachable
      ⟨(x, y), hl⟩ ⟨(x + 1, y), hr⟩ := by
  induction y using Nat.strong_induction_on with
  | h y ih =>
      have hlData := Finset.mem_sdiff.mp hl
      have hrData := Finset.mem_sdiff.mp hr
      have hxR : x < R := by
        have := (mem_grid.mp hrData.1).1
        omega
      let a : Σ _row : ℕ, ℕ := ⟨y, x⟩
      have ha : a ∈ horizontalOccupiedEdges R S V := by
        simp only [horizontalOccupiedEdges, Finset.mem_sigma]
        refine ⟨Windows.mem_line.mpr (mem_grid.mp hlData.1).2, ?_⟩
        simp only [occupiedLineEdgeStarts, Finset.mem_filter, Finset.mem_range]
        dsimp [a]
        refine ⟨hxR, ?_, ?_⟩
        · intro hxRow
          exact hlData.2 (mem_row.mp hxRow).2
        · intro hxRow
          exact hrData.2 (mem_row.mp hxRow).2
      let e : OccupiedEdge R S V := Sum.inl ⟨a, ha⟩
      have hlink : (occupiedGridMultigraph R S V).IsLink e
          ⟨(x, y), hl⟩ ⟨(x + 1, y), hr⟩ := by
        change (occupiedGridMultigraph R S V).ends e =
          s((⟨(x, y), hl⟩ : OccupiedVertex R S V),
            (⟨(x + 1, y), hr⟩ : OccupiedVertex R S V))
        apply Sym2.eq_iff.mpr
        left
        exact ⟨by apply Subtype.ext; rfl, by apply Subtype.ext; rfl⟩
      by_cases he : e ∈ unmarkedFaceTopLabels R S V
      · rw [mem_unmarkedFaceTopLabels_iff] at he
        rcases he with ⟨z, hz⟩
        have hsigma :
            (unmarkedFaceTopLabel z : OccupiedEdge R S V) = e := hz
        have hsigma' := Sum.inl.inj hsigma
        have hzX : z.1.1 = x := congrArg (fun f => f.1.2) hsigma'
        have hzTop : z.1.2 + 1 = y := congrArg (fun f => f.1.1) hsigma'
        have hyPos : 0 < y := by omega
        have hzY : z.1.2 = y - 1 := by omega
        have hzVal : z.1 = (x, y - 1) := Prod.ext hzX hzY
        have hface : (x, y - 1) ∈ unmarkedFaces R S V := hzVal ▸ z.2
        have hbl : (x, y - 1) ∈ occupiedVertices R S V := by
          apply Finset.mem_sdiff.mpr
          have hzBounds := mem_faceIndices.mp (mem_unmarkedFaces.mp hface).1
          refine ⟨mem_grid.mpr ⟨by omega, by omega⟩, ?_⟩
          exact corner_not_mem_of_unmarked hface
            (mem_faceCorners.mpr ⟨le_rfl, by omega, le_rfl, by omega⟩)
        have hbr : (x + 1, y - 1) ∈ occupiedVertices R S V := by
          apply Finset.mem_sdiff.mpr
          have hzBounds := mem_faceIndices.mp (mem_unmarkedFaces.mp hface).1
          refine ⟨mem_grid.mpr ⟨by omega, by omega⟩, ?_⟩
          exact corner_not_mem_of_unmarked hface
            (mem_faceCorners.mpr ⟨by omega, le_rfl, le_rfl, by omega⟩)
        let avl : Σ _col : ℕ, ℕ := ⟨x, y - 1⟩
        have havl : avl ∈ verticalOccupiedEdges R S V := by
          simp only [verticalOccupiedEdges, Finset.mem_sigma]
          refine ⟨Windows.mem_line.mpr (mem_grid.mp (Finset.mem_sdiff.mp hbl).1).1, ?_⟩
          simp only [occupiedLineEdgeStarts, Finset.mem_filter, Finset.mem_range]
          dsimp [avl]
          refine ⟨by have := (mem_grid.mp hlData.1).2; omega, ?_, ?_⟩
          · intro hcol
            exact (Finset.mem_sdiff.mp hbl).2 (mem_column.mp hcol).2
          · intro hcol
            have htop : (x, y) ∈ V := by
              have := (mem_column.mp hcol).2
              simpa [Nat.sub_add_cancel (by omega : 1 ≤ y)] using this
            exact hlData.2 htop
        let avr : Σ _col : ℕ, ℕ := ⟨x + 1, y - 1⟩
        have havr : avr ∈ verticalOccupiedEdges R S V := by
          simp only [verticalOccupiedEdges, Finset.mem_sigma]
          refine ⟨Windows.mem_line.mpr (mem_grid.mp (Finset.mem_sdiff.mp hbr).1).1, ?_⟩
          simp only [occupiedLineEdgeStarts, Finset.mem_filter, Finset.mem_range]
          dsimp [avr]
          refine ⟨by have := (mem_grid.mp hrData.1).2; omega, ?_, ?_⟩
          · intro hcol
            exact (Finset.mem_sdiff.mp hbr).2 (mem_column.mp hcol).2
          · intro hcol
            have htop : (x + 1, y) ∈ V := by
              have := (mem_column.mp hcol).2
              simpa [Nat.sub_add_cancel (by omega : 1 ≤ y)] using this
            exact hrData.2 htop
        let evl : OccupiedEdge R S V := Sum.inr ⟨avl, havl⟩
        let evr : OccupiedEdge R S V := Sum.inr ⟨avr, havr⟩
        have hleftLink : (occupiedGridMultigraph R S V).IsLink evl
            ⟨(x, y - 1), hbl⟩ ⟨(x, y), hl⟩ := by
          change (occupiedGridMultigraph R S V).ends evl =
            s((⟨(x, y - 1), hbl⟩ : OccupiedVertex R S V),
              (⟨(x, y), hl⟩ : OccupiedVertex R S V))
          apply Sym2.eq_iff.mpr
          left
          exact ⟨by apply Subtype.ext; rfl, by
            apply Subtype.ext
            change (x, (y - 1) + 1) = (x, y)
            exact Prod.ext rfl (by omega)⟩
        have hrightLink : (occupiedGridMultigraph R S V).IsLink evr
            ⟨(x + 1, y - 1), hbr⟩ ⟨(x + 1, y), hr⟩ := by
          change (occupiedGridMultigraph R S V).ends evr =
            s((⟨(x + 1, y - 1), hbr⟩ : OccupiedVertex R S V),
              (⟨(x + 1, y), hr⟩ : OccupiedVertex R S V))
          apply Sym2.eq_iff.mpr
          left
          exact ⟨by apply Subtype.ext; rfl, by
            apply Subtype.ext
            change (x + 1, (y - 1) + 1) = (x + 1, y)
            exact Prod.ext rfl (by omega)⟩
        have hleft : (occupiedGridWithoutTopLabels R S V).toSimpleGraph.Adj
            ⟨(x, y - 1), hbl⟩ ⟨(x, y), hl⟩ :=
          reduced_adj_of_unselected
            (vertical_not_mem_unmarkedFaceTopLabels ⟨avl, havl⟩)
            (by intro hEq
                have hEq' := congrArg (fun t : OccupiedVertex R S V => t.1.2) hEq
                change y - 1 = y at hEq'
                omega)
            hleftLink
        have hright : (occupiedGridWithoutTopLabels R S V).toSimpleGraph.Adj
            ⟨(x + 1, y - 1), hbr⟩ ⟨(x + 1, y), hr⟩ :=
          reduced_adj_of_unselected
            (vertical_not_mem_unmarkedFaceTopLabels ⟨avr, havr⟩)
            (by intro hEq
                have hEq' := congrArg (fun t : OccupiedVertex R S V => t.1.2) hEq
                change y - 1 = y at hEq'
                omega)
            hrightLink
        have hbottom := ih (y - 1) (by omega) hbl hbr
        exact hleft.symm.reachable.trans (hbottom.trans hright.reachable)
      · exact (reduced_adj_of_unselected he
          (by intro hEq
              have hEq' := congrArg (fun t : OccupiedVertex R S V => t.1.1) hEq
              change x = x + 1 at hEq'
              omega)
          hlink).reachable

private theorem reduced_reachable_of_original_adj
    {R S : ℕ} {V : Finset LatticePoint}
    {p q : OccupiedVertex R S V}
    (hpq : (occupiedGridMultigraph R S V).toSimpleGraph.Adj p q) :
    (occupiedGridWithoutTopLabels R S V).toSimpleGraph.Reachable p q := by
  rcases hpq with ⟨hne, e, hlink⟩
  cases e with
  | inr e =>
      exact (reduced_adj_of_unselected
        (vertical_not_mem_unmarkedFaceTopLabels e) hne hlink).reachable
  | inl e =>
      let x := e.1.2
      let y := e.1.1
      have heData := Finset.mem_sigma.mp e.2
      have hxData := Finset.mem_filter.mp heData.2
      have hxlt : x < R := Finset.mem_range.mp hxData.1
      have hyS : y ≤ S := Windows.mem_line.mp heData.1
      have hl : (x, y) ∈ occupiedVertices R S V := by
        apply Finset.mem_sdiff.mpr
        refine ⟨mem_grid.mpr ⟨by omega, hyS⟩, ?_⟩
        intro hV
        exact hxData.2.1 (mem_row.mpr ⟨by omega, hV⟩)
      have hr : (x + 1, y) ∈ occupiedVertices R S V := by
        apply Finset.mem_sdiff.mpr
        refine ⟨mem_grid.mpr ⟨by omega, hyS⟩, ?_⟩
        intro hV
        exact hxData.2.2 (mem_row.mpr ⟨by omega, hV⟩)
      have hreach := reduced_horizontal_reachable hl hr
      have hval := congrArg
        (Sym2.map (fun z : OccupiedVertex R S V => z.1)) hlink
      change s((x, y), (x + 1, y)) = s(p.1, q.1) at hval
      rcases Sym2.eq_iff.mp hval with h | h
      · have hp : p = (⟨(x, y), hl⟩ : OccupiedVertex R S V) :=
          Subtype.ext h.1.symm
        have hq : q = (⟨(x + 1, y), hr⟩ : OccupiedVertex R S V) :=
          Subtype.ext h.2.symm
        simpa [hp, hq] using hreach
      · have hq : q = (⟨(x, y), hl⟩ : OccupiedVertex R S V) :=
          Subtype.ext h.1.symm
        have hp : p = (⟨(x + 1, y), hr⟩ : OccupiedVertex R S V) :=
          Subtype.ext h.2.symm
        simpa [hp, hq] using hreach.symm

/-- Deleting one top edge per unmarked face preserves connectivity. -/
theorem occupiedGridWithoutTopLabels_connected
    {R S : ℕ} {V : Finset LatticePoint}
    (hconn : (occupiedGridMultigraph R S V).Connected) :
    (occupiedGridWithoutTopLabels R S V).Connected := by
  letI : Nonempty (OccupiedVertex R S V) := hconn.nonempty
  refine { preconnected := ?_ }
  intro p q
  have hpq := hconn.preconnected p q
  rw [SimpleGraph.reachable_iff_reflTransGen] at hpq ⊢
  exact hpq.lift' id fun u v huv =>
    (SimpleGraph.reachable_iff_reflTransGen _ _).mp
      (reduced_reachable_of_original_adj huv)

/-- General grid-cycle inequality: in a connected occupied grid, distinct
unmarked unit faces contribute at least that many edges beyond a spanning
tree.  Equivalently, the cubical Euler characteristic is at most one. -/
theorem occupiedVertices_add_unmarkedFaces_le_edges_add_one
    {R S : ℕ} {V : Finset LatticePoint}
    (hconn : (occupiedGridMultigraph R S V).Connected) :
    (occupiedVertices R S V).card + (unmarkedFaces R S V).card ≤
      (horizontalOccupiedEdges R S V).card +
        (verticalOccupiedEdges R S V).card + 1 := by
  classical
  have hred := occupiedGridWithoutTopLabels_connected hconn
  let tree := Classical.choose
    (Multigraph.LabeledMultigraph.exists_isSpanningTree
      (occupiedGridWithoutTopLabels R S V) hred)
  have htree := Classical.choose_spec
    (Multigraph.LabeledMultigraph.exists_isSpanningTree
      (occupiedGridWithoutTopLabels R S V) hred)
  have htreeCard : tree.card + 1 = (occupiedVertices R S V).card := by
    simpa [OccupiedVertex] using htree.card_edges_add_one
  have htreeLe : tree.card ≤
      Fintype.card {e : OccupiedEdge R S V //
        e ∉ unmarkedFaceTopLabels R S V} := by
    simpa using Finset.card_le_univ tree
  have hcompl : Fintype.card {e : OccupiedEdge R S V //
        e ∉ unmarkedFaceTopLabels R S V} =
      Fintype.card (OccupiedEdge R S V) -
        (unmarkedFaces R S V).card := by
    have h := Fintype.card_subtype_compl
      (fun e : OccupiedEdge R S V =>
        e ∈ unmarkedFaceTopLabels R S V)
    rw [Fintype.card_coe, card_unmarkedFaceTopLabels] at h
    exact h
  have hedgeCard : Fintype.card (OccupiedEdge R S V) =
      (horizontalOccupiedEdges R S V).card +
        (verticalOccupiedEdges R S V).card := by
    simp [OccupiedEdge]
  have hfacesLe : (unmarkedFaces R S V).card ≤
      Fintype.card (OccupiedEdge R S V) := by
    rw [← card_unmarkedFaceTopLabels]
    simpa using Finset.card_le_univ (unmarkedFaceTopLabels R S V)
  rw [hcompl] at htreeLe
  omega

private theorem sum_card_columns_euler
    (R S : ℕ) (V : Finset LatticePoint) (hV : V ⊆ grid R S) :
    (∑ x ∈ Windows.line R, (column S V x).card) = V.card := by
  classical
  let C : Finset (Σ _x : ℕ, ℕ) :=
    (Windows.line R).sigma fun x => column S V x
  have hcard : C.card = V.card := by
    symm
    apply Finset.card_bij (fun z _ => ⟨z.1, z.2⟩)
    · intro z hz
      have hgrid := mem_grid.mp (hV hz)
      simp only [C, Finset.mem_sigma]
      exact ⟨Windows.mem_line.mpr hgrid.1,
        mem_column.mpr ⟨hgrid.2, hz⟩⟩
    · intro z₁ hz₁ z₂ hz₂ h
      have hx : z₁.1 = z₂.1 := congrArg Sigma.fst h
      have hy : z₁.2 = z₂.2 := congrArg (fun z => z.2) h
      exact Prod.ext hx hy
    · rintro ⟨x, y⟩ h
      simp only [C, Finset.mem_sigma] at h
      exact ⟨(x, y), (mem_column.mp h.2).2, rfl⟩
  simpa [C] using hcard

private theorem card_horizontalOccupiedEdges_euler
    {R S : ℕ} {V : Finset LatticePoint}
    (hV : V ⊆ grid R S)
    (hrows : ∀ y ≤ S, row R V y ≠ Windows.line R) :
    (horizontalOccupiedEdges R S V).card + V.card +
        horizontalInternalRunCount R S V = R * (S + 1) := by
  have heach : ∀ y ∈ Windows.line S,
      (occupiedLineEdgeStarts R (row R V y)).card + (row R V y).card +
          (internalRunStarts R (row R V y)).card = R := by
    intro y hy
    exact occupiedLineEdges_add_vacancies_add_internalRuns R (row R V y)
      (row_subset_line R V y) (hrows y (Windows.mem_line.mp hy))
  have hsum := Finset.sum_congr rfl heach
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_card_rows R S V hV] at hsum
  simpa [horizontalOccupiedEdges, horizontalInternalRunCount, Windows.line,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum

private theorem card_verticalOccupiedEdges_euler
    {R S : ℕ} {V : Finset LatticePoint}
    (hV : V ⊆ grid R S)
    (hcols : ∀ x ≤ R, column S V x ≠ Windows.line S) :
    (verticalOccupiedEdges R S V).card + V.card +
        verticalInternalRunCount R S V = (R + 1) * S := by
  have heach : ∀ x ∈ Windows.line R,
      (occupiedLineEdgeStarts S (column S V x)).card + (column S V x).card +
          (internalRunStarts S (column S V x)).card = S := by
    intro x hx
    exact occupiedLineEdges_add_vacancies_add_internalRuns S (column S V x)
      (column_subset_line S V x) (hcols x (Windows.mem_line.mp hx))
  have hsum := Finset.sum_congr rfl heach
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_card_columns_euler R S V hV] at hsum
  simpa [verticalOccupiedEdges, verticalInternalRunCount, Windows.line,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hsum

private theorem card_occupiedVertices_euler
    {R S : ℕ} {V : Finset LatticePoint} (hV : V ⊆ grid R S) :
    (occupiedVertices R S V).card + V.card = (R + 1) * (S + 1) := by
  rw [occupiedVertices, Finset.card_sdiff_add_card_eq_card hV]
  simp [grid, Windows.line]

/-- The sliding-window inequality is the reverse Euler inequality.  This
statement includes the degenerate one-row/one-column cases. -/
theorem edges_add_one_le_occupiedVertices_add_unmarkedFaces
    {R S : ℕ} {V : Finset LatticePoint}
    (hV : V ⊆ grid R S)
    (hrows : ∀ y ≤ S, row R V y ≠ Windows.line R)
    (hcols : ∀ x ≤ R, column S V x ≠ Windows.line S)
    (hinj : SlidingWindowInjection R S 1 V) :
    (horizontalOccupiedEdges R S V).card +
        (verticalOccupiedEdges R S V).card + 1 ≤
      (occupiedVertices R S V).card + (unmarkedFaces R S V).card := by
  have hh := card_horizontalOccupiedEdges_euler hV hrows
  have hv := card_verticalOccupiedEdges_euler hV hcols
  have hvertices := card_occupiedVertices_euler hV
  have hfaces := card_markedFaces_add_card_unmarkedFaces R S V
  have hmarked : (markedFaces R S V).card ≤
      V.card + horizontalInternalRunCount R S V +
        verticalInternalRunCount R S V := by
    by_cases hR : 1 ≤ R
    · by_cases hS : 1 ≤ S
      · exact card_markedFaces_le R S V hV hR hS hinj
      · have hS0 : S = 0 := by omega
        subst S
        have hm : (markedFaces R 0 V).card = 0 := by
          omega
        omega
    · have hR0 : R = 0 := by omega
      subst R
      have hm : (markedFaces 0 S V).card = 0 := by
        omega
      omega
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at hh hv hvertices hfaces
  omega

private theorem row_ne_line_of_subset_euler
    {R : ℕ} {V W : Finset LatticePoint} (hVW : V ⊆ W) {y : ℕ}
    (hW : row R W y ≠ Windows.line R) : row R V y ≠ Windows.line R := by
  intro hV
  apply hW
  apply Finset.Subset.antisymm (row_subset_line R W y)
  intro x hx
  have hxV : x ∈ row R V y := by simpa [hV] using hx
  have hxData := mem_row.mp hxV
  exact mem_row.mpr ⟨hxData.1, hVW hxData.2⟩

private theorem column_ne_line_of_subset_euler
    {S : ℕ} {V W : Finset LatticePoint} (hVW : V ⊆ W) {x : ℕ}
    (hW : column S W x ≠ Windows.line S) :
    column S V x ≠ Windows.line S := by
  intro hV
  apply hW
  apply Finset.Subset.antisymm (column_subset_line S W x)
  intro y hy
  have hyV : y ∈ column S V x := by simpa [hV] using hy
  have hyData := mem_column.mp hyV
  exact mem_column.mpr ⟨hyData.1, hVW hyData.2⟩

/-- The finite planar Euler identity for the boundary-attached encoded
vacancies is fully proved.  The two inequalities are respectively the
top-edge deletion argument and the rooted sliding-window injection. -/
theorem encodedBoundaryEulerIdentity_of_connected
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    EncodedBoundaryEulerIdentity R S A := by
  let W := encodedVacancies R S A
  let B := boundaryVacancies R S W
  have hWGrid : W ⊆ grid R S := encodedVacancies_subset_grid R S A
  have hBGrid : B ⊆ grid R S := fun _ hz =>
    hWGrid (boundaryVacancies_subset R S W hz)
  have hrows : ∀ y ≤ S, row R B y ≠ Windows.line R := by
    intro y hy
    exact row_ne_line_of_subset_euler (boundaryVacancies_subset R S W)
      (encodedVacancies_row_ne_line hHull hconn hy)
  have hcols : ∀ x ≤ R, column S B x ≠ Windows.line S := by
    intro x hx
    exact column_ne_line_of_subset_euler (boundaryVacancies_subset R S W)
      (encodedVacancies_column_ne_line hHull hconn hx)
  have hinj : SlidingWindowInjection R S 1 B := by
    simpa [W, B] using
      (slidingWindowInjection_encodedBoundaryVacancies R S 1 A)
  have hoccupied : (occupiedGridMultigraph R S B).Connected := by
    simpa [W, B] using
      (occupiedGrid_encodedBoundaryVacancies_connected hHull hconn)
  change (occupiedVertices R S B).card + (unmarkedFaces R S B).card =
    (horizontalOccupiedEdges R S B).card +
      (verticalOccupiedEdges R S B).card + 1
  apply Nat.le_antisymm
  · exact occupiedVertices_add_unmarkedFaces_le_edges_add_one hoccupied
  · exact edges_add_one_le_occupiedVertices_add_unmarkedFaces
      hBGrid hrows hcols hinj

/-- Hence the formerly hypothesized finite cellulation certificate is now
constructed without any planar or Euler assumption. -/
noncomputable def gridCellulationCertificate_encodedBoundaryVacancies
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    GridCellulationCertificate R S
      (boundaryVacancies R S (encodedVacancies R S A)) :=
  gridCellulationCertificate_encodedBoundaryVacancies_of_euler hHull hconn
    (encodedBoundaryEulerIdentity_of_connected hHull hconn)

/-- Marked-face count in the normalized connected setting. -/
theorem card_markedFaces_encodedBoundaryVacancies
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected) :
    (markedFaces R S
      (boundaryVacancies R S (encodedVacancies R S A))).card =
      (boundaryVacancies R S (encodedVacancies R S A)).card +
        horizontalInternalRunCount R S
          (boundaryVacancies R S (encodedVacancies R S A)) +
        verticalInternalRunCount R S
          (boundaryVacancies R S (encodedVacancies R S A)) :=
  card_markedFaces_encodedBoundaryVacancies_of_cellulation hHull hconn
    (gridCellulationCertificate_encodedBoundaryVacancies hHull hconn)

end

end Boundary
end SquareMaximality
