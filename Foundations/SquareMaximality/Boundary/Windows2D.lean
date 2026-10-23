module

public import SquareMaximality.Windows
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Dist
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Two-dimensional vacancy windows

This file formalizes the finite counting part of `general.tex`, lines 836--927.
The grid has coordinates `{0, ..., R} × {0, ..., S}`; thus the manuscript's
`r` and `s` are `R + 1` and `S + 1` here.

The manuscript's sliding-window construction is isolated as
`SlidingWindowInjection`: an injection from internal components appearing in
horizontal windows to unmarked vertices of the finite vertical-run graph.  All
cardinality consequences, including the anisotropic-window inequality, are
proved from that single finite statement.
-/

namespace SquareMaximality

namespace Boundary

open Windows

abbrev LatticePoint := ℕ × ℕ

/-- The finite lattice rectangle `{0, ..., R} × {0, ..., S}`. -/
def grid (R S : ℕ) : Finset LatticePoint := line R ×ˢ line S

/-- Vacant horizontal coordinates in row `y`. -/
def row (R : ℕ) (V : Finset LatticePoint) (y : ℕ) : Finset ℕ :=
  (line R).filter fun x => (x, y) ∈ V

/-- Vacant vertical coordinates in column `x`. -/
def column (S : ℕ) (V : Finset LatticePoint) (x : ℕ) : Finset ℕ :=
  (line S).filter fun y => (x, y) ∈ V

@[simp] theorem mem_grid {R S : ℕ} {z : LatticePoint} :
    z ∈ grid R S ↔ z.1 ≤ R ∧ z.2 ≤ S := by
  simp [grid]

@[simp] theorem mem_row {R : ℕ} {V : Finset LatticePoint} {y x : ℕ} :
    x ∈ row R V y ↔ x ≤ R ∧ (x, y) ∈ V := by
  simp [row]

@[simp] theorem mem_column {S : ℕ} {V : Finset LatticePoint} {x y : ℕ} :
    y ∈ column S V x ↔ y ≤ S ∧ (x, y) ∈ V := by
  simp [column]

theorem row_subset_line (R : ℕ) (V : Finset LatticePoint) (y : ℕ) :
    row R V y ⊆ line R := by
  intro x hx
  simpa using (mem_row.mp hx).1

theorem column_subset_line (S : ℕ) (V : Finset LatticePoint) (x : ℕ) :
    column S V x ⊆ line S := by
  intro y hy
  simpa using (mem_column.mp hy).1

/-- The total number `g_x` of horizontally internal vacancy runs. -/
def horizontalInternalRunCount (R S : ℕ) (V : Finset LatticePoint) : ℕ :=
  ∑ y ∈ line S, (internalRunStarts R (row R V y)).card

/-- The total number `g_y` of vertically internal vacancy runs. -/
def verticalInternalRunCount (R S : ℕ) (V : Finset LatticePoint) : ℕ :=
  ∑ x ∈ line R, (internalRunStarts S (column S V x)).card

/-- A closed two-dimensional lattice window with side increments `p` and `q`. -/
def rectangleWindow (x y p q : ℕ) : Finset LatticePoint :=
  window x p ×ˢ window y q

@[simp] theorem mem_rectangleWindow {x y p q : ℕ} {z : LatticePoint} :
    z ∈ rectangleWindow x y p q ↔
      x ≤ z.1 ∧ z.1 ≤ x + p ∧ y ≤ z.2 ∧ z.2 ≤ y + q := by
  simp only [rectangleWindow, Finset.mem_product, mem_window]
  tauto

/-- Horizontal windows, indexed first by their row and then by their start. -/
def horizontalWindowStarts (R S p : ℕ) (V : Finset LatticePoint) :
    Finset (Σ _y : ℕ, ℕ) :=
  (line S).sigma fun y => meetingWindowStarts R p (row R V y)

/-- Rows met by the horizontal window whose left endpoint is `x`. -/
def horizontalSection (R S p : ℕ) (V : Finset LatticePoint) (x : ℕ) : Finset ℕ :=
  (line S).filter fun y => x ∈ meetingWindowStarts R p (row R V y)

@[simp] theorem mem_horizontalSection {R S p : ℕ} {V : Finset LatticePoint}
    {x y : ℕ} :
    y ∈ horizontalSection R S p V x ↔
      y ≤ S ∧ x ∈ meetingWindowStarts R p (row R V y) := by
  simp [horizontalSection]

theorem horizontalSection_subset_line (R S p : ℕ) (V : Finset LatticePoint) (x : ℕ) :
    horizontalSection R S p V x ⊆ line S := by
  intro y hy
  simpa using (mem_horizontalSection.mp hy).1

/-- The same horizontal windows, indexed first by their start and then by row. -/
def horizontalWindowStartsByColumn (R S p : ℕ) (V : Finset LatticePoint) :
    Finset (Σ _x : ℕ, ℕ) :=
  (validWindowStarts R p).sigma fun x => horizontalSection R S p V x

theorem card_horizontalWindowStartsByColumn (R S p : ℕ) (V : Finset LatticePoint) :
    (horizontalWindowStartsByColumn R S p V).card =
      (horizontalWindowStarts R S p V).card := by
  classical
  apply Finset.card_bij (fun z _ => ⟨z.2, z.1⟩)
  · rintro ⟨x, y⟩ h
    simp only [horizontalWindowStartsByColumn, Finset.mem_sigma] at h
    simp only [horizontalWindowStarts, Finset.mem_sigma]
    have hy := mem_horizontalSection.mp h.2
    exact ⟨mem_line.mpr hy.1, hy.2⟩
  · rintro ⟨x₁, y₁⟩ h₁ ⟨x₂, y₂⟩ h₂ h
    have hy : y₁ = y₂ := congrArg Sigma.fst h
    have hx : x₁ = x₂ := congrArg (fun z => z.2) h
    cases hx
    cases hy
    rfl
  · rintro ⟨y, x⟩ h
    simp only [horizontalWindowStarts, Finset.mem_sigma] at h
    refine ⟨⟨x, y⟩, ?_, rfl⟩
    simp only [horizontalWindowStartsByColumn, Finset.mem_sigma]
    exact ⟨mem_validWindowStarts.mpr (mem_meetingWindowStarts.mp h.2).1,
      mem_horizontalSection.mpr ⟨mem_line.mp h.1, h.2⟩⟩

/-- Vacancy points indexed by row; used to identify row mass with `|V|`. -/
private def vacancyByRows (R S : ℕ) (V : Finset LatticePoint) :
    Finset (Σ _y : ℕ, ℕ) :=
  (line S).sigma fun y => row R V y

private theorem card_vacancyByRows (R S : ℕ) (V : Finset LatticePoint)
    (hV : V ⊆ grid R S) :
    (vacancyByRows R S V).card = V.card := by
  classical
  symm
  apply Finset.card_bij (fun z _ => ⟨z.2, z.1⟩)
  · intro z hz
    have hgrid := mem_grid.mp (hV hz)
    simp only [vacancyByRows, Finset.mem_sigma]
    exact ⟨by simpa using hgrid.2, mem_row.mpr ⟨hgrid.1, hz⟩⟩
  · rintro z₁ hz₁ z₂ hz₂ h
    have hy : z₁.2 = z₂.2 := congrArg Sigma.fst h
    have hx : z₁.1 = z₂.1 := congrArg (fun z => z.2) h
    exact Prod.ext hx hy
  · rintro ⟨y, x⟩ h
    simp only [vacancyByRows, Finset.mem_sigma] at h
    exact ⟨(x, y), (mem_row.mp h.2).2, rfl⟩

theorem sum_card_rows (R S : ℕ) (V : Finset LatticePoint) (hV : V ⊆ grid R S) :
    (∑ y ∈ line S, (row R V y).card) = V.card := by
  simpa [vacancyByRows] using card_vacancyByRows R S V hV

/-! ## The finite vertical-run graph -/

/-- Canonical starts of every nonempty interval component, including boundary runs. -/
def runStarts (L : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (line L).filter fun a => a ∈ B ∧ (a = 0 ∨ a - 1 ∉ B)

@[simp] theorem mem_runStarts {L a : ℕ} {B : Finset ℕ} :
    a ∈ runStarts L B ↔ a ≤ L ∧ a ∈ B ∧ (a = 0 ∨ a - 1 ∉ B) := by
  simp [runStarts]

/-- A run is marked exactly when its interval touches row `0` or row `L`. -/
def runMarked (L : ℕ) (B : Finset ℕ) (a : ℕ) : Prop :=
  a = 0 ∨ L ∈ intervalComponent L B a

theorem mem_internalRunStarts_iff_runStart_not_marked {L a : ℕ} {B : Finset ℕ} :
    a ∈ internalRunStarts L B ↔ a ∈ runStarts L B ∧ ¬ runMarked L B a := by
  constructor
  · intro ha
    have hi := mem_internalRunStarts.mp ha
    have hends := internal_component_avoids_endpoints ha
    refine ⟨mem_runStarts.mpr ⟨hi.1, hi.2.2.1, Or.inr hi.2.2.2.1⟩, ?_⟩
    intro hm
    rcases hm with hzero | hL
    · omega
    · exact hends.2 hL
  · rintro ⟨ha, hmark⟩
    have hs := mem_runStarts.mp ha
    have hapos : 0 < a := by
      by_contra h
      apply hmark
      left
      omega
    have hpred : a - 1 ∉ B := by
      rcases hs.2.2 with hzero | hpred
      · omega
      · exact hpred
    refine mem_internalRunStarts.mpr ⟨hs.1, hapos, hs.2.1, hpred, ?_⟩
    intro hright
    apply hmark
    right
    rw [mem_rightBoundaryRun] at hright
    exact mem_intervalComponent.mpr ⟨hright.1, le_rfl, hright.2⟩

/-- Vertices of the full vertical-run graph, represented by `(column, run start)`. -/
def verticalRuns (R S : ℕ) (V : Finset LatticePoint) : Finset (Σ _x : ℕ, ℕ) :=
  (line R).sigma fun x => runStarts S (column S V x)

/-- The unmarked vertices of the full vertical-run graph. -/
noncomputable def unmarkedVerticalRuns (R S : ℕ) (V : Finset LatticePoint) :
    Finset (Σ _x : ℕ, ℕ) := by
  classical
  exact (verticalRuns R S V).filter fun z =>
    ¬ runMarked S (column S V z.1) z.2

/-- Two run vertices are joined when their columns are adjacent and their intervals overlap
or are separated by one lattice unit. -/
def verticalRunRelation (R S : ℕ) (V : Finset LatticePoint)
    (u v : ↑(verticalRuns R S V)) : Prop :=
  Nat.dist u.1.1 v.1.1 = 1 ∧
    ∃ yu ∈ intervalComponent S (column S V u.1.1) u.1.2,
      ∃ yv ∈ intervalComponent S (column S V v.1.1) v.1.2,
        Nat.dist yu yv ≤ 1

/-- The finite full run graph used by the manuscript's sliding-window construction. -/
def fullVerticalRunGraph (R S : ℕ) (V : Finset LatticePoint) :
    SimpleGraph (↑(verticalRuns R S V)) :=
  SimpleGraph.fromRel (verticalRunRelation R S V)

private def internalVerticalRuns (R S : ℕ) (V : Finset LatticePoint) :
    Finset (Σ _x : ℕ, ℕ) :=
  (line R).sigma fun x => internalRunStarts S (column S V x)

theorem unmarkedVerticalRuns_eq_internalVerticalRuns (R S : ℕ) (V : Finset LatticePoint) :
    unmarkedVerticalRuns R S V = internalVerticalRuns R S V := by
  classical
  ext z
  simp only [unmarkedVerticalRuns, Finset.mem_filter, verticalRuns,
    internalVerticalRuns, Finset.mem_sigma]
  rw [mem_internalRunStarts_iff_runStart_not_marked]
  tauto

theorem card_unmarkedVerticalRuns (R S : ℕ) (V : Finset LatticePoint) :
    (unmarkedVerticalRuns R S V).card = verticalInternalRunCount R S V := by
  rw [unmarkedVerticalRuns_eq_internalVerticalRuns]
  simp [internalVerticalRuns, verticalInternalRunCount]

/-! ## The one remaining sliding-window statement -/

/-- Internal row-components appearing in all horizontal windows. -/
def windowInternalComponents (R S p : ℕ) (V : Finset LatticePoint) :
    Finset (Σ _x : ℕ, ℕ) :=
  (validWindowStarts R p).sigma fun x =>
    internalRunStarts S (horizontalSection R S p V x)

/--
The manuscript's equation `window-injection`, stated as its actual finite injection.

The intended map is constructed from rooted spanning trees of `fullVerticalRunGraph`.
Keeping that construction behind this one predicate makes the precise remaining proof
obligation visible without introducing a global axiom.
-/
def SlidingWindowInjection (R S p : ℕ) (V : Finset LatticePoint) : Prop :=
  Nonempty
    (↑(windowInternalComponents R S p V) ↪
      ↑(unmarkedVerticalRuns R S V))

/-- Equation `window-injection`: the injection implies the required component bound. -/
theorem window_injection_inequality (R S p : ℕ) (V : Finset LatticePoint)
    (hinj : SlidingWindowInjection R S p V) :
    (∑ x ∈ validWindowStarts R p,
        (internalRunStarts S (horizontalSection R S p V x)).card) ≤
      verticalInternalRunCount R S V := by
  rcases hinj with ⟨f⟩
  have hcard : Fintype.card (↑(windowInternalComponents R S p V)) ≤
      Fintype.card (↑(unmarkedVerticalRuns R S V)) :=
    Fintype.card_le_of_injective f f.injective
  have hcard' : (windowInternalComponents R S p V).card ≤
      (unmarkedVerticalRuns R S V).card := by
    calc
      _ = Fintype.card (↑(windowInternalComponents R S p V)) := (Fintype.card_coe _).symm
      _ ≤ Fintype.card (↑(unmarkedVerticalRuns R S V)) := hcard
      _ = _ := Fintype.card_coe _
  simpa [windowInternalComponents, card_unmarkedVerticalRuns] using hcard'

/-! ## Horizontal and anisotropic window bounds -/

/-- Equation `horizontal-window`. -/
theorem horizontal_window_inequality (R S p : ℕ) (V : Finset LatticePoint)
    (hV : V ⊆ grid R S) (hp : p ≤ R) :
    (horizontalWindowStarts R S p V).card ≤
      V.card + p * horizontalInternalRunCount R S V := by
  rw [horizontalWindowStarts, Finset.card_sigma]
  have hrow : ∀ y ∈ line S,
      (meetingWindowStarts R p (row R V y)).card ≤
        (row R V y).card + p * (internalRunStarts R (row R V y)).card := by
    intro y hy
    exact one_dimensional_window R p (row R V y) (row_subset_line R V y) hp
  calc
    (∑ y ∈ line S, (meetingWindowStarts R p (row R V y)).card) ≤
        ∑ y ∈ line S,
          ((row R V y).card + p * (internalRunStarts R (row R V y)).card) :=
      Finset.sum_le_sum hrow
    _ = (∑ y ∈ line S, (row R V y).card) +
        p * ∑ y ∈ line S, (internalRunStarts R (row R V y)).card := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = V.card + p * horizontalInternalRunCount R S V := by
      rw [sum_card_rows R S V hV]
      rfl

/--
All two-dimensional windows which meet `V`, indexed by horizontal start and then
vertical start.  The membership theorem below identifies this layered finite
definition with intersection by `rectangleWindow`.
-/
def meetingRectangleWindowStarts (R S p q : ℕ) (V : Finset LatticePoint) :
    Finset (Σ _x : ℕ, ℕ) :=
  (validWindowStarts R p).sigma fun x =>
    meetingWindowStarts S q (horizontalSection R S p V x)

theorem mem_meetingRectangleWindowStarts {R S p q : ℕ} {V : Finset LatticePoint}
    {z : Σ _x : ℕ, ℕ} :
    z ∈ meetingRectangleWindowStarts R S p q V ↔
      z.1 + p ≤ R ∧ z.2 + q ≤ S ∧
        ∃ w ∈ V,
          z.1 ≤ w.1 ∧ w.1 ≤ z.1 + p ∧
          z.2 ≤ w.2 ∧ w.2 ≤ z.2 + q := by
  simp only [meetingRectangleWindowStarts, Finset.mem_sigma, mem_validWindowStarts,
    mem_meetingWindowStarts, mem_horizontalSection]
  constructor
  · rintro ⟨hx, hq, y, hysection, hzy, hyq⟩
    rcases hysection with ⟨hyS, hpmeet⟩
    rcases hpmeet with ⟨hpvalid, x, hxrow, hzx, hxp⟩
    exact ⟨hx, hq, (x, y), (mem_row.mp hxrow).2, hzx, hxp, hzy, hyq⟩
  · rintro ⟨hx, hq, ⟨x, y⟩, hxyV, hzx, hxp, hzy, hyq⟩
    refine ⟨hx, hq, y, ?_, hzy, hyq⟩
    refine ⟨?_, ⟨hx, x, ?_, hzx, hxp⟩⟩
    · omega
    · exact mem_row.mpr ⟨hxp.trans hx, hxyV⟩

theorem meetingRectangleWindowStarts_eq_geometric (R S p q : ℕ)
    (V : Finset LatticePoint) :
    meetingRectangleWindowStarts R S p q V =
      ((validWindowStarts R p).sigma fun _ => validWindowStarts S q).filter
        fun z => (rectangleWindow z.1 z.2 p q ∩ V).Nonempty := by
  ext z
  rw [mem_meetingRectangleWindowStarts]
  simp only [Finset.mem_filter, Finset.mem_sigma, mem_validWindowStarts]
  constructor
  · rintro ⟨hx, hy, w, hwV, hxw, hwxp, hyw, hwyq⟩
    refine ⟨⟨hx, hy⟩, ?_⟩
    exact ⟨w, Finset.mem_inter.mpr
      ⟨mem_rectangleWindow.mpr ⟨hxw, hwxp, hyw, hwyq⟩, hwV⟩⟩
  · rintro ⟨⟨hx, hy⟩, hne⟩
    rcases hne with ⟨w, hw⟩
    have hwi := Finset.mem_inter.mp hw
    have hrect := mem_rectangleWindow.mp hwi.1
    exact ⟨hx, hy, w, hwi.2, hrect.1, hrect.2.1, hrect.2.2.1, hrect.2.2.2⟩

/-- Equation `anisotropic-window`. -/
theorem anisotropic_window_inequality (R S p q : ℕ) (V : Finset LatticePoint)
    (hV : V ⊆ grid R S) (hp : p ≤ R) (hq : q ≤ S)
    (hinj : SlidingWindowInjection R S p V) :
    (meetingRectangleWindowStarts R S p q V).card ≤
      V.card + p * horizontalInternalRunCount R S V +
        q * verticalInternalRunCount R S V := by
  rw [meetingRectangleWindowStarts, Finset.card_sigma]
  have heach : ∀ x ∈ validWindowStarts R p,
      (meetingWindowStarts S q (horizontalSection R S p V x)).card ≤
        (horizontalSection R S p V x).card +
          q * (internalRunStarts S (horizontalSection R S p V x)).card := by
    intro x hx
    exact one_dimensional_window S q (horizontalSection R S p V x)
      (horizontalSection_subset_line R S p V x) hq
  have hsum := Finset.sum_le_sum heach
  have hswap := card_horizontalWindowStartsByColumn R S p V
  have hsections :
      (∑ x ∈ validWindowStarts R p, (horizontalSection R S p V x).card) =
        (horizontalWindowStarts R S p V).card := by
    simpa [horizontalWindowStartsByColumn] using hswap
  have hinj' := window_injection_inequality R S p V hinj
  have hhoriz := horizontal_window_inequality R S p V hV hp
  calc
    (∑ x ∈ validWindowStarts R p,
        (meetingWindowStarts S q (horizontalSection R S p V x)).card) ≤
        ∑ x ∈ validWindowStarts R p,
          ((horizontalSection R S p V x).card +
            q * (internalRunStarts S (horizontalSection R S p V x)).card) := hsum
    _ = (∑ x ∈ validWindowStarts R p, (horizontalSection R S p V x).card) +
        q * ∑ x ∈ validWindowStarts R p,
          (internalRunStarts S (horizontalSection R S p V x)).card := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (horizontalWindowStarts R S p V).card +
        q * verticalInternalRunCount R S V := by
      rw [hsections]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left q hinj') _
    _ ≤ (V.card + p * horizontalInternalRunCount R S V) +
        q * verticalInternalRunCount R S V := Nat.add_le_add_right hhoriz _

end Boundary

end SquareMaximality
