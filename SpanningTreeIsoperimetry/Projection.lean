import SpanningTreeIsoperimetry.Grid
import SpanningTreeIsoperimetry.HullArithmetic
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# The edge projection bound

This module proves the inequality in manuscript `lem:projection-bound` for the
actual edge set of `domainGraph S`. Its proof counts the eastward and northward
edges by an explicit bijection, then finds one terminal point in every nonempty
coordinate fiber. The equality characterization in terms of convex rows and
columns and the minimal-hull side sum is not asserted by this module.
-/

namespace SpanningTreeIsoperimetry

def east (v : Vertex) : Vertex := (v.1 + 1, v.2)
def north (v : Vertex) : Vertex := (v.1, v.2 + 1)

def horizontalSources (S : Domain) : Domain := S.filter (fun v => east v ∈ S)
def verticalSources (S : Domain) : Domain := S.filter (fun v => north v ∈ S)

/-- Every nonempty fiber has a point with no forward neighbor, found by
maximizing a strictly increasing integer coordinate on that finite fiber. -/
theorem forward_count_add_projection_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → ℤ) (g : α → β) (step : α → α)
    (hstep : ∀ v, f (step v) = f v + 1) (hfixed : ∀ v, g (step v) = g v) :
    (S.filter (fun v => step v ∈ S)).card + (S.image g).card ≤ S.card := by
  let ends := S.filter (fun v => step v ∉ S)
  have hcover : S.image g ⊆ ends.image g := by
    intro b hb
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    let row := S.filter (fun w => g w = g v)
    have hrow : row.Nonempty := ⟨v, by simp [row, hv]⟩
    obtain ⟨w, hw, hmax⟩ := Finset.exists_max_image row f hrow
    have hwS : w ∈ S := (Finset.mem_filter.mp hw).1
    have hwg : g w = g v := (Finset.mem_filter.mp hw).2
    have hwend : step w ∉ S := by
      intro hnext
      have hnextrow : step w ∈ row := by simp [row, hnext, hfixed, hwg]
      have hle := hmax (step w) hnextrow
      rw [hstep] at hle
      omega
    exact Finset.mem_image.mpr ⟨w, by simp [ends, hwS, hwend], hwg⟩
  have hcount := (Finset.card_le_card hcover).trans (Finset.card_image_le)
  have hpartition := Finset.card_filter_add_card_filter_not (s := S) (fun v => step v ∈ S)
  change (S.filter (fun v => step v ∈ S)).card + ends.card = S.card at hpartition
  omega

theorem horizontal_count_add_rows_le (S : Domain) :
    (horizontalSources S).card + (S.image Prod.snd).card ≤ S.card :=
  forward_count_add_projection_le S Prod.fst Prod.snd east (fun _ => rfl) (fun _ => rfl)

theorem vertical_count_add_columns_le (S : Domain) :
    (verticalSources S).card + (S.image Prod.fst).card ≤ S.card :=
  forward_count_add_projection_le S Prod.snd Prod.fst north (fun _ => rfl) (fun _ => rfl)

/-- Oriented horizontal and vertical sources map to actual unordered edges
of the induced graph, not to a surrogate edge-count definition. -/
def forwardEdge (S : Domain) :
    (horizontalSources S) ⊕ (verticalSources S) → (domainGraph S).edgeSet
  | .inl v =>
    ⟨s(⟨v.val, (Finset.mem_filter.mp v.property).1⟩,
       ⟨east v.val, (Finset.mem_filter.mp v.property).2⟩), by
      simp [SimpleGraph.mem_edgeSet, domainGraph, lattice, east]⟩
  | .inr v =>
    ⟨s(⟨v.val, (Finset.mem_filter.mp v.property).1⟩,
       ⟨north v.val, (Finset.mem_filter.mp v.property).2⟩), by
      simp [SimpleGraph.mem_edgeSet, domainGraph, lattice, north]⟩

theorem forwardEdge_surjective (S : Domain) : Function.Surjective (forwardEdge S) := by
  intro edge
  obtain ⟨e, he⟩ := edge
  induction e using Sym2.inductionOn with
  | _ u v =>
    change lattice.Adj u.val v.val at he
    rcases he with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · have hdir : u.val.2 + 1 = v.val.2 ∨ v.val.2 + 1 = u.val.2 := by
        have hsign := eq_or_eq_neg_of_abs_eq hy
        omega
      rcases hdir with hdir | hdir
      · have hnext : north u.val = v.val := Prod.ext hx hdir
        let w : verticalSources S := ⟨u.val, by
          simp only [verticalSources, Finset.mem_filter]
          exact ⟨u.property, hnext ▸ v.property⟩⟩
        refine ⟨Sum.inr w, ?_⟩
        apply Subtype.ext
        apply Sym2.eq_iff.mpr
        left
        constructor
        · rfl
        · exact Subtype.ext hnext
      · have hnext : north v.val = u.val := Prod.ext hx.symm hdir
        let w : verticalSources S := ⟨v.val, by
          simp only [verticalSources, Finset.mem_filter]
          exact ⟨v.property, hnext ▸ u.property⟩⟩
        refine ⟨Sum.inr w, ?_⟩
        apply Subtype.ext
        apply Sym2.eq_iff.mpr
        right
        constructor
        · rfl
        · exact Subtype.ext hnext
    · have hdir : u.val.1 + 1 = v.val.1 ∨ v.val.1 + 1 = u.val.1 := by
        have hsign := eq_or_eq_neg_of_abs_eq hx
        omega
      rcases hdir with hdir | hdir
      · have hnext : east u.val = v.val := Prod.ext hdir hy
        let w : horizontalSources S := ⟨u.val, by
          simp only [horizontalSources, Finset.mem_filter]
          exact ⟨u.property, hnext ▸ v.property⟩⟩
        refine ⟨Sum.inl w, ?_⟩
        apply Subtype.ext
        apply Sym2.eq_iff.mpr
        left
        constructor
        · rfl
        · exact Subtype.ext hnext
      · have hnext : east v.val = u.val := Prod.ext hdir hy.symm
        let w : horizontalSources S := ⟨v.val, by
          simp only [horizontalSources, Finset.mem_filter]
          exact ⟨v.property, hnext ▸ u.property⟩⟩
        refine ⟨Sum.inl w, ?_⟩
        apply Subtype.ext
        apply Sym2.eq_iff.mpr
        right
        constructor
        · rfl
        · exact Subtype.ext hnext

theorem forwardEdge_injective (S : Domain) : Function.Injective (forwardEdge S) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      rcases Sym2.eq_iff.mp (congrArg Subtype.val h) with h | h
      · apply congrArg Sum.inl
        exact Subtype.ext (congrArg (fun v : (S : Set Vertex) => v.val) h.1)
      · have h₁ := congrArg (fun v : (S : Set Vertex) => v.val.1) h.1
        have h₂ := congrArg (fun v : (S : Set Vertex) => v.val.1) h.2
        simp only [east] at h₁ h₂
        omega
    | inr b =>
      rcases Sym2.eq_iff.mp (congrArg Subtype.val h) with h | h
      all_goals
        have h₁ := congrArg (fun v : (S : Set Vertex) => v.val.1) h.1
        have h₂ := congrArg (fun v : (S : Set Vertex) => v.val.1) h.2
        simp only [east, north] at h₁ h₂
        omega
  | inr a =>
    cases b with
    | inl b =>
      rcases Sym2.eq_iff.mp (congrArg Subtype.val h) with h | h
      all_goals
        have h₁ := congrArg (fun v : (S : Set Vertex) => v.val.1) h.1
        have h₂ := congrArg (fun v : (S : Set Vertex) => v.val.1) h.2
        simp only [east, north] at h₁ h₂
        omega
    | inr b =>
      rcases Sym2.eq_iff.mp (congrArg Subtype.val h) with h | h
      · apply congrArg Sum.inr
        exact Subtype.ext (congrArg (fun v : (S : Set Vertex) => v.val) h.1)
      · have h₁ := congrArg (fun v : (S : Set Vertex) => v.val.2) h.1
        have h₂ := congrArg (fun v : (S : Set Vertex) => v.val.2) h.2
        simp only [north] at h₁ h₂
        omega

/-- Exact equality between actual unordered edges and the two directional
source counts. -/
theorem edgeCount_eq_forward_count (S : Domain) :
    Nat.card (domainGraph S).edgeSet =
      (horizontalSources S).card + (verticalSources S).card := by
  have h := Nat.card_eq_of_bijective (forwardEdge S)
    ⟨forwardEdge_injective S, forwardEdge_surjective S⟩
  simpa only [Nat.card_sum, Nat.card_eq_finsetCard] using h.symm

theorem edgeCount_le_forward_count (S : Domain) :
    Nat.card (domainGraph S).edgeSet ≤
      (horizontalSources S).card + (verticalSources S).card := by
  have h := Nat.card_le_card_of_surjective (forwardEdge S) (forwardEdge_surjective S)
  simpa only [Nat.card_sum, Nat.card_eq_finsetCard] using h

/-- The projection bound in its stronger row-and-column form. -/
theorem edgeCount_add_projections_le (S : Domain) :
    Nat.card (domainGraph S).edgeSet +
      (S.image Prod.fst).card + (S.image Prod.snd).card ≤ 2 * S.card := by
  have hE := edgeCount_le_forward_count S
  have hH := horizontal_count_add_rows_le S
  have hV := vertical_count_add_columns_le S
  omega

theorem card_le_projection_product (S : Domain) :
    S.card ≤ (S.image Prod.fst).card * (S.image Prod.snd).card := by
  have hsub : S ⊆ S.image Prod.fst ×ˢ S.image Prod.snd := by
    intro v hv
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨v, hv, rfl⟩, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
  simpa only [Finset.card_product] using Finset.card_le_card hsub

/-- The edge-isoperimetric upper bound for the actual induced graph of any
finite lattice domain. The equality characterization is a separate theorem. -/
theorem edgeCount_projection_bound (S : Domain) :
    Nat.card (domainGraph S).edgeSet ≤
      2 * S.card - ⌈2 * Real.sqrt (S.card : ℝ)⌉₊ := by
  by_cases hS : S.card = 0
  · have hE := edgeCount_add_projections_le S
    simp only [hS, mul_zero, Nat.cast_zero, Real.sqrt_zero, mul_zero,
      Nat.ceil_zero, Nat.sub_self]
    omega
  · have hside := minimum_side_sum_le
      (ceil_sqrt_is_minimum_side_sum (Nat.pos_of_ne_zero hS))
      (card_le_projection_product S)
    have hE := edgeCount_add_projections_le S
    omega

end SpanningTreeIsoperimetry
