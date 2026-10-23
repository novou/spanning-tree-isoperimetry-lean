module

public import SpanningTreeIsoperimetry.FoundationsBridge
public import SpanningTreeIsoperimetry.ProjectionEquality
public import SquareMaximality.Normalization
public import Mathlib.Data.Set.Finite.Lemmas

@[expose] public section

/-! Translation invariance, projection sizes of minimal hulls, and existence
of actual spanning-tree maximizers. -/
namespace SpanningTreeIsoperimetry.MaximizerGeometry

open SquareMaximality
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[simp] theorem translateFinset_card (a b : ℤ) (S : Domain) :
    (translateFinset a b S).card = S.card := by
  simp [translateFinset]

@[simp] theorem treeCount_translateFinset (a b : ℤ) (S : Domain) :
    SpanningTreeIsoperimetry.treeCount (translateFinset a b S) =
      SpanningTreeIsoperimetry.treeCount S := by
  rw [treeCount_eq_foundation, tau_translateFinset, ← treeCount_eq_foundation]

theorem connected_translateFinset_iff (a b : ℤ) (S : Domain) :
    (domainGraph (translateFinset a b S)).Connected ↔ (domainGraph S).Connected := by
  rw [domainGraph_eq_foundation, domainGraph_eq_foundation]
  exact (inducedGridTranslationIso a b S).connected_iff.symm

@[simp] theorem mem_translateFinset_iff (a b : ℤ) (S : Domain) (p : Vertex) :
    p ∈ translateFinset a b S ↔ (p.1 - a, p.2 - b) ∈ S := by
  simpa [pointTranslation] using mem_translateFinset a b S (p.1 - a, p.2 - b)

@[simp] theorem translateFinset_neg_cancel (a b : ℤ) (S : Domain) :
    translateFinset (-a) (-b) (translateFinset a b S) = S := by
  ext p
  simp only [mem_translateFinset_iff]
  simp

theorem isMaximizer_translateFinset {S : Domain} (hS : IsMaximizer S) (a b : ℤ) :
    IsMaximizer (translateFinset a b S) := by
  refine ⟨(connected_translateFinset_iff a b S).mpr hS.1, ?_⟩
  intro T hcard hconn
  have hcard' : (translateFinset (-a) (-b) T).card = S.card := by
    simpa using hcard
  have hconn' := (connected_translateFinset_iff (-a) (-b) T).mpr hconn
  have h := hS.2 (translateFinset (-a) (-b) T) hcard' hconn'
  simpa only [treeCount_translateFinset] using h

theorem isMaximizer_translateFinset_iff (a b : ℤ) (S : Domain) :
    IsMaximizer (translateFinset a b S) ↔ IsMaximizer S := by
  constructor
  · intro h
    have hh := isMaximizer_translateFinset h (-a) (-b)
    simpa only [translateFinset_neg_cancel] using hh
  · exact fun h => isMaximizer_translateFinset h a b

theorem rowConvex_translateFinset {S : Domain} (hS : IsRowConvex S) (a b : ℤ) :
    IsRowConvex (translateFinset a b S) := by
  intro x₁ x x₂ y h₁ h₂ hleft hright
  rw [mem_translateFinset_iff] at h₁ h₂ ⊢
  exact hS (x₁ - a) (x - a) (x₂ - a) (y - b) h₁ h₂ (by omega) (by omega)

theorem columnConvex_translateFinset {S : Domain} (hS : IsColumnConvex S) (a b : ℤ) :
    IsColumnConvex (translateFinset a b S) := by
  intro x y₁ y y₂ h₁ h₂ hleft hright
  rw [mem_translateFinset_iff] at h₁ h₂ ⊢
  exact hS (x - a) (y₁ - b) (y - b) (y₂ - b) h₁ h₂ (by omega) (by omega)

theorem rowConvex_translateFinset_iff (a b : ℤ) (S : Domain) :
    IsRowConvex (translateFinset a b S) ↔ IsRowConvex S := by
  constructor
  · intro h
    have hh := rowConvex_translateFinset h (-a) (-b)
    simpa only [translateFinset_neg_cancel] using hh
  · exact fun h => rowConvex_translateFinset h a b

theorem columnConvex_translateFinset_iff (a b : ℤ) (S : Domain) :
    IsColumnConvex (translateFinset a b S) ↔ IsColumnConvex S := by
  constructor
  · intro h
    have hh := columnConvex_translateFinset h (-a) (-b)
    simpa only [translateFinset_neg_cancel] using hh
  · exact fun h => columnConvex_translateFinset h a b

/-- A connected domain occupies every column between its attained hull sides. -/
theorem xProjection_eq_hull_interval {S : Domain} {a b : ℤ} {r s : ℕ}
    (hconn : (domainGraph S).Connected) (hHull : IsRectHull S a b r s) :
    S.image Prod.fst = Finset.Ico a (a + r) := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    have h := hHull.2.2.1 hp
    simpa [SquareMaximality.rectangle] using (Finset.mem_product.mp h).1
  · intro hx
    have hbounds := Finset.mem_Ico.mp hx
    obtain ⟨p, hp, hpa⟩ := hHull.2.2.2.1
    obtain ⟨q, hq, hqc⟩ := hHull.2.2.2.2.1
    apply connected_xProjection_interval hconn a (Finset.mem_image.mpr ⟨p, hp, hpa⟩)
      (a + r - 1) (Finset.mem_image.mpr ⟨q, hq, hqc⟩) x hbounds.1
    omega

theorem yProjection_eq_hull_interval {S : Domain} {a b : ℤ} {r s : ℕ}
    (hconn : (domainGraph S).Connected) (hHull : IsRectHull S a b r s) :
    S.image Prod.snd = Finset.Ico b (b + s) := by
  ext y
  constructor
  · intro hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    have h := hHull.2.2.1 hp
    simpa [SquareMaximality.rectangle] using (Finset.mem_product.mp h).2
  · intro hy
    have hbounds := Finset.mem_Ico.mp hy
    obtain ⟨p, hp, hpb⟩ := hHull.2.2.2.2.2.1
    obtain ⟨q, hq, hqd⟩ := hHull.2.2.2.2.2.2
    apply connected_yProjection_interval hconn b (Finset.mem_image.mpr ⟨p, hp, hpb⟩)
      (b + s - 1) (Finset.mem_image.mpr ⟨q, hq, hqd⟩) y hbounds.1
    omega

theorem projection_card_of_hull {S : Domain} {a b : ℤ} {r s : ℕ}
    (hconn : (domainGraph S).Connected) (hHull : IsRectHull S a b r s) :
    (S.image Prod.fst).card = r ∧ (S.image Prod.snd).card = s := by
  rw [xProjection_eq_hull_interval hconn hHull, yProjection_eq_hull_interval hconn hHull]
  simp [Int.card_Ico]

/-- Convex rows and columns turn the hull side sum into the exact edge count. -/
theorem edgeCount_eq_of_convex_hull {S : Domain} {a b : ℤ} {r s : ℕ}
    (hconn : (domainGraph S).Connected) (hHull : IsRectHull S a b r s)
    (hrow : IsRowConvex S) (hcol : IsColumnConvex S) :
    Nat.card (domainGraph S).edgeSet = 2 * S.card - (r + s) := by
  have h := (edgeCount_add_projections_eq_iff S).mpr ⟨hrow, hcol⟩
  have hp := projection_card_of_hull hconn hHull
  rw [hp.1, hp.2] at h
  omega

theorem edgeCount_eq_of_minimum_hull {S : Domain} {a b : ℤ} {r s : ℕ}
    (hconn : (domainGraph S).Connected) (hHull : IsRectHull S a b r s)
    (hrow : IsRowConvex S) (hcol : IsColumnConvex S)
    (hsum : r + s = ⌈2 * Real.sqrt (S.card : ℝ)⌉₊) :
    Nat.card (domainGraph S).edgeSet = 2 * S.card - ⌈2 * Real.sqrt (S.card : ℝ)⌉₊ := by
  rw [edgeCount_eq_of_convex_hull hconn hHull hrow hcol, hsum]

/-- A uniform finite bound on attainable tree counts at a fixed cardinality.
No finite enumeration of lattice shapes is needed. -/
theorem treeCount_le_graphCount {S : Domain} {N : ℕ} (hcard : S.card = N) :
    SpanningTreeIsoperimetry.treeCount S ≤ Nat.card (SimpleGraph (Fin N)) := by
  have hc : Fintype.card (S : Set Vertex) = N := by simpa using hcard
  let e : (S : Set Vertex) ≃ Fin N := Fintype.equivFinOfCardEq hc
  calc
    SpanningTreeIsoperimetry.treeCount S ≤ Nat.card (SimpleGraph (S : Set Vertex)) :=
      Nat.card_le_card_of_injective (fun T : SpanningTrees S => T.val) Subtype.val_injective
    _ = Nat.card (SimpleGraph (Fin N)) := Nat.card_congr e.simpleGraph

/-- An actual maximizer exists at every positive cardinality. -/
theorem exists_isMaximizer {N : ℕ} (hN : 0 < N) :
    ∃ S : Domain, S.card = N ∧ IsMaximizer S := by
  let values : Set ℕ := {k | ∃ S : Domain, S.card = N ∧
    (domainGraph S).Connected ∧ SpanningTreeIsoperimetry.treeCount S = k}
  have hbound : values ⊆ Set.Iic (Nat.card (SimpleGraph (Fin N))) := by
    rintro k ⟨S, hcard, _, rfl⟩
    exact treeCount_le_graphCount hcard
  have hfinite : values.Finite := (Set.finite_Iic _).subset hbound
  have hpath : (domainGraph (SpanningTreeIsoperimetry.rectangle 1 N)).Connected := by
    rw [domainGraph_eq_foundation, rectangle_eq_foundation]
    exact standardRectangle_connected (by omega) hN
  have hnonempty : values.Nonempty :=
    ⟨SpanningTreeIsoperimetry.treeCount (SpanningTreeIsoperimetry.rectangle 1 N),
      SpanningTreeIsoperimetry.rectangle 1 N, by simp, hpath, rfl⟩
  obtain ⟨m, hm, hmax⟩ := Set.exists_max_image values id hfinite hnonempty
  obtain ⟨S, hcard, hconn, hcount⟩ := hm
  refine ⟨S, hcard, hconn, ?_⟩
  intro T hT hTconn
  have h := hmax (SpanningTreeIsoperimetry.treeCount T) ⟨T, hT.trans hcard, hTconn, rfl⟩
  change SpanningTreeIsoperimetry.treeCount T ≤ m at h
  rwa [← hcount] at h

end SpanningTreeIsoperimetry.MaximizerGeometry
