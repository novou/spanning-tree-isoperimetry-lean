module

public import SpanningTreeIsoperimetry.FoundationsBridge
public import SpanningTreeIsoperimetry.StabilityGeometry
public import SquareMaximality.Theorem

@[expose] public section

/-! Closed square-cardinality results transported to the current definitions.
Every dependency of SquareMaximality.Theorem is included under Foundations
and checked by the current pinned toolchain. -/
namespace SpanningTreeIsoperimetry

@[simp] theorem translatedSquare_eq_foundation (n : ℕ) (a : Vertex) :
    translatedSquare n a = SquareMaximality.rectangle a.1 a.2 n n := by
  ext ⟨x,y⟩
  simp [mem_translatedSquare, SquareMaximality.rectangle, and_assoc]

theorem square_maximality {n : ℕ} (hn : 0 < n) (S : Domain) (hcard : S.card = n ^ 2) :
    treeCount S ≤ treeCount (rectangle n n) := by
  rw [treeCount_eq_foundation, rectangle_treeCount_eq_foundation]
  exact SquareMaximality.squareMaximality hn S hcard

theorem square_equality_iff {n : ℕ} (hn : 0 < n) (S : Domain) (hcard : S.card = n ^ 2) :
    treeCount S = treeCount (rectangle n n) ↔ ∃ a : Vertex, S = translatedSquare n a := by
  rw [treeCount_eq_foundation, rectangle_treeCount_eq_foundation,
    SquareMaximality.equality_iff_latticeSquare hn S hcard]
  unfold SquareMaximality.IsLatticeSquare
  constructor
  · rintro ⟨a,b,h⟩
    exact ⟨(a,b), by simpa only [translatedSquare_eq_foundation] using h⟩
  · rintro ⟨a,h⟩
    exact ⟨a.1,a.2, by simpa only [translatedSquare_eq_foundation] using h⟩

theorem square_isMaximizer {n : ℕ} (hn : 0 < n) : IsMaximizer (rectangle n n) := by
  refine ⟨?_, ?_⟩
  · rw [domainGraph_eq_foundation, rectangle_eq_foundation]
    exact SquareMaximality.standardRectangle_connected hn hn
  · intro S hcard _
    apply square_maximality hn S
    simpa only [card_rectangle, pow_two] using hcard

end SpanningTreeIsoperimetry
