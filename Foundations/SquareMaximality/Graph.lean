import SquareMaximality.Geometry
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

namespace SquareMaximality

/-- The Manhattan distance between two integer lattice points. -/
def manhattanDist (p q : Point) : ℕ :=
  (p.1 - q.1).natAbs + (p.2 - q.2).natAbs

@[simp]
theorem manhattanDist_self (p : Point) : manhattanDist p p = 0 := by
  simp [manhattanDist]

theorem manhattanDist_comm (p q : Point) :
    manhattanDist p q = manhattanDist q p := by
  simp only [manhattanDist]
  congr 1
  · rw [show q.1 - p.1 = -(p.1 - q.1) by omega, Int.natAbs_neg]
  · rw [show q.2 - p.2 = -(p.2 - q.2) by omega, Int.natAbs_neg]

/-- The infinite square-lattice graph on `ℤ × ℤ`.

Two vertices are adjacent exactly when their Manhattan distance is one. -/
def squareLattice : SimpleGraph Point where
  Adj p q := manhattanDist p q = 1
  symm.symm p q h := by
    calc
      manhattanDist q p = manhattanDist p q := manhattanDist_comm q p
      _ = 1 := h
  loopless.irrefl p h := by
    simp only [manhattanDist_self, zero_ne_one] at h

@[simp]
theorem squareLattice_adj (p q : Point) :
    squareLattice.Adj p q ↔ manhattanDist p q = 1 :=
  Iff.rfl

/-- The square-lattice graph induced on a finite set of lattice points.

Its vertex type is the subtype of points belonging to `S`, so all vertices of
`S` (including isolated vertices) are retained. -/
def inducedGrid (S : Finset Point) : SimpleGraph {p : Point // p ∈ S} :=
  squareLattice.comap Subtype.val

@[simp]
theorem inducedGrid_adj {S : Finset Point} (p q : {x : Point // x ∈ S}) :
    (inducedGrid S).Adj p q ↔ squareLattice.Adj p.1 q.1 :=
  Iff.rfl

@[simp]
theorem inducedGrid_adj_iff {S : Finset Point} (p q : {x : Point // x ∈ S}) :
    (inducedGrid S).Adj p q ↔ manhattanDist p.1 q.1 = 1 :=
  Iff.rfl

@[simp]
theorem inducedGrid_vertex_card (S : Finset Point) :
    Fintype.card {p : Point // p ∈ S} = S.card :=
  Fintype.card_coe S

/-- The number of spanning trees of a finite simple graph.

A graph `T : SimpleGraph V` uses the same vertex type as `G`, so the condition
`T ≤ G` makes it a spanning subgraph.  We count precisely those spanning
subgraphs which satisfy Mathlib's `SimpleGraph.IsTree` predicate. -/
noncomputable def treeCount {V : Type*} [Finite V] (G : SimpleGraph V) : ℕ :=
  Nat.card {T : SimpleGraph V // T ≤ G ∧ T.IsTree}

/-- A finite graph has a spanning tree exactly when it is connected. -/
theorem treeCount_pos_iff_connected {V : Type*} [Finite V] (G : SimpleGraph V) :
    0 < treeCount G ↔ G.Connected := by
  rw [treeCount, Finite.card_pos_iff]
  constructor
  · rintro ⟨⟨T, hTG, hT⟩⟩
    exact hT.connected.mono hTG
  · intro hG
    obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
    exact ⟨⟨T, hTG, hT⟩⟩

/-- The number of spanning trees in the square-lattice graph induced by `S`. -/
noncomputable def tau (S : Finset Point) : ℕ :=
  treeCount (inducedGrid S)

theorem tau_pos_iff_connected (S : Finset Point) :
    0 < tau S ↔ (inducedGrid S).Connected :=
  treeCount_pos_iff_connected (inducedGrid S)

/-- The spanning-tree count of the standard `r × s` lattice rectangle. -/
noncomputable def tauRect (r s : ℕ) : ℕ :=
  tau (rectangle 0 0 r s)

theorem tauRect_eq (r s : ℕ) :
    tauRect r s = tau (rectangle 0 0 r s) :=
  rfl

end SquareMaximality
