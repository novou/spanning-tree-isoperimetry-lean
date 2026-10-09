import SquareMaximality.Paper

/-!
# Main theorems

This module exposes the closed end-to-end results of the paper formalization.
Internal modules use parameterized propositions to organize the proof. Every
such input is constructed before the declarations below, so none is an
assumption of the public theorems.
-/

set_option autoImplicit false

namespace SquareMaximality

universe uV uE

/-- Kirchhoff's Matrix--Tree theorem for finite edge-labelled undirected
multigraphs. Parallel labels are counted separately and loops contribute
zero incidence columns. -/
theorem matrixTreeTheorem :
    LabeledMultigraphCofactorInput.{uV, uE} :=
  labeledMultigraphCofactorInput

/-- Among induced square-lattice graphs on `n ^ 2` vertices, the `n × n`
square has maximal spanning-tree count. -/
theorem squareMaximality
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2) :
    tau S ≤ tauRect n n :=
  paper_squareMaximality hn S hcard

/-- Equality in square maximality holds exactly for a translate of the
standard `n × n` lattice square. -/
theorem equality_iff_latticeSquare
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2) :
    tau S = tauRect n n ↔ IsLatticeSquare S n :=
  paper_equality_iff_latticeSquare hn S hcard

/-- Maximality for an arbitrary spanning subgraph of the induced lattice
graph. -/
theorem spanningSubgraph_squareMaximality
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2)
    (G : SimpleGraph {p : Point // p ∈ S}) (hG : G ≤ inducedGrid S) :
    treeCount G ≤ tauRect n n :=
  paper_spanningSubgraph_squareMaximality
    hn S hcard G hG

/-- Every proper connected spanning subgraph lies strictly below the square
maximum. -/
theorem spanningSubgraph_lt_square
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2)
    (G : SimpleGraph {p : Point // p ∈ S}) (hconn : G.Connected)
    (hproper : G < inducedGrid S) :
    treeCount G < tauRect n n :=
  paper_spanningSubgraph_lt_square
    hn S hcard G hconn hproper

/-- Equality for an arbitrary square-lattice spanning subgraph requires both
the full induced edge set and a translated `n × n` square vertex set. -/
theorem spanningSubgraph_equality_iff
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2)
    (G : SimpleGraph {p : Point // p ∈ S}) (hG : G ≤ inducedGrid S) :
    treeCount G = tauRect n n ↔
      G = inducedGrid S ∧ IsLatticeSquare S n :=
  paper_spanningSubgraph_equality_iff
    hn S hcard G hG

end SquareMaximality
