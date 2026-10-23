module

public import SpanningTreeIsoperimetry.Grid
public import SpanningTreeIsoperimetry.External.KirchhoffMatrixTree

@[expose] public section

/-! Kirchhoff's theorem for the actual combinatorial lattice tree count. -/
namespace SpanningTreeIsoperimetry

open scoped Classical in
theorem treeCount_eq_laplacian_cofactor_int (S : Domain) (q : (S : Set Vertex)) :
    ((domainGraph S).reducedLaplacian ℤ q).det = (treeCount S : ℤ) := by
  exact SimpleGraph.kirchhoff_matrix_tree_int (domainGraph S) q

open scoped Classical in
theorem treeCount_eq_laplacian_cofactor (S : Domain) (q : (S : Set Vertex)) :
    ((domainGraph S).reducedLaplacian ℝ q).det = (treeCount S : ℝ) := by
  exact SimpleGraph.kirchhoff_matrix_tree (domainGraph S) q

open scoped Classical in
theorem laplacian_cofactor_pos_iff_connected (S : Domain) (q : (S : Set Vertex)) :
    0 < ((domainGraph S).reducedLaplacian ℝ q).det ↔ (domainGraph S).Connected := by
  rw [treeCount_eq_laplacian_cofactor, Nat.cast_pos, treeCount_pos_iff_connected]

end SpanningTreeIsoperimetry
