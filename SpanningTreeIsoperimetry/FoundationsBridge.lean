module

public import SpanningTreeIsoperimetry.Grid
public import SpanningTreeIsoperimetry.LocalBounds
public import SquareMaximality.Infrastructure
public import SquareMaximality.Constants

@[expose] public section

/-! Definition-level bridges to the complete proofs included under Foundations.
These are actual equalities, not assumptions identifying two tree-count models. -/
namespace SpanningTreeIsoperimetry

 theorem lattice_eq_foundation : lattice = SquareMaximality.squareLattice := by
  ext p q
  change (p.1 = q.1 ∧ |p.2-q.2| = 1 ∨ p.2 = q.2 ∧ |p.1-q.1| = 1) ↔
    SquareMaximality.manhattanDist p q = 1
  rw [SquareMaximality.manhattanDist_eq_one_iff]
  rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1), abs_eq (by norm_num : (0 : ℤ) ≤ 1)]
  omega

theorem domainGraph_eq_foundation (S : Domain) :
    domainGraph S = SquareMaximality.inducedGrid S := by
  ext u v
  change lattice.Adj u.val v.val ↔ SquareMaximality.squareLattice.Adj u.val v.val
  rw [lattice_eq_foundation]

theorem treeCount_eq_foundation (S : Domain) : treeCount S = SquareMaximality.tau S := by
  unfold treeCount SpanningTrees SquareMaximality.tau SquareMaximality.treeCount
  rw [domainGraph_eq_foundation]
  rfl

theorem rectangle_eq_foundation (r s : ℕ) :
    rectangle r s = SquareMaximality.rectangle 0 0 r s := by
  simp [rectangle, SquareMaximality.rectangle]

theorem rectangle_treeCount_eq_foundation (r s : ℕ) :
    treeCount (rectangle r s) = SquareMaximality.tauRect r s := by
  rw [treeCount_eq_foundation, rectangle_eq_foundation]
  rfl

theorem catalan_eq_foundation :
    LocalBounds.catalanConstant = SquareMaximality.catalanConstant := by
  unfold LocalBounds.catalanConstant SquareMaximality.catalanConstant
  apply tsum_congr
  intro n
  simp [LocalBounds.catalanTerm, div_eq_mul_inv]

theorem entropy_eq_foundation :
    LocalBounds.entropyConstant = SquareMaximality.squareLatticeEntropy := by
  unfold LocalBounds.entropyConstant SquareMaximality.squareLatticeEntropy
  rw [catalan_eq_foundation]

end SpanningTreeIsoperimetry
