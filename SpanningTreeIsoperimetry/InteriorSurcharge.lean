module

public import SpanningTreeIsoperimetry.MatrixTree
public import SpanningTreeIsoperimetry.SmallCases
public import SpanningTreeIsoperimetry.LocalBounds
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Tactic.NormDet

@[expose] public section

/-!
# Graph-theoretic ingredients for the interior surcharge

This module first identifies the actual uniform-spanning-tree avoidance
probability of the two central perpendicular edges in the free five-by-five
patch. Both graph counts are obtained from locally proved Matrix--Tree and
kernel-checked integer determinants. It does not yet assert the full interior
surcharge: wiring/Rayleigh transport and the strengthened square-family bound
are separate proof obligations.
-/
namespace SpanningTreeIsoperimetry.InteriorSurcharge

/-- Number of trees of `G` avoiding every edge in `E`. -/
noncomputable def edgeAvoidanceCount {V : Type*} (G : SimpleGraph V)
    (E : Set (Sym2 V)) : ℕ :=
  Nat.card {T : SimpleGraph V // T ≤ G ∧ T.IsTree ∧ Disjoint T.edgeSet E}

/-- An actual event probability under the uniform distribution on spanning
trees. Positivity of the denominator is supplied in applications. -/
noncomputable def edgeAvoidanceProbability {V : Type*} [Fintype V]
    (G : SimpleGraph V) (E : Set (Sym2 V)) : ℝ :=
  (edgeAvoidanceCount G E : ℝ) / G.spanningTreeCount

/-- Counting the avoidance event is exactly counting trees after edge deletion. -/
theorem edgeAvoidanceCount_eq_deleteEdges {V : Type*} [Fintype V]
    (G : SimpleGraph V) (E : Set (Sym2 V)) :
    edgeAvoidanceCount G E = (G.deleteEdges E).spanningTreeCount := by
  unfold edgeAvoidanceCount SimpleGraph.spanningTreeCount SimpleGraph.SpanningTree
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro T
  rw [SimpleGraph.deleteEdges, le_sdiff, SimpleGraph.disjoint_fromEdgeSet]
  tauto

/-- A Laplacian cofactor on the numbered primal vertices counts actual trees. -/
theorem cofactor_eq_spanningTreeCount {n : ℕ} (G : SimpleGraph (Fin (n + 1)))
    [DecidableRel G.Adj] :
    ((G.lapMatrix ℤ).submatrix Fin.succ Fin.succ).det =
      (G.spanningTreeCount : ℤ) := by
  classical
  rw [← SimpleGraph.kirchhoff_matrix_tree_int G (0 : Fin (n + 1)),
    ← Matrix.det_submatrix_equiv_self (finSuccAboveEquiv (0 : Fin (n + 1)))]
  congr 1

/-- Lexicographically ordered points of the free five-by-five grid. -/
def patchPoints : Fin 25 → Vertex :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4),
    (1, 0), (1, 1), (1, 2), (1, 3), (1, 4),
    (2, 0), (2, 1), (2, 2), (2, 3), (2, 4),
    (3, 0), (3, 1), (3, 2), (3, 3), (3, 4),
    (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)]

def freePatch : SimpleGraph (Fin 25) := SmallCases.pointGraph patchPoints

instance : DecidableRel freePatch.Adj :=
  inferInstanceAs (DecidableRel (SmallCases.pointGraph patchPoints).Adj)

/-- The east and north edges out of the center `(2,2)`. -/
def centralEdges : Finset (Sym2 (Fin 25)) := {s(12, 17), s(12, 13)}

def cutPatch : SimpleGraph (Fin 25) := freePatch.deleteEdges centralEdges

instance : DecidableRel cutPatch.Adj :=
  inferInstanceAs (DecidableRel (freePatch.deleteEdges (centralEdges : Set (Sym2 (Fin 25)))).Adj)

theorem centralEdges_coordinates :
    patchPoints 12 = (2, 2) ∧ patchPoints 17 = (3, 2) ∧
      patchPoints 13 = (2, 3) := by decide

theorem centralEdges_in_patch : (centralEdges : Set (Sym2 (Fin 25))) ⊆ freePatch.edgeSet := by
  intro e he
  have he' : e = s(12, 17) ∨ e = s(12, 13) := by simpa [centralEdges] using he
  rcases he' with rfl | rfl
  · change freePatch.Adj 12 17
    decide
  · change freePatch.Adj 12 13
    decide

/-- The actual graph Laplacian cofactor after removing vertex `(0,0)`. -/
def freePatchCofactor : Matrix (Fin 24) (Fin 24) ℤ :=
  !![3, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    -1, 3, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, -1, 3, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, -1, 2, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 3, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, -1, 0, 0, 0, -1, 3, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, -1, 0, 0, 0, 0, 3, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 3, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 3, -1, 0, 0, 0, -1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 3, 0, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 2, -1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 3, -1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 3, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 3, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 2]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem freePatchCofactor_eq :
    ((freePatch.lapMatrix ℤ).submatrix Fin.succ Fin.succ) = freePatchCofactor := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem freePatchCofactor_det : freePatchCofactor.det = 557568000 := by
  unfold freePatchCofactor
  eval_det

/-- The combinatorial spanning-tree count of the explicitly specified graph. -/
theorem freePatch_treeCount : freePatch.spanningTreeCount = 557568000 := by
  have h := cofactor_eq_spanningTreeCount freePatch
  rw [freePatchCofactor_eq, freePatchCofactor_det] at h
  exact_mod_cast h.symm

/-- The actual graph Laplacian cofactor after removing vertex `(0,0)`. -/
def cutPatchCofactor : Matrix (Fin 24) (Fin 24) ℤ :=
  !![3, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    -1, 3, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, -1, 3, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, -1, 2, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 3, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, -1, 0, 0, 0, -1, 3, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, -1, 0, 0, 0, 0, 3, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 3, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 3, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 3, -1, 0, 0, 0, -1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 3, -1, 0, 0, 0, -1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 3, 0, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 2, -1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 3, -1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 3, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 3, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 2]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem cutPatchCofactor_eq :
    ((cutPatch.lapMatrix ℤ).submatrix Fin.succ Fin.succ) = cutPatchCofactor := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem cutPatchCofactor_det : cutPatchCofactor.det = 107976960 := by
  unfold cutPatchCofactor
  eval_det

/-- The combinatorial spanning-tree count of the explicitly specified graph. -/
theorem cutPatch_treeCount : cutPatch.spanningTreeCount = 107976960 := by
  have h := cofactor_eq_spanningTreeCount cutPatch
  rw [cutPatchCofactor_eq, cutPatchCofactor_det] at h
  exact_mod_cast h.symm

/-- The uniform spanning tree of the free patch avoids both specified central
perpendicular edges with probability exactly `9373 / 48400`. -/
theorem freePatch_avoidanceProbability :
    edgeAvoidanceProbability freePatch centralEdges = (9373 : ℝ) / 48400 := by
  unfold edgeAvoidanceProbability
  rw [edgeAvoidanceCount_eq_deleteEdges]
  change (cutPatch.spanningTreeCount : ℝ) / freePatch.spanningTreeCount = _
  rw [freePatch_treeCount, cutPatch_treeCount]
  norm_num

/-- The strict local margin required by the interior-vacancy argument. -/
theorem freePatch_avoidanceProbability_gt :
    (3 : ℝ) / 16 < edgeAvoidanceProbability freePatch centralEdges := by
  rw [freePatch_avoidanceProbability]
  norm_num

/-- The exact finite-graph calculation agrees with the displayed local matrix. -/
theorem freePatch_avoidanceProbability_eq_localDet :
    edgeAvoidanceProbability freePatch centralEdges =
      ((Matrix.det (1 - LocalBounds.localTransferMatrix) : ℚ) : ℝ) := by
  rw [freePatch_avoidanceProbability, LocalBounds.localTransferMatrix_det_complement]
  norm_num

end SpanningTreeIsoperimetry.InteriorSurcharge
