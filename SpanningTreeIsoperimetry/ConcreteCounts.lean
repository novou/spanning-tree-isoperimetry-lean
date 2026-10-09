import SpanningTreeIsoperimetry.MatrixTree
import SpanningTreeIsoperimetry.SmallCases
import Mathlib.Tactic.NormDet

/-! Exact counts of actual primal spanning trees in the exceptional small domains.
The coordinate lists, graph Laplacians and determinants are all checked in Lean.
No planar duality result or computed count is assumed. -/
namespace SpanningTreeIsoperimetry.ConcreteCounts

open SmallCases

private theorem lapMatrix_iso {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H) (i j : V) :
    H.lapMatrix ℤ (e i) (e j) = G.lapMatrix ℤ i j := by
  simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.diagonal,
    SimpleGraph.adjMatrix, e.degree_eq, e.injective.eq_iff, e.map_adj_iff]

/-- A primal coordinate Laplacian minor counts spanning trees of its domain. -/
theorem primal_cofactor_eq_treeCount {n : ℕ} (p : Fin (n + 1) → Vertex)
    (S : Domain) (e : pointGraph p ≃g domainGraph S) :
    (((pointGraph p).lapMatrix ℤ).submatrix Fin.succ Fin.succ).det = (treeCount S : ℤ) := by
  classical
  let d : Fin n ≃ (domainGraph S).DelVert (e 0) :=
    (finSuccAboveEquiv 0).trans (e.toEquiv.subtypeEquiv (by
      intro i
      exact e.injective.ne_iff.symm))
  rw [← treeCount_eq_laplacian_cofactor_int S (e 0),
    ← Matrix.det_submatrix_equiv_self d]
  congr 1
  ext i j
  change (pointGraph p).lapMatrix ℤ i.succ j.succ =
    (domainGraph S).lapMatrix ℤ (e ((0 : Fin (n + 1)).succAbove i))
      (e ((0 : Fin (n + 1)).succAbove j))
  simp only [Fin.zero_succAbove]
  exact (lapMatrix_iso e i.succ j.succ).symm

/-- The seventeen primal vertices, in lexicographic order. -/
def winner17Vertices : Fin 17 → Vertex := ![(0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 1), (3, 2), (3, 3)]

theorem winner17Vertices_injective : Function.Injective winner17Vertices := by decide

theorem winner17Vertices_image : Finset.univ.image winner17Vertices = winner17Domain := by decide

/-- The actual primal Laplacian cofactor, deleting the first listed vertex. -/
def winner17Cofactor : Matrix (Fin 16) (Fin 16) ℤ :=
  !![3, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    -1, 2, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 2, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, -1, 3, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
    -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0;
    0, -1, 0, 0, 0, -1, 3, 0, 0, 0, 0, -1, 0, 0, 0, 0;
    0, 0, -1, 0, 0, 0, 0, 3, -1, 0, 0, 0, -1, 0, 0, 0;
    0, 0, 0, -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0, 0;
    0, 0, 0, 0, -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 2, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 2, -1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 3, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 3, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 2]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem winner17Cofactor_eq :
    (((pointGraph winner17Vertices).lapMatrix ℤ).submatrix Fin.succ Fin.succ) =
      winner17Cofactor := by
  decide

set_option maxHeartbeats 2000000 in
theorem winner17Cofactor_det : winner17Cofactor.det = 112456 := by
  unfold winner17Cofactor
  eval_det

/-- The actual combinatorial tree count, not only the dual polynomial evaluation. -/
theorem winner17_treeCount : treeCount winner17Domain = 112456 := by
  have e : pointGraph winner17Vertices ≃g domainGraph winner17Domain := by
    rw [← winner17Vertices_image]
    exact pointGraphIso winner17Vertices winner17Vertices_injective
  have h := primal_cofactor_eq_treeCount winner17Vertices winner17Domain e
  rw [winner17Cofactor_eq, winner17Cofactor_det] at h
  exact_mod_cast h.symm

/-- The seventeen primal vertices, in lexicographic order. -/
def canonical17Vertices : Fin 17 → Vertex := ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5)]

theorem canonical17Vertices_injective : Function.Injective canonical17Vertices := by decide

theorem canonical17Vertices_image : Finset.univ.image canonical17Vertices = canonical17Domain := by decide

/-- The actual primal Laplacian cofactor, deleting the first listed vertex. -/
def canonical17Cofactor : Matrix (Fin 16) (Fin 16) ℤ :=
  !![3, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    -1, 3, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, -1, 3, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, -1, 2, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 2, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, -1, 4, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0;
    -1, 0, 0, 0, 0, -1, 4, -1, 0, 0, 0, 0, -1, 0, 0, 0;
    0, -1, 0, 0, 0, 0, -1, 4, -1, 0, 0, 0, 0, -1, 0, 0;
    0, 0, -1, 0, 0, 0, 0, -1, 4, -1, 0, 0, 0, 0, -1, 0;
    0, 0, 0, -1, 0, 0, 0, 0, -1, 3, 0, 0, 0, 0, 0, -1;
    0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 2, -1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 3, -1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 3, -1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 3, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 3, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 2]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem canonical17Cofactor_eq :
    (((pointGraph canonical17Vertices).lapMatrix ℤ).submatrix Fin.succ Fin.succ) =
      canonical17Cofactor := by
  decide

set_option maxHeartbeats 2000000 in
theorem canonical17Cofactor_det : canonical17Cofactor.det = 112272 := by
  unfold canonical17Cofactor
  eval_det

/-- The actual combinatorial tree count, not only the dual polynomial evaluation. -/
theorem canonical17_treeCount : treeCount canonical17Domain = 112272 := by
  have e : pointGraph canonical17Vertices ≃g domainGraph canonical17Domain := by
    rw [← canonical17Vertices_image]
    exact pointGraphIso canonical17Vertices canonical17Vertices_injective
  have h := primal_cofactor_eq_treeCount canonical17Vertices canonical17Domain e
  rw [canonical17Cofactor_eq, canonical17Cofactor_det] at h
  exact_mod_cast h.symm

/-- The actual connected counterexample has exactly 184 more spanning trees. -/
theorem seventeen_treeCount_improvement :
    treeCount winner17Domain = treeCount canonical17Domain + 184 := by
  rw [winner17_treeCount, canonical17_treeCount]

theorem winner17_connected : (domainGraph winner17Domain).Connected := by
  apply (treeCount_pos_iff_connected winner17Domain).mp
  rw [winner17_treeCount]
  decide

theorem canonical17_connected : (domainGraph canonical17Domain).Connected := by
  apply (treeCount_pos_iff_connected canonical17Domain).mp
  rw [canonical17_treeCount]
  decide

/-- The paper's canonical domain at seventeen is not a maximizer among all
connected induced lattice graphs of that size. This is a closed combinatorial
counterexample, independent of the reduction to exceptional candidate families. -/
theorem canonical17_not_isMaximizer : ¬ IsMaximizer canonical17Domain := by
  intro h
  have hcard : winner17Domain.card = canonical17Domain.card := by
    rw [seventeen_domain_sizes.1, seventeen_domain_sizes.2.2.2.1]
  have hle := h.2 winner17Domain hcard winner17_connected
  rw [winner17_treeCount, canonical17_treeCount] at hle
  omega

/-- The concrete primal domain at cardinality 7. -/
def winner7Domain : Domain := rectangle 3 3 \ {(0, 0), (2, 2)}

theorem winner7Domain_card : winner7Domain.card = 7 := by decide

def winner7Vertices : Fin 7 → Vertex := ![(0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1)]

theorem winner7Vertices_injective : Function.Injective winner7Vertices := by decide

theorem winner7Vertices_image : Finset.univ.image winner7Vertices = winner7Domain := by decide

/-- The primal Laplacian cofactor, deleting the first listed vertex. -/
def winner7Cofactor : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2, 0, 0, -1, 0, 0;
    0, 2, -1, 0, -1, 0;
    0, -1, 4, -1, 0, -1;
    -1, 0, -1, 2, 0, 0;
    0, -1, 0, 0, 2, -1;
    0, 0, -1, 0, -1, 2]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem winner7Cofactor_eq :
    (((pointGraph winner7Vertices).lapMatrix ℤ).submatrix Fin.succ Fin.succ) =
      winner7Cofactor := by
  decide

set_option maxHeartbeats 2000000 in
theorem winner7Cofactor_det : winner7Cofactor.det = 16 := by
  unfold winner7Cofactor
  eval_det

theorem winner7_treeCount : treeCount winner7Domain = 16 := by
  have e : pointGraph winner7Vertices ≃g domainGraph winner7Domain := by
    rw [← winner7Vertices_image]
    exact pointGraphIso winner7Vertices winner7Vertices_injective
  have h := primal_cofactor_eq_treeCount winner7Vertices winner7Domain e
  rw [winner7Cofactor_eq, winner7Cofactor_det] at h
  exact_mod_cast h.symm

theorem winner7_connected : (domainGraph winner7Domain).Connected := by
  apply (treeCount_pos_iff_connected winner7Domain).mp
  rw [winner7_treeCount]
  decide

/-- The concrete primal domain at cardinality 7. -/
def canonical7Domain : Domain := rectangle 2 4 \ {(0, 0)}

theorem canonical7Domain_card : canonical7Domain.card = 7 := by decide

def canonical7Vertices : Fin 7 → Vertex := ![(0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3)]

theorem canonical7Vertices_injective : Function.Injective canonical7Vertices := by decide

theorem canonical7Vertices_image : Finset.univ.image canonical7Vertices = canonical7Domain := by decide

/-- The primal Laplacian cofactor, deleting the first listed vertex. -/
def canonical7Cofactor : Matrix (Fin 6) (Fin 6) ℤ :=
  !![3, -1, 0, 0, -1, 0;
    -1, 2, 0, 0, 0, -1;
    0, 0, 1, -1, 0, 0;
    0, 0, -1, 3, -1, 0;
    -1, 0, 0, -1, 3, -1;
    0, -1, 0, 0, -1, 2]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem canonical7Cofactor_eq :
    (((pointGraph canonical7Vertices).lapMatrix ℤ).submatrix Fin.succ Fin.succ) =
      canonical7Cofactor := by
  decide

set_option maxHeartbeats 2000000 in
theorem canonical7Cofactor_det : canonical7Cofactor.det = 15 := by
  unfold canonical7Cofactor
  eval_det

theorem canonical7_treeCount : treeCount canonical7Domain = 15 := by
  have e : pointGraph canonical7Vertices ≃g domainGraph canonical7Domain := by
    rw [← canonical7Vertices_image]
    exact pointGraphIso canonical7Vertices canonical7Vertices_injective
  have h := primal_cofactor_eq_treeCount canonical7Vertices canonical7Domain e
  rw [canonical7Cofactor_eq, canonical7Cofactor_det] at h
  exact_mod_cast h.symm

theorem canonical7_connected : (domainGraph canonical7Domain).Connected := by
  apply (treeCount_pos_iff_connected canonical7Domain).mp
  rw [canonical7_treeCount]
  decide

/-- The concrete primal domain at cardinality 14. -/
def winner14Domain : Domain := rectangle 4 4 \ {(0, 0), (3, 3)}

theorem winner14Domain_card : winner14Domain.card = 14 := by decide

def winner14Vertices : Fin 14 → Vertex := ![(0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2)]

theorem winner14Vertices_injective : Function.Injective winner14Vertices := by decide

theorem winner14Vertices_image : Finset.univ.image winner14Vertices = winner14Domain := by decide

/-- The primal Laplacian cofactor, deleting the first listed vertex. -/
def winner14Cofactor : Matrix (Fin 13) (Fin 13) ℤ :=
  !![3, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0;
    -1, 2, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 2, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0;
    0, 0, -1, 4, -1, 0, 0, -1, 0, 0, 0, 0, 0;
    -1, 0, 0, -1, 4, -1, 0, 0, -1, 0, 0, 0, 0;
    0, -1, 0, 0, -1, 3, 0, 0, 0, -1, 0, 0, 0;
    0, 0, -1, 0, 0, 0, 3, -1, 0, 0, -1, 0, 0;
    0, 0, 0, -1, 0, 0, -1, 4, -1, 0, 0, -1, 0;
    0, 0, 0, 0, -1, 0, 0, -1, 4, -1, 0, 0, -1;
    0, 0, 0, 0, 0, -1, 0, 0, -1, 2, 0, 0, 0;
    0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 2, -1, 0;
    0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 3, -1;
    0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 2]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem winner14Cofactor_eq :
    (((pointGraph winner14Vertices).lapMatrix ℤ).submatrix Fin.succ Fin.succ) =
      winner14Cofactor := by
  decide

set_option maxHeartbeats 2000000 in
theorem winner14Cofactor_det : winner14Cofactor.det = 8960 := by
  unfold winner14Cofactor
  eval_det

theorem winner14_treeCount : treeCount winner14Domain = 8960 := by
  have e : pointGraph winner14Vertices ≃g domainGraph winner14Domain := by
    rw [← winner14Vertices_image]
    exact pointGraphIso winner14Vertices winner14Vertices_injective
  have h := primal_cofactor_eq_treeCount winner14Vertices winner14Domain e
  rw [winner14Cofactor_eq, winner14Cofactor_det] at h
  exact_mod_cast h.symm

theorem winner14_connected : (domainGraph winner14Domain).Connected := by
  apply (treeCount_pos_iff_connected winner14Domain).mp
  rw [winner14_treeCount]
  decide

/-- The concrete primal domain at cardinality 14. -/
def canonical14Domain : Domain := rectangle 3 5 \ {(0, 0)}

theorem canonical14Domain_card : canonical14Domain.card = 14 := by decide

def canonical14Vertices : Fin 14 → Vertex := ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)]

theorem canonical14Vertices_injective : Function.Injective canonical14Vertices := by decide

theorem canonical14Vertices_image : Finset.univ.image canonical14Vertices = canonical14Domain := by decide

/-- The primal Laplacian cofactor, deleting the first listed vertex. -/
def canonical14Cofactor : Matrix (Fin 13) (Fin 13) ℤ :=
  !![3, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0;
    -1, 3, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0;
    0, -1, 2, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0;
    0, 0, 0, 2, -1, 0, 0, 0, -1, 0, 0, 0, 0;
    0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0, 0, 0;
    -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0, 0;
    0, -1, 0, 0, 0, -1, 4, -1, 0, 0, 0, -1, 0;
    0, 0, -1, 0, 0, 0, -1, 3, 0, 0, 0, 0, -1;
    0, 0, 0, -1, 0, 0, 0, 0, 2, -1, 0, 0, 0;
    0, 0, 0, 0, -1, 0, 0, 0, -1, 3, -1, 0, 0;
    0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 3, -1, 0;
    0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 3, -1;
    0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 2]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem canonical14Cofactor_eq :
    (((pointGraph canonical14Vertices).lapMatrix ℤ).submatrix Fin.succ Fin.succ) =
      canonical14Cofactor := by
  decide

set_option maxHeartbeats 2000000 in
theorem canonical14Cofactor_det : canonical14Cofactor.det = 8948 := by
  unfold canonical14Cofactor
  eval_det

theorem canonical14_treeCount : treeCount canonical14Domain = 8948 := by
  have e : pointGraph canonical14Vertices ≃g domainGraph canonical14Domain := by
    rw [← canonical14Vertices_image]
    exact pointGraphIso canonical14Vertices canonical14Vertices_injective
  have h := primal_cofactor_eq_treeCount canonical14Vertices canonical14Domain e
  rw [canonical14Cofactor_eq, canonical14Cofactor_det] at h
  exact_mod_cast h.symm

theorem canonical14_connected : (domainGraph canonical14Domain).Connected := by
  apply (treeCount_pos_iff_connected canonical14Domain).mp
  rw [canonical14_treeCount]
  decide

theorem improvement7 :
    treeCount winner7Domain = treeCount canonical7Domain + 1 := by
  rw [winner7_treeCount, canonical7_treeCount]

/-- A closed counterexample to canonical maximality at cardinality 7. -/
theorem canonical7_not_isMaximizer : ¬ IsMaximizer canonical7Domain := by
  intro h
  have hcard : winner7Domain.card = canonical7Domain.card := by
    rw [winner7Domain_card, canonical7Domain_card]
  have hle := h.2 winner7Domain hcard winner7_connected
  rw [winner7_treeCount, canonical7_treeCount] at hle
  omega

theorem improvement14 :
    treeCount winner14Domain = treeCount canonical14Domain + 12 := by
  rw [winner14_treeCount, canonical14_treeCount]

/-- A closed counterexample to canonical maximality at cardinality 14. -/
theorem canonical14_not_isMaximizer : ¬ IsMaximizer canonical14Domain := by
  intro h
  have hcard : winner14Domain.card = canonical14Domain.card := by
    rw [winner14Domain_card, canonical14Domain_card]
  have hle := h.2 winner14Domain hcard winner14_connected
  rw [winner14_treeCount, canonical14_treeCount] at hle
  omega

end SpanningTreeIsoperimetry.ConcreteCounts
