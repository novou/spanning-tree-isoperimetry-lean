import SpanningTreeIsoperimetry.SmallCases
import SpanningTreeIsoperimetry.StripPolarization
import SpanningTreeIsoperimetry.DomainIsometries

/-! The checked small coordinate-matrix polynomials are the actual face
determinants used in primal tree-count comparisons. -/
namespace SpanningTreeIsoperimetry.FiniteFaceCountBridge
open SmallCases StripPolarization DomainIsometries
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem pointMatrix_eq_shifted {n : ℕ} (p : Fin n → Vertex) (z : ℝ) :
    pointMatrix p z=z • (1 : Matrix (Fin n) (Fin n) ℝ)-(pointGraph p).adjMatrix ℝ := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp [pointMatrix,pointGraph,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,SimpleGraph.adjMatrix,Matrix.of_apply]
  · by_cases ha : lattice.Adj (p i) (p j)
    · simp only [lattice] at ha
      simp [pointMatrix,pointGraph,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
        Matrix.one_apply,SimpleGraph.adjMatrix,Matrix.of_apply,hij,ha]
    · simp only [lattice] at ha
      simp [pointMatrix,pointGraph,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
        Matrix.one_apply,SimpleGraph.adjMatrix,Matrix.of_apply,hij,ha]

theorem faceDeterminant_points {n : ℕ} (p : Fin n → Vertex) (hinj : Function.Injective p) (z : ℝ) :
    faceDeterminant (Finset.univ.image p) z=Matrix.det (pointMatrix p z) := by
  have h:=shiftedAdjacency_det_iso (pointGraph p) (domainGraph (Finset.univ.image p))
    (pointGraphIso p hinj) z
  exact h.symm.trans (congrArg Matrix.det (pointMatrix_eq_shifted p z).symm)

end SpanningTreeIsoperimetry.FiniteFaceCountBridge
