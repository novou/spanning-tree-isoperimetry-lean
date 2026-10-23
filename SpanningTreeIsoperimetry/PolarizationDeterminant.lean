module

public import SpanningTreeIsoperimetry.PolarizationReflections
public import SpanningTreeIsoperimetry.DomainSpectral
public import SpanningTreeIsoperimetry.DeterminantComparison

@[expose] public section

/-! Concrete finite-lattice determinant inequalities for polarization. -/
namespace SpanningTreeIsoperimetry.Polarization

open scoped Classical

theorem domainKernel_adjacency (U : Domain) :
    domainKernel adjacencyKernel U = (domainGraph U).adjMatrix ℝ := by
  ext i j
  rfl

theorem domainKernel_holding (U : Domain) :
    domainKernel holdingKernel U = 1 + (domainGraph U).adjMatrix ℝ := by
  rw [← domainKernel_adjacency]
  ext i j
  simp only [domainKernel, holdingKernel, Matrix.add_apply, Matrix.one_apply, Subtype.ext_iff]

theorem shift_holding (U : Domain) (z : ℝ) :
    (z + 1) • (1 : Matrix U U ℝ) - (1 + (domainGraph U).adjMatrix ℝ) =
      z • (1 : Matrix U U ℝ) - (domainGraph U).adjMatrix ℝ := by
  rw [add_smul, one_smul]
  abel

theorem det_shift_holding (U : Domain) (z : ℝ) :
    Matrix.det ((z + 1) • (1 : Matrix (U : Set Vertex) (U : Set Vertex) ℝ) -
        (1 + (domainGraph U).adjMatrix ℝ)) =
      Matrix.det (z • (1 : Matrix (U : Set Vertex) (U : Set Vertex) ℝ) -
        (domainGraph U).adjMatrix ℝ) := by
  congr 1
  rw [add_smul, one_smul]
  abel

theorem adjacency_determinant_of_domain_moments (U V : Domain) (hcard : U.card = V.card)
    (htrace : ∀ n : ℕ, Matrix.trace (domainKernel adjacencyKernel U ^ (n + 1)) ≤
      Matrix.trace (domainKernel adjacencyKernel V ^ (n + 1)))
    (z : ℝ) (hz : 4 ≤ z) :
    Matrix.det (z • (1 : Matrix V V ℝ) - (domainGraph V).adjMatrix ℝ) ≤
      Matrix.det (z • (1 : Matrix U U ℝ) - (domainGraph U).adjMatrix ℝ) := by
  apply DeterminantComparison.determinant_le_of_trace_le
    (DomainSpectral.adjacency_isHermitian U) (DomainSpectral.adjacency_isHermitian V)
    (by linarith : 0 < z)
    (fun i => (DomainSpectral.adjacency_eigenvalues_bound U i).trans_le hz)
    (fun i => (DomainSpectral.adjacency_eigenvalues_bound V i).trans_le hz)
  · simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hcard
  · intro n
    simpa only [domainKernel_adjacency] using htrace n

theorem holding_determinant_of_domain_moments (U V : Domain) (hcard : U.card = V.card)
    (htrace : ∀ n : ℕ, Matrix.trace (domainKernel holdingKernel U ^ (n + 1)) ≤
      Matrix.trace (domainKernel holdingKernel V ^ (n + 1)))
    (z : ℝ) (hz : 4 ≤ z) :
    Matrix.det (z • (1 : Matrix V V ℝ) - (domainGraph V).adjMatrix ℝ) ≤
      Matrix.det (z • (1 : Matrix U U ℝ) - (domainGraph U).adjMatrix ℝ) := by
  have h := DeterminantComparison.determinant_le_of_trace_le
    (DomainSpectral.holding_isHermitian U) (DomainSpectral.holding_isHermitian V)
    (c := z + 1) (by linarith : 0 < z + 1)
    (fun i => (DomainSpectral.holding_eigenvalues_bound U i).trans_le (by linarith))
    (fun i => (DomainSpectral.holding_eigenvalues_bound V i).trans_le (by linarith))
    (by simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hcard)
    (fun n => by simpa only [domainKernel_holding] using htrace n)
  simpa only [det_shift_holding] using h

/-- Determinant polarization for a horizontal axis, including half-integer axes. -/
theorem axial_determinant (U : Domain) (c : ℤ) (z : ℝ) (hz : 4 ≤ z) :
    let P := polarized U (axialReflection c) (fun x => c < 2 * x.2)
    Matrix.det (z • (1 : Matrix P P ℝ) - (domainGraph P).adjMatrix ℝ) ≤
      Matrix.det (z • (1 : Matrix U U ℝ) - (domainGraph U).adjMatrix ℝ) := by
  apply holding_determinant_of_domain_moments
  · exact (card_polarized (axialReflection_involutive c) _ (axial_preferred_side c)).symm
  · intro n
    exact axial_holding_moments U c (n + 1)
  · exact hz

/-- Determinant polarization for the reflection about `y=x+c`. -/
theorem shiftedDiagonal_determinant (U : Domain) (c : ℤ) (z : ℝ) (hz : 4 ≤ z) :
    let P := polarized U (shiftedDiagonalReflection c) (fun x => x.1 + c < x.2)
    Matrix.det (z • (1 : Matrix P P ℝ) - (domainGraph P).adjMatrix ℝ) ≤
      Matrix.det (z • (1 : Matrix U U ℝ) - (domainGraph U).adjMatrix ℝ) := by
  apply adjacency_determinant_of_domain_moments
  · exact (card_polarized (shiftedDiagonal_involutive c) _ (shiftedDiagonal_side c)).symm
  · intro n
    exact shiftedDiagonal_adjacency_moments U c (n + 1)
  · exact hz

/-- Determinant polarization for the reflection about `x+y=c`. -/
theorem antiDiagonal_determinant (U : Domain) (c : ℤ) (z : ℝ) (hz : 4 ≤ z) :
    let P := polarized U (antiDiagonalReflection c) (fun x => x.1 + x.2 < c)
    Matrix.det (z • (1 : Matrix P P ℝ) - (domainGraph P).adjMatrix ℝ) ≤
      Matrix.det (z • (1 : Matrix U U ℝ) - (domainGraph U).adjMatrix ℝ) := by
  apply adjacency_determinant_of_domain_moments
  · exact (card_polarized (antiDiagonal_involutive c) _ (antiDiagonal_side c)).symm
  · intro n
    exact antiDiagonal_adjacency_moments U c (n + 1)
  · exact hz

theorem vertical_determinant (U : Domain) (c : ℤ) (z : ℝ) (hz : 4 ≤ z) :
    let P := polarized U (verticalReflection c) (fun x => c < 2 * x.1)
    Matrix.det (z • (1 : Matrix P P ℝ) - (domainGraph P).adjMatrix ℝ) ≤
      Matrix.det (z • (1 : Matrix U U ℝ) - (domainGraph U).adjMatrix ℝ) := by
  apply holding_determinant_of_domain_moments
  · exact (card_polarized (vertical_involutive c) _ (vertical_preferred_side c)).symm
  · intro n
    exact vertical_holding_moments U c (n + 1)
  · exact hz

end SpanningTreeIsoperimetry.Polarization

