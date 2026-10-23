module

public import SquareMaximality.Inputs.MatrixTreeProof
public import SquareMaximality.LinearAlgebra.GramCauchyBinet

@[expose] public section

set_option autoImplicit false

/-!
# Kirchhoff's Matrix--Tree theorem

This module discharges the explicit `LabeledMultigraphCofactorInput` used by
the paper.  Cauchy--Binet writes the determinant of the reduced incidence
Gram matrix as a sum of squared maximal minors.  Total unimodularity and the
incidence-kernel argument in `MatrixTreeProof` identify each summand with the
indicator of a labelled spanning tree.
-/

namespace SquareMaximality

open scoped BigOperators Matrix

namespace Multigraph
namespace LabeledMultigraph

noncomputable section

universe uV uE

variable {V : Type uV} {E : Type uE} [DecidableEq V]
    (G : LabeledMultigraph V E)

noncomputable local instance matrixTreeTheoremDecidableEqE : DecidableEq E :=
  Classical.decEq E
noncomputable local instance (priority := 100) matrixTreeTheoremDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The canonical maximal minor used by Gram Cauchy--Binet has the same
determinant square as the selected incidence minor used in the combinatorial
classification.  The two constructions differ only in their row and column
orderings. -/
theorem maximalMinor_kirchhoffReducedIncidence_sq
    [Fintype V] [Fintype E] (root : V) (F : Finset E)
    (hcard : F.card = Fintype.card (AwayFrom root)) :
    GramCauchyBinet.maximalMinor (G.kirchhoffReducedIncidence root) F ^ 2 =
      if G.IsSpanningTree F then 1 else 0 := by
  have hVpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨root⟩
  have hAway : Fintype.card (AwayFrom root) = Fintype.card V - 1 := by
    change Fintype.card {v : V // ¬v = root} = _
    rw [Fintype.card_subtype_compl]
    simp
  have hfullcard : F.card + 1 = Fintype.card V := by
    rw [hcard, hAway]
    omega
  have hsubcard : Fintype.card F = Fintype.card (AwayFrom root) := by
    simpa using hcard
  rw [GramCauchyBinet.maximalMinor, dif_pos hsubcard]
  let e : F ≃ AwayFrom root := Fintype.equivOfCardEq hsubcard
  let q : AwayFrom root ≃ F := G.awayEquivSelectedEdge root F hfullcard
  let M := G.selectedIncidenceMinor root F hfullcard
  have hmatrix :
      (G.kirchhoffReducedIncidence root).submatrix e Subtype.val =
        M.submatrix e q.symm := by
    ext i j
    simp only [M, selectedIncidenceMinor, kirchhoffReducedIncidence,
      Matrix.submatrix_apply]
    change G.kirchhoffIncidence (e i).1 j.1 =
      G.kirchhoffIncidence (e i).1 (q (q.symm j)).1
    rw [q.apply_symm_apply]
  have habs :
      |Matrix.det ((G.kirchhoffReducedIncidence root).submatrix e Subtype.val)| =
        |Matrix.det M| := by
    rw [hmatrix]
    exact Matrix.abs_det_submatrix_equiv_equiv e q.symm M
  change Matrix.det
      ((G.kirchhoffReducedIncidence root).submatrix e Subtype.val) ^ 2 = _
  calc
    Matrix.det
          ((G.kirchhoffReducedIncidence root).submatrix e Subtype.val) ^ 2 =
        |Matrix.det
          ((G.kirchhoffReducedIncidence root).submatrix e Subtype.val)| ^ 2 := by
            rw [sq_abs]
    _ = |Matrix.det M| ^ 2 := congrArg (fun z : ℤ => z ^ 2) habs
    _ = Matrix.det M ^ 2 := sq_abs _
    _ = if G.IsSpanningTree F then 1 else 0 := by
      simpa only [M] using G.selectedIncidenceMinor_det_sq root F hfullcard

/-- Summing the spanning-tree indicators over all edge sets of the required
cardinality gives the labelled spanning-tree count. -/
theorem sum_spanningTreeIndicators_eq_count
    [Fintype V] [Fintype E] (root : V) :
    (∑ F ∈ Finset.univ.powersetCard (Fintype.card (AwayFrom root)),
        if G.IsSpanningTree F then (1 : ℤ) else 0) =
      (G.spanningTreeCount : ℤ) := by
  let P : Finset (Finset E) :=
    Finset.univ.powersetCard (Fintype.card (AwayFrom root))
  have hAway : Fintype.card (AwayFrom root) + 1 = Fintype.card V := by
    have hVpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨root⟩
    change Fintype.card {v : V // ¬v = root} + 1 = _
    rw [Fintype.card_subtype_compl]
    simp
    omega
  have hfilter :
      P.filter (fun F => G.IsSpanningTree F) =
        Finset.univ.filter (fun F => G.IsSpanningTree F) := by
    ext F
    simp only [P, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.mem_univ, Finset.subset_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro htree
      refine ⟨?_, htree⟩
      have htreeCard := htree.card_edges_add_one
      omega
  change (∑ F ∈ P, if G.IsSpanningTree F then (1 : ℤ) else 0) = _
  rw [Finset.sum_boole, hfilter]
  norm_cast
  unfold spanningTreeCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

end

end LabeledMultigraph
end Multigraph

universe uV uE

/-- Kirchhoff's Matrix--Tree theorem for finite labelled multigraphs.
Parallel labels are counted separately and loops contribute zero incidence
columns, exactly matching `LabeledMultigraph.spanningTreeCount`. -/
theorem labeledMultigraphCofactorInput :
    LabeledMultigraphCofactorInput.{uV, uE} := by
  intro V E _hV hdecV hfiniteE G root
  letI : Fintype E := Fintype.ofFinite E
  letI : DecidableEq E := Classical.decEq E
  letI (F : Finset E) : Decidable (G.IsSpanningTree F) :=
    Classical.propDecidable _
  let B := G.kirchhoffReducedIncidence root
  calc
    (G.spanningTreeCount : ℤ) =
        ∑ F ∈ Finset.univ.powersetCard
            (Fintype.card (Multigraph.LabeledMultigraph.AwayFrom root)),
          if G.IsSpanningTree F then (1 : ℤ) else 0 :=
      (G.sum_spanningTreeIndicators_eq_count root).symm
    _ = ∑ F ∈ Finset.univ.powersetCard
            (Fintype.card (Multigraph.LabeledMultigraph.AwayFrom root)),
          GramCauchyBinet.maximalMinor B F ^ 2 := by
      apply Finset.sum_congr rfl
      intro F hF
      symm
      apply G.maximalMinor_kirchhoffReducedIncidence_sq root F
      exact (Finset.mem_powersetCard.mp hF).2
    _ = Matrix.det (B * Bᵀ) :=
      (GramCauchyBinet.det_gram_eq_sum_sq_maximalMinors B).symm
    _ = Matrix.det (G.reducedLaplacian ℤ root) := by
      rw [G.kirchhoffReducedIncidence_mul_transpose]

end SquareMaximality
