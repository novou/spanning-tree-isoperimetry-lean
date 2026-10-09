import SquareMaximality.Dual.Components
import SquareMaximality.Multigraph.ContractionTrees
import SquareMaximality.Boundary.Assembly

/-!
# Canonical forest events and the component product

This module isolates the genuinely planar event identifications from the
finite probability algebra.  Given forest blocks whose containment ratios are
the required deletion ratios, transfer-current negative correlation implies
the manuscript's component-product inequality.  The empty interior-family
case is handled by the already proved zero-block theorem.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Dual

open Multigraph

/-- Exact forest-event data for the canonical boundary/interior decomposition.
The equality fields are the remaining planar matroid-duality bridge. -/
structure CanonicalForestEvents (A : Finset Point) (R S : ℕ) where
  block : Option (Fin (Boundary.canonicalInteriorCount R S A)) →
    Finset (RectangleEdge (R + 1) (S + 1))
  block_subset : ∀ i, block i ⊆ canonicalDualEdgeBlock R S A i
  unionForest : (rectangleDual (R + 1) (S + 1)).IsEdgeForest
    (Multigraph.LabeledMultigraph.unionEdgeBlocks block)
  ambientPositive : 0 < (rectangleDual (R + 1) (S + 1)).spanningTreeCount
  wholeEvent :
    (rectangleDual (R + 1) (S + 1)).containmentRatio
        (Multigraph.LabeledMultigraph.unionEdgeBlocks block) =
      (tau A : ℝ) / (tauRect (R + 1) (S + 1) : ℝ)
  boundaryEvent :
    (rectangleDual (R + 1) (S + 1)).containmentRatio (block none) =
      (tau (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A) : ℝ) /
      (tauRect (R + 1) (S + 1) : ℝ)
  interiorEvent : ∀ i,
    (rectangleDual (R + 1) (S + 1)).containmentRatio (block (some i)) =
      (tau (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i) : ℝ) /
      (tauRect (R + 1) (S + 1) : ℝ)

namespace CanonicalForestEvents

variable {A : Finset Point} {R S : ℕ}

theorem block_pairwiseDisjoint (d : CanonicalForestEvents A R S) :
    Pairwise fun i j => Disjoint (d.block i) (d.block j) := by
  intro i j hij
  exact (canonicalDualEdgeBlock_pairwiseDisjoint R S A hij).mono
    (d.block_subset i) (d.block_subset j)

theorem block_subset_union (d : CanonicalForestEvents A R S) (i) :
    d.block i ⊆ Multigraph.LabeledMultigraph.unionEdgeBlocks d.block := by
  intro e he
  exact Multigraph.LabeledMultigraph.mem_unionEdgeBlocks.mpr ⟨i, he⟩

theorem blockForest (d : CanonicalForestEvents A R S) (i) :
    (rectangleDual (R + 1) (S + 1)).IsEdgeForest (d.block i) :=
  (rectangleDual (R + 1) (S + 1)).isEdgeForest_mono
    d.unionForest (d.block_subset_union i)

/-- Negative correlation gives the componentwise product of deletion ratios. -/
theorem ratio_component_product
    (d : CanonicalForestEvents A R S)
    (hneg : (rectangleDual (R + 1) (S + 1)).ForestBlockNegativeCorrelation) :
    (tau A : ℝ) / (tauRect (R + 1) (S + 1) : ℝ) ≤
      ((tau (rectangle 0 0 (R + 1) (S + 1) \
          Boundary.canonicalBoundary R S A) : ℝ) /
        (tauRect (R + 1) (S + 1) : ℝ)) *
      ∏ i, ((tau (rectangle 0 0 (R + 1) (S + 1) \
          Boundary.canonicalInterior R S A i) : ℝ) /
        (tauRect (R + 1) (S + 1) : ℝ)) := by
  have h := (rectangleDual (R + 1) (S + 1)).forestBlockNegativeCorrelation_all
    d.ambientPositive hneg d.block d.block_pairwiseDisjoint d.unionForest
  rw [Fintype.prod_option] at h
  rw [d.wholeEvent, d.boundaryEvent] at h
  simpa only [d.interiorEvent] using h

private theorem nat_pos_of_ratio_pos {a b : ℕ} (h : 0 < (a : ℝ) / (b : ℝ)) :
    0 < a := by
  by_contra ha
  have ha0 : a = 0 := by omega
  simp [ha0] at h

theorem boundaryTau_pos (d : CanonicalForestEvents A R S) :
    0 < tau (rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalBoundary R S A) := by
  apply nat_pos_of_ratio_pos
  rw [← d.boundaryEvent]
  exact (rectangleDual (R + 1) (S + 1)).containmentRatio_pos_of_isEdgeForest
    d.ambientPositive (d.blockForest none)

theorem interiorTau_pos (d : CanonicalForestEvents A R S) (i) :
    0 < tau (rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalInterior R S A i) := by
  apply nat_pos_of_ratio_pos
  rw [← d.interiorEvent i]
  exact (rectangleDual (R + 1) (S + 1)).containmentRatio_pos_of_isEdgeForest
    d.ambientPositive (d.blockForest (some i))

/-- Additive logarithmic form used by `CanonicalFactorEstimates`. -/
theorem log_component_product
    (d : CanonicalForestEvents A R S)
    (hconn : (inducedGrid A).Connected)
    (hneg : (rectangleDual (R + 1) (S + 1)).ForestBlockNegativeCorrelation) :
    Real.log (tau A : ℝ) - Real.log (tauRect (R + 1) (S + 1) : ℝ) ≤
      (Real.log (tau (rectangle 0 0 (R + 1) (S + 1) \
          Boundary.canonicalBoundary R S A) : ℝ) -
        Real.log (tauRect (R + 1) (S + 1) : ℝ)) +
      ∑ i, (Real.log (tau (rectangle 0 0 (R + 1) (S + 1) \
          Boundary.canonicalInterior R S A i) : ℝ) -
        Real.log (tauRect (R + 1) (S + 1) : ℝ)) := by
  apply Boundary.log_component_product_of_ratio
  · exact (tau_pos_iff_connected A).mpr hconn
  · exact tauRect_pos (by omega) (by omega)
  · exact d.boundaryTau_pos
  · exact d.interiorTau_pos
  · exact d.ratio_component_product hneg

end CanonicalForestEvents

/-- The two per-component exponential estimates, separated from the forest
event product. -/
structure CanonicalFactorBounds (κ : ℝ) (A : Finset Point) (R S : ℕ) : Prop where
  boundary :
    Real.log (tau (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A) : ℝ) -
      Real.log (tauRect (R + 1) (S + 1) : ℝ) ≤
        -κ * (Boundary.canonicalBoundary R S A).card
  interior : ∀ i,
    Real.log (tau (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i) : ℝ) -
      Real.log (tauRect (R + 1) (S + 1) : ℝ) ≤
        -κ * (Boundary.canonicalInterior R S A i).card

/-- Forest events plus the two factor estimates construct all canonical hull
factor data. -/
theorem canonicalFactorEstimates_of_forestEvents
    {κ : ℝ} {A : Finset Point} {R S : ℕ}
    (hconn : (inducedGrid A).Connected)
    (d : CanonicalForestEvents A R S)
    (hneg : (rectangleDual (R + 1) (S + 1)).ForestBlockNegativeCorrelation)
    (b : CanonicalFactorBounds κ A R S) :
    Boundary.CanonicalFactorEstimates κ A R S where
  componentProduct := d.log_component_product hconn hneg
  boundaryFactor := b.boundary
  interiorFactor := b.interior

end Dual
end SquareMaximality
