module

public import SquareMaximality.Dual.ForestProduct
public import SquareMaximality.Multigraph.Incompatible

@[expose] public section

set_option backward.privateInPublic true

/-!
# Interior-component factor from incompatible forest events

The interior-vacancy argument needs only two facts about the collection of
spanning trees of the dual component: their containment events are pairwise
incompatible, and there are exponentially many of them.  This file proves
the complete probability and logarithm reduction from an explicit finite
certificate carrying exactly those facts.  Planar duality and Tapp's lower
bound remain upstream of the certificate.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Dual

open Multigraph

/-- Finite event certificate for one canonical interior vacancy component.
`eventCount` is intended to be the spanning-tree count of its dual
face-star graph. -/
structure CanonicalInteriorEventCertificate
    (κ : ℝ) (A : Finset Point) (R S : ℕ)
    (i : Fin (Boundary.canonicalInteriorCount R S A)) : Type where
  eventCount : ℕ
  block : Fin eventCount → Finset (RectangleEdge (R + 1) (S + 1))
  ambientPositive :
    0 < (rectangleDual (R + 1) (S + 1)).spanningTreeCount
  blockForest : ∀ j,
    (rectangleDual (R + 1) (S + 1)).IsEdgeForest (block j)
  incompatible :
    (rectangleDual (R + 1) (S + 1)).PairwiseIncompatible block
  eventRatio : ∀ j,
    (rectangleDual (R + 1) (S + 1)).containmentRatio (block j) =
      (tau (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i) : ℝ) /
      (tauRect (R + 1) (S + 1) : ℝ)
  exponentialMultiplicity :
    Real.exp (κ * (Boundary.canonicalInterior R S A i).card) ≤ eventCount

namespace CanonicalInteriorEventCertificate

variable {κ : ℝ} {A : Finset Point} {R S : ℕ}
variable {i : Fin (Boundary.canonicalInteriorCount R S A)}

private theorem eventCount_pos
    (d : CanonicalInteriorEventCertificate κ A R S i) : 0 < d.eventCount := by
  have hpos : 0 < Real.exp (κ * (Boundary.canonicalInterior R S A i).card) :=
    Real.exp_pos _
  have hcast : (0 : ℝ) < d.eventCount := hpos.trans_le d.exponentialMultiplicity
  exact_mod_cast hcast

private theorem deletionTau_pos
    (d : CanonicalInteriorEventCertificate κ A R S i) :
    0 < tau (rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalInterior R S A i) := by
  let j : Fin d.eventCount := ⟨0, d.eventCount_pos⟩
  have hratio :=
    (rectangleDual (R + 1) (S + 1)).containmentRatio_pos_of_isEdgeForest
      d.ambientPositive (d.blockForest j)
  rw [d.eventRatio j] at hratio
  by_contra hzero
  have heq : tau (rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalInterior R S A i) = 0 := by omega
  simp [heq] at hratio

/-- Incompatibility and exponential multiplicity give the desired
exponential probability bound. -/
theorem ratio_le_exp_neg
    (d : CanonicalInteriorEventCertificate κ A R S i) :
    (tau (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i) : ℝ) /
      (tauRect (R + 1) (S + 1) : ℝ) ≤
        Real.exp (-κ * (Boundary.canonicalInterior R S A i).card) := by
  let q : ℝ :=
    (tau (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i) : ℝ) /
      (tauRect (R + 1) (S + 1) : ℝ)
  have hsum := (rectangleDual (R + 1) (S + 1)).sum_containmentRatio_le_one
    d.ambientPositive d.incompatible
  have hsum' : (d.eventCount : ℝ) * q ≤ 1 := by
    calc
      (d.eventCount : ℝ) * q = ∑ _j : Fin d.eventCount, q := by simp
      _ = ∑ j, (rectangleDual (R + 1) (S + 1)).containmentRatio
          (d.block j) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (d.eventRatio j).symm
      _ ≤ 1 := hsum
  have hq : 0 ≤ q := by
    dsimp only [q]
    positivity
  have hmul : Real.exp
      (κ * (Boundary.canonicalInterior R S A i).card) * q ≤ 1 :=
    (mul_le_mul_of_nonneg_right d.exponentialMultiplicity hq).trans hsum'
  have hexp : 0 < Real.exp
      (κ * (Boundary.canonicalInterior R S A i).card) := Real.exp_pos _
  have hinv : q ≤ 1 / Real.exp
      (κ * (Boundary.canonicalInterior R S A i).card) := by
    rw [le_div_iff₀ hexp]
    simpa only [one_mul, mul_comm] using hmul
  change q ≤ Real.exp (-κ * (Boundary.canonicalInterior R S A i).card)
  simpa only [Real.exp_neg, neg_mul, one_div] using hinv

/-- Logarithmic form used by `CanonicalFactorBounds`. -/
theorem log_factor
    (d : CanonicalInteriorEventCertificate κ A R S i) :
    Real.log (tau (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalInterior R S A i) : ℝ) -
      Real.log (tauRect (R + 1) (S + 1) : ℝ) ≤
        -κ * (Boundary.canonicalInterior R S A i).card := by
  exact Boundary.log_factor_of_ratio_le_exp d.deletionTau_pos
    (tauRect_pos (by omega) (by omega)) d.ratio_le_exp_neg

end CanonicalInteriorEventCertificate

/-- A boundary factor together with one explicit event certificate per
interior component constructs all per-component factor bounds. -/
theorem canonicalFactorBounds_of_interiorEvents
    {κ : ℝ} {A : Finset Point} {R S : ℕ}
    (hboundary :
      Real.log (tau (rectangle 0 0 (R + 1) (S + 1) \
          Boundary.canonicalBoundary R S A) : ℝ) -
        Real.log (tauRect (R + 1) (S + 1) : ℝ) ≤
          -κ * (Boundary.canonicalBoundary R S A).card)
    (d : ∀ i, CanonicalInteriorEventCertificate κ A R S i) :
    CanonicalFactorBounds κ A R S where
  boundary := hboundary
  interior i := (d i).log_factor

end Dual
end SquareMaximality
