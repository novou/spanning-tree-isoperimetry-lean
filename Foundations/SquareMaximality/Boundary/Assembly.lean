module

public import SquareMaximality.Boundary.Degenerate
public import SquareMaximality.Penalties

@[expose] public section

set_option autoImplicit false

/-!
# Assembly of boundary and interior vacancy factors

This file refines the single `NormalizedHullPenalty` input into the precise
component-level obligations used by `general.tex`.  The finite partition,
empty-family endpoint, summation, and cancellation are proved here.  What
remains for later modules is to construct this data using planar duality,
negative correlation, Tapp's bound, and the boundary determinant estimate.
-/

namespace SquareMaximality

namespace Boundary

/-- Taking logarithms turns the component-product probability estimate into
the additive inequality used by `HullFactorData`.  Positivity is explicit, so
no zero-count case is hidden in the logarithm step. -/
theorem log_component_product_of_ratio
    {m a b c : ℕ} {f : Fin m → ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hf : ∀ i, 0 < f i)
    (hprod : (a : ℝ) / (b : ℝ) ≤
      ((c : ℝ) / (b : ℝ)) * ∏ i, ((f i : ℝ) / (b : ℝ))) :
    Real.log (a : ℝ) - Real.log (b : ℝ) ≤
      (Real.log (c : ℝ) - Real.log (b : ℝ)) +
        ∑ i, (Real.log (f i : ℝ) - Real.log (b : ℝ)) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hfR : ∀ i, (0 : ℝ) < f i := fun i => by exact_mod_cast hf i
  have hleft : 0 < (a : ℝ) / (b : ℝ) := div_pos haR hbR
  have hfactor : 0 < (c : ℝ) / (b : ℝ) := div_pos hcR hbR
  have hfamily : 0 < ∏ i, ((f i : ℝ) / (b : ℝ)) := by
    exact Finset.prod_pos fun i _ => div_pos (hfR i) hbR
  have hright : 0 < ((c : ℝ) / (b : ℝ)) *
      ∏ i, ((f i : ℝ) / (b : ℝ)) := mul_pos hfactor hfamily
  have hlog := Real.strictMonoOn_log.monotoneOn
    (show (a : ℝ) / (b : ℝ) ∈ Set.Ioi 0 from hleft)
    (show ((c : ℝ) / (b : ℝ)) * ∏ i, ((f i : ℝ) / (b : ℝ)) ∈ Set.Ioi 0
      from hright) hprod
  rw [Real.log_div (ne_of_gt haR) (ne_of_gt hbR),
    Real.log_mul (ne_of_gt hfactor) (ne_of_gt hfamily),
    Real.log_div (ne_of_gt hcR) (ne_of_gt hbR),
    Real.log_prod] at hlog
  · simpa only [Finset.sum_const_zero, Finset.sum_sub_distrib,
      Real.log_div (ne_of_gt (hfR _)) (ne_of_gt hbR)] using hlog
  · intro i _
    exact ne_of_gt (div_pos (hfR i) hbR)

/-- Exponential factor bounds imply their additive logarithmic form. -/
theorem log_factor_of_ratio_le_exp
    {a b n : ℕ} {κ : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hfactor : (a : ℝ) / (b : ℝ) ≤ Real.exp (-κ * (n : ℝ))) :
    Real.log (a : ℝ) - Real.log (b : ℝ) ≤ -κ * (n : ℝ) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hratio : 0 < (a : ℝ) / (b : ℝ) := div_pos haR hbR
  have hexp : 0 < Real.exp (-κ * (n : ℝ)) := Real.exp_pos _
  have hlog := Real.strictMonoOn_log.monotoneOn
    (show (a : ℝ) / (b : ℝ) ∈ Set.Ioi 0 from hratio)
    (show Real.exp (-κ * (n : ℝ)) ∈ Set.Ioi 0 from hexp) hfactor
  rw [Real.log_div (ne_of_gt haR) (ne_of_gt hbR), Real.log_exp] at hlog
  exact hlog

/-- A component decomposition together with the three logarithmic estimates
that occur in the normalized-hull proof. -/
structure HullFactorData (κ : ℝ) (S : Finset Point) (r s : ℕ) where
  componentCount : ℕ
  boundary : Finset Point
  interior : Fin componentCount → Finset Point
  partition :
    rectangle 0 0 r s \ S =
      boundary ∪ Finset.univ.biUnion interior
  boundary_disjoint :
    Disjoint boundary (Finset.univ.biUnion interior)
  interior_pairwise :
    ((Finset.univ : Finset (Fin componentCount)) : Set (Fin componentCount)).PairwiseDisjoint
      interior
  componentProduct :
    Real.log (tau S : ℝ) - Real.log (tauRect r s : ℝ) ≤
      (Real.log (tau (rectangle 0 0 r s \ boundary) : ℝ) -
        Real.log (tauRect r s : ℝ)) +
      ∑ i, (Real.log (tau (rectangle 0 0 r s \ interior i) : ℝ) -
        Real.log (tauRect r s : ℝ))
  boundaryFactor :
    Real.log (tau (rectangle 0 0 r s \ boundary) : ℝ) -
        Real.log (tauRect r s : ℝ) ≤
      -κ * (boundary.card : ℝ)
  interiorFactor : ∀ i,
    Real.log (tau (rectangle 0 0 r s \ interior i) : ℝ) -
        Real.log (tauRect r s : ℝ) ≤
      -κ * ((interior i).card : ℝ)

namespace HullFactorData

variable {κ : ℝ} {S : Finset Point} {r s : ℕ}

/-- The component hypotheses imply the exact vacancy-cardinality partition,
including the case of zero interior components. -/
theorem vacancy_card (d : HullFactorData κ S r s) :
    (rectangle 0 0 r s \ S).card =
      d.boundary.card + ∑ i, (d.interior i).card := by
  rw [d.partition, Finset.card_union_of_disjoint d.boundary_disjoint,
    Finset.card_biUnion d.interior_pairwise]

/-- Boundary and interior exponential factors assemble to the normalized hull
inequality. -/
theorem normalizedHullBound (d : HullFactorData κ S r s) :
    Real.log (tau S : ℝ) - Real.log (tauRect r s : ℝ) ≤
      -κ * ((rectangle 0 0 r s \ S).card : ℝ) := by
  calc
    Real.log (tau S : ℝ) - Real.log (tauRect r s : ℝ) ≤
        (Real.log (tau (rectangle 0 0 r s \ d.boundary) : ℝ) -
          Real.log (tauRect r s : ℝ)) +
        ∑ i, (Real.log (tau (rectangle 0 0 r s \ d.interior i) : ℝ) -
          Real.log (tauRect r s : ℝ)) := d.componentProduct
    _ ≤ -κ * (d.boundary.card : ℝ) +
        ∑ i, (-κ * ((d.interior i).card : ℝ)) := by
      exact add_le_add d.boundaryFactor (Finset.sum_le_sum fun i _ => d.interiorFactor i)
    _ = -κ * ((rectangle 0 0 r s \ S).card : ℝ) := by
      rw [d.vacancy_card]
      push_cast
      rw [← Finset.mul_sum]
      ring

end HullFactorData

/-- The remaining component-level target for every nondegenerate normalized
hull.  This is substantially narrower than assuming `NormalizedHullPenalty`
itself. -/
def ComponentwiseHullInputs (κ : ℝ) : Prop :=
  ∀ ⦃S : Finset Point⦄ ⦃r s : ℕ⦄,
    (inducedGrid S).Connected → IsRectHull S 0 0 r s →
    2 ≤ r → 2 ≤ s → Nonempty (HullFactorData κ S r s)

/-- Component-level inputs, together with the proved one-row/one-column
branches, establish the complete normalized hull predicate. -/
theorem normalizedHullPenalty_of_componentwise
    {κ : ℝ} (h : ComponentwiseHullInputs κ) :
    NormalizedHullPenalty κ := by
  intro S r s hconn hHull
  by_cases hr : r = 1
  · subst r
    exact normalizedHull_bound_of_width_one κ hHull hconn
  by_cases hs : s = 1
  · subst s
    exact normalizedHull_bound_of_height_one κ hHull hconn
  have hrpos : 0 < r := hHull.1
  have hspos : 0 < s := hHull.2.1
  have hr2 : 2 ≤ r := by omega
  have hs2 : 2 ≤ s := by omega
  rcases h hconn hHull hr2 hs2 with ⟨d⟩
  exact d.normalizedHullBound

end Boundary

end SquareMaximality
