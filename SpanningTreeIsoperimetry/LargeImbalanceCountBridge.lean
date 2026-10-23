module

public import SpanningTreeIsoperimetry.CrossHullCountComparison
public import SpanningTreeIsoperimetry.SourceHullArithmetic
public import SpanningTreeIsoperimetry.LargeImbalanceTest

@[expose] public section

/-! Actual T≥4 count exclusion once the rectangular remainder absorption is
supplied. The remaining analytic input is explicit and is not counted here
as a proved final exclusion theorem. -/
namespace SpanningTreeIsoperimetry.LargeImbalanceCountBridge
open Ferrers CornerEnergy CornerPrimalDomains SquareMaximality.Boundary
open CrossHullCountComparison SourceHullArithmetic RectangularRemainder AspectCost
open LargeImbalanceGeometry CanonicalRectangleBounds RefinedCornerEnvelope
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem offset_of_sides {r s t e : ℕ} (hr : 0<r) (hs : s=r+2*t+e) :
    aspectOffset r s=(2*(t : ℝ)+e)/r := by
  have hr0 : (r : ℝ)≠0 := by exact_mod_cast hr.ne'
  unfold aspectOffset
  rw [hs]
  push_cast
  field_simp [hr0] <;> ring

theorem count_lt_canonical_of_absorption {N t : ℕ} (hN : 0<N)
    (hT : 4≤canonicalIndex N) (ht : t<canonicalIndex N)
    (M : Corner → Diagram) (hM : ∀ c, IsFerrers (M c))
    (hcard : totalDefect M=(sourceParameters N t).2.2)
    (hnot : ¬CornerConcentration.IsConcentrated Finset.univ M)
    (habsorb : error (sourceParameters N t).1 (sourceParameters N t).2.1-
      error (canonicalParameters N).1 (canonicalParameters N).2.1 ≤
      ((totalDefect M : ℝ)-(canonicalParameters N).2.2)*
        correction (faceRectangle ((sourceParameters N t).1-1) ((sourceParameters N t).2.1-1)) {(0,0)}) :
    treeCount (cornerPrimal ((sourceParameters N t).1-1) ((sourceParameters N t).2.1-1) M)<
      treeCount (canonicalDomain N) := by
  let L := minimumSideSum N
  let m := L/2
  let e := L%2
  let d := m*(m+e)-N
  let T := canonicalIndex N
  let r := (sourceParameters N t).1
  let s := (sourceParameters N t).2.1
  let k := (sourceParameters N t).2.2
  let R := (canonicalParameters N).1
  let S := (canonicalParameters N).2.1
  let j := (canonicalParameters N).2.2
  change 4≤T at hT
  change t<T at ht
  change totalDefect M=k at hcard
  change error r s-error R S≤((totalDefect M : ℝ)-j)*
    correction (faceRectangle (r-1) (s-1)) {(0,0)} at habsorb
  change treeCount (cornerPrimal (r-1) (s-1) M)<treeCount (cornerStrip R S j)
  have hf := source_hull_facts hN ht.le
  have hr0 : 0<r := hf.short_pos
  have hrs : r≤s := hf.ordered
  have hsrcArea : r*s=N+k := hf.area
  have hsrcSum : r+s=L := hf.side_sum
  have hkshort : k<r := hf.deficit_lt_short
  have hRr : R≤r := hf.canonical_short_le
  have hsS : s≤S := hf.long_le_canonical
  have hsrcSide : s=r+2*t+e := hf.side_difference
  have hc := selected_hull_properties_of_ceil hN
  change 0<R ∧ R≤S ∧ R+S=L ∧ R*S=N+j ∧ j<R at hc
  have hsize := canonical_size_relation hN
  change T^2-T+T*e+j+1≤R at hsize
  have hmul := Nat.mul_le_mul hT (show 3≤T-1 by omega)
  have heq : T*(T-1)=T^2-T := by rw [Nat.mul_sub_left_distrib,pow_two]; simp
  rw [heq] at hmul
  have hR3 : 3≤R := by omega
  have htarSide : S=R+2*T+e := by
    have hh := (source_hull_facts hN (t := T) (le_refl T)).side_difference
    simpa only [T,source_at_canonical] using hh
  have hkstep := source_deficit_lower (selectorIndex_bounds d e).1 ht
  change 2*T+e-1+j≤k at hkstep
  have hk2 : 2≤totalDefect M := by omega
  have hcost := LargeImbalanceTest.actual_selector_test hN hT ht
  change realEnergy (horizontalStrip j)+D ((2*(T : ℝ)+e)/R)-D ((2*(t : ℝ)+e)/r)+
    FluxBounds.fluxBound R S j < bound k at hcost
  have hDsrc := offset_of_sides hr0 hsrcSide
  have hDtgt := offset_of_sides hc.1 htarSide
  have hfamily := RefinedCornerEnvelope.family_bound Finset.univ M
    (fun c _ => hM c) hk2 hnot
  change bound (totalDefect M)<∑ c,realEnergy (M c) at hfamily
  rw [hcard] at hfamily
  apply count_lt_of_normalized_cost hR3 hRr hrs hsS M hM
    (show totalDefect M≤r-1 by omega) (show totalDefect M≤s-1 by omega)
    (show j+1<S by omega) (show r*s+j=R*S+totalDefect M by omega)
    (show r+s=R+S by omega) habsorb
  rw [hDtgt,hDsrc]
  exact hcost.trans hfamily

end
end SpanningTreeIsoperimetry.LargeImbalanceCountBridge
