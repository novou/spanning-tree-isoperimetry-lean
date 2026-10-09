import SpanningTreeIsoperimetry.InteriorCost
import SpanningTreeIsoperimetry.ComparisonDomain
import SpanningTreeIsoperimetry.IsoperimetryArithmetic
import SpanningTreeIsoperimetry.RectangularComparison
import SpanningTreeIsoperimetry.GapConvexity
import SpanningTreeIsoperimetry.Targets
import SpanningTreeIsoperimetry.MaximizerGeometry
import SpanningTreeIsoperimetry.BoundaryGap

/-! Integer defect elimination for actual spanning-tree maximizers.
Every quantitative comparison used below is supplied by a proved component. -/
namespace SpanningTreeIsoperimetry

open SquareMaximality.Boundary

theorem normalized_maximizer_defects {A : Domain} {R S : ℕ}
    (hmax : IsMaximizer A)
    (hHull : SquareMaximality.IsRectHull A 0 0 (R+1) (S+1)) :
    (R+1)+(S+1)=minimumSideSum A.card ∧
      EnhancedBoundary.boundaryGapCount R S A=0 ∧ canonicalInteriorCount R S A=0 := by
  let n := Nat.sqrt A.card
  let q := A.card-n^2
  let j := ComparisonDomain.leafSeeds n q
  let beta := (R+1)+(S+1)-minimumSideSum A.card
  have hN : 0<A.card := hHull.card_pos
  obtain ⟨hn,hEq,hq⟩ := square_remainder_data hN
  change 0<n at hn
  change A.card=n^2+q at hEq
  change q≤2*n at hq
  have hj : j≤2 := by unfold j ComparisonDomain.leafSeeds; split_ifs <;> omega
  have hL : minimumSideSum A.card=2*n+j := by
    rw [minimumSideSum,hEq]
    exact ceil_sqrt_square_remainder hn hq
  have harea : A.card≤(R+1)*(S+1) := by
    simpa only [SquareMaximality.rectangle_card] using Finset.card_le_card hHull.2.2.1
  have hsideLower : minimumSideSum A.card≤(R+1)+(S+1) :=
    minimum_side_sum_le (ceil_sqrt_is_minimum_side_sum hN) harea
  have hbeta : beta+minimumSideSum A.card=(R+1)+(S+1) := Nat.sub_add_cancel hsideLower
  have hside : ((R+1 : ℕ) : ℝ)+(S+1 : ℕ)=(beta : ℝ)+2*n+j := by
    exact_mod_cast (show (R+1)+(S+1)=beta+2*n+j by omega)
  let B := ComparisonDomain.comparisonDomain n q
  have hBcard : B.card=A.card := by
    change (ComparisonDomain.comparisonDomain n q).card=A.card
    rw [ComparisonDomain.comparisonDomain_card]
    exact hEq.symm
  have hBconn : (domainGraph B).Connected := by
    rw [domainGraph_eq_foundation]
    exact ComparisonDomain.comparisonDomain_connected hn q
  have hBpos : (0 : ℝ)<SquareMaximality.tau B := by
    rw [← treeCount_eq_foundation]
    exact_mod_cast (treeCount_pos_iff_connected B).mpr hBconn
  have hcount : (SquareMaximality.tau B : ℝ)≤SquareMaximality.tau A := by
    have h := hmax.2 B hBcard hBconn
    rw [treeCount_eq_foundation,treeCount_eq_foundation] at h
    exact_mod_cast h
  have hlog := Real.log_le_log hBpos hcount
  have hgain := ComparisonDomain.comparisonDomain_log_gain hn hq
  change Real.log (SquareMaximality.tauRect n n : ℝ)+
    SquareMaximality.squareLatticeEntropy*((q : ℝ)-j)≤Real.log (SquareMaximality.tau B : ℝ) at hgain
  have hrect := RectangularComparison.rectangular_comparison hn
    (by omega : 0<R+1) (by omega : 0<S+1) (by omega : n^2≤(R+1)*(S+1))
  rw [rectangle_treeCount_eq_foundation,rectangle_treeCount_eq_foundation,
    entropy_eq_foundation] at hrect
  have hcost := InteriorCost.enhanced_hull_bound_all hHull
    (by simpa only [← domainGraph_eq_foundation] using hmax.1)
  rw [Nat.cast_sub harea] at hcost
  push_cast at hcost hrect hside
  have hEqR : (A.card : ℝ)=(n : ℝ)^2+q := by exact_mod_cast hEq
  rw [hEqR] at hcost
  rw [hside] at hrect
  have hbudget : Real.log (1+Real.sqrt 2)*((beta : ℝ)+EnhancedBoundary.boundaryGapCount R S A)+
      (3 : ℝ)/5*canonicalInteriorCount R S A ≤
      (j : ℝ)*(SquareMaximality.squareLatticeEntropy-Real.log (1+Real.sqrt 2)) := by
    nlinarith only [hlog,hgain,hcost,hrect]
  have hconstants := LocalBounds.strict_constants
  rw [entropy_eq_foundation] at hconstants
  have hzero := integer_defects_vanish (β := beta)
    (g := EnhancedBoundary.boundaryGapCount R S A) (c := canonicalInteriorCount R S A)
    (j := j) (by norm_num : (0 : ℝ)<3/5) hconstants.2.le hconstants.1 hj hbudget
  exact ⟨by omega,hzero.2.1,hzero.2.2⟩

theorem normalized_maximizer_convex {A : Domain} {R S : ℕ}
    (hmax : IsMaximizer A)
    (hHull : SquareMaximality.IsRectHull A 0 0 (R+1) (S+1)) :
    IsRowConvex A ∧ IsColumnConvex A ∧ (R+1)+(S+1)=minimumSideSum A.card := by
  have hd := normalized_maximizer_defects hmax hHull
  have hsub : A ⊆ rectangle (R+1) (S+1) := by
    simpa only [rectangle_eq_foundation] using hHull.2.2.1
  have hc := convex_of_zero_vacancy_defects hsub hd.2.1 hd.2.2
  exact ⟨hc.1,hc.2,hd.1⟩

/-- A maximizer has interval rows and columns and a minimal hull side sum,
at any translated location in the integer lattice. -/
theorem maximizer_hull_shape {A : Domain} {a b : ℤ} {r s : ℕ}
    (hmax : IsMaximizer A) (hHull : SquareMaximality.IsRectHull A a b r s) :
    IsRowConvex A ∧ IsColumnConvex A ∧ r+s=minimumSideSum A.card := by
  obtain ⟨R,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hHull.1)
  obtain ⟨S,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hHull.2.1)
  have ht := normalized_maximizer_convex
    (MaximizerGeometry.isMaximizer_translateFinset hmax (-a) (-b)) hHull.translate_to_origin
  refine ⟨(MaximizerGeometry.rowConvex_translateFinset_iff (-a) (-b) A).mp ht.1,
    (MaximizerGeometry.columnConvex_translateFinset_iff (-a) (-b) A).mp ht.2.1,?_⟩
  simpa only [MaximizerGeometry.translateFinset_card] using ht.2.2

/-- Every spanning-tree maximizer is edge-isoperimetric, for every positive
cardinality. This is the headline isoperimetry conclusion in the current
graph/count model. -/
theorem maximizer_isoperimetric {A : Domain} (hmax : IsMaximizer A) :
    edgeCount A=2*A.card-minimumSideSum A.card := by
  obtain ⟨a,b,r,s,hHull⟩ := SquareMaximality.exists_isRectHull_of_nonempty A
    (connected_domain_nonempty hmax.1)
  obtain ⟨hrow,hcol,hsum⟩ := maximizer_hull_shape hmax hHull
  exact MaximizerGeometry.edgeCount_eq_of_minimum_hull hmax.1 hHull hrow hcol hsum

theorem isoperimetryTarget : IsoperimetryTarget := by
  intro A hmax
  exact maximizer_isoperimetric hmax

theorem maximizer_deficit_lt_min_side {A : Domain} {a b : ℤ} {r s : ℕ}
    (hmax : IsMaximizer A) (hHull : SquareMaximality.IsRectHull A a b r s) :
    r*s-A.card < min r s := by
  have harea : A.card≤r*s := by
    simpa only [SquareMaximality.rectangle_card] using Finset.card_le_card hHull.2.2.1
  exact deficit_lt_min_side_of_ceil_sqrt hHull.card_pos hHull.1 hHull.2.1 harea
    (maximizer_hull_shape hmax hHull).2.2

/-- A maximizing domain has no finite nearest-neighbor vacancy component. -/
theorem maximizer_vacancy_component_infinite {A : Domain} (hmax : IsMaximizer A)
    (p : {v : Vertex // v ∉ A}) :
    ((vacancyGraph A).connectedComponentMk p).supp.Infinite := by
  obtain ⟨a,b,r,s,hHull⟩ := SquareMaximality.exists_isRectHull_of_nonempty A
    (connected_domain_nonempty hmax.1)
  exact vacancy_component_infinite (maximizer_hull_shape hmax hHull).1 p

/-- On a normalized minimal hull, the vacancies of a maximizer are the
actual four disjoint corner Ferrers diagrams constructed in `FourCorners`. -/
theorem maximizer_four_corner_partition {A : Domain} {r s : ℕ}
    (hmax : IsMaximizer A) (hHull : IsStandardHull A r s) (p : Vertex) :
    (∀ bx byFlag, IsFerrers (cornerDiagram A r s bx byFlag)) ∧
    (p ∈ rectangle r s \ A ↔ ∃! c : Bool × Bool,
      p ∈ (cornerDiagram A r s c.1 c.2).image (cornerEmbedding r s c.1 c.2)) := by
  have hc := maximizer_hull_shape hmax (standardHull_to_foundation hHull)
  exact four_corner_ferrers_partition hHull hmax.1 hc.1 hc.2.1 p

end SpanningTreeIsoperimetry
