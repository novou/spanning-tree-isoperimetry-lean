import SpanningTreeIsoperimetry.Isoperimetry

/-! The full quantitative integer-rigidity comparison for arbitrary connected
lattice domains. This does not assume that the source is a maximizer. -/
namespace SpanningTreeIsoperimetry.IntegerRigidityComparison
open SquareMaximality.Boundary
open scoped Classical
noncomputable section

/-- The explicit comparison domain B_N used in Section 3. -/
def comparisonDomain (N : ℕ) : Domain :=
  ComparisonDomain.comparisonDomain (Nat.sqrt N) (N-(Nat.sqrt N)^2)

def leafSeeds (N : ℕ) : ℕ :=
  ComparisonDomain.leafSeeds (Nat.sqrt N) (N-(Nat.sqrt N)^2)

theorem comparisonDomain_card {N : ℕ} (hN : 0<N) : (comparisonDomain N).card=N := by
  obtain ⟨_,hEq,_⟩ := square_remainder_data hN
  rw [comparisonDomain,ComparisonDomain.comparisonDomain_card]
  exact hEq.symm

theorem comparisonDomain_connected {N : ℕ} (hN : 0<N) :
    (domainGraph (comparisonDomain N)).Connected := by
  obtain ⟨hn,_,_⟩ := square_remainder_data hN
  rw [domainGraph_eq_foundation]
  exact ComparisonDomain.comparisonDomain_connected hn _

/-- The entire quantitative inequality, before imposing maximality. The
boundary gap and interior count are the actual canonical vacancy counts. -/
theorem normalized_integer_rigidity {A : Domain} {R S : ℕ}
    (hconn : (domainGraph A).Connected)
    (hHull : SquareMaximality.IsRectHull A 0 0 (R+1) (S+1)) :
    Real.log (1+Real.sqrt 2)*
        (((R+1)+(S+1)-minimumSideSum A.card : ℕ)+
          (EnhancedBoundary.boundaryGapCount R S A : ℝ))+
      (3 : ℝ)/5*canonicalInteriorCount R S A-
        (leafSeeds A.card : ℝ)*(SquareMaximality.squareLatticeEntropy-Real.log (1+Real.sqrt 2))≤
      Real.log ((treeCount (comparisonDomain A.card) : ℝ)/(treeCount A : ℝ)) := by
  let n := Nat.sqrt A.card
  let q := A.card-n^2
  let j := ComparisonDomain.leafSeeds n q
  let beta := (R+1)+(S+1)-minimumSideSum A.card
  have hN : 0<A.card := hHull.card_pos
  obtain ⟨hn,hEq,hq⟩ := square_remainder_data hN
  change 0<n at hn
  change A.card=n^2+q at hEq
  change q≤2*n at hq
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
  have hBconn : (domainGraph B).Connected := by
    rw [domainGraph_eq_foundation]
    exact ComparisonDomain.comparisonDomain_connected hn q
  have hBpos : (0 : ℝ)<SquareMaximality.tau B := by
    rw [← treeCount_eq_foundation]
    exact_mod_cast (treeCount_pos_iff_connected B).mpr hBconn
  have hApos : (0 : ℝ)<SquareMaximality.tau A := by
    rw [← treeCount_eq_foundation]
    exact_mod_cast (treeCount_pos_iff_connected A).mpr hconn
  have hgain := ComparisonDomain.comparisonDomain_log_gain hn hq
  change Real.log (SquareMaximality.tauRect n n : ℝ)+
    SquareMaximality.squareLatticeEntropy*((q : ℝ)-j)≤Real.log (SquareMaximality.tau B : ℝ) at hgain
  have hrect := RectangularComparison.rectangular_comparison hn
    (by omega : 0<R+1) (by omega : 0<S+1) (by omega : n^2≤(R+1)*(S+1))
  rw [rectangle_treeCount_eq_foundation,rectangle_treeCount_eq_foundation,
    entropy_eq_foundation] at hrect
  have hcost := InteriorCost.enhanced_hull_bound_all hHull
    (by simpa only [← domainGraph_eq_foundation] using hconn)
  rw [Nat.cast_sub harea] at hcost
  push_cast at hcost hrect hside
  have hEqR : (A.card : ℝ)=(n : ℝ)^2+q := by exact_mod_cast hEq
  rw [hEqR] at hcost
  rw [hside] at hrect
  change Real.log (1+Real.sqrt 2)*((beta : ℝ)+EnhancedBoundary.boundaryGapCount R S A)+
      (3 : ℝ)/5*canonicalInteriorCount R S A-
        (j : ℝ)*(SquareMaximality.squareLatticeEntropy-Real.log (1+Real.sqrt 2))≤
      Real.log ((treeCount B : ℝ)/(treeCount A : ℝ))
  rw [treeCount_eq_foundation,treeCount_eq_foundation,Real.log_div hBpos.ne' hApos.ne']
  nlinarith only [hgain,hcost,hrect]

/-- Quantitative integer rigidity at an arbitrary translated minimal hull.
The counts g,c are taken after translating its southwest corner to zero;
translation does not change the source tree count or cardinality. -/
theorem integer_rigidity {A : Domain} {a b : ℤ} {r s : ℕ}
    (hconn : (domainGraph A).Connected) (hHull : SquareMaximality.IsRectHull A a b r s) :
    let A₀ := SquareMaximality.translateFinset (-a) (-b) A
    Real.log (1+Real.sqrt 2)*
        (((r+s-minimumSideSum A.card : ℕ) : ℝ)+
          EnhancedBoundary.boundaryGapCount (r-1) (s-1) A₀)+
      (3 : ℝ)/5*canonicalInteriorCount (r-1) (s-1) A₀-
        (leafSeeds A.card : ℝ)*(SquareMaximality.squareLatticeEntropy-Real.log (1+Real.sqrt 2))≤
      Real.log ((treeCount (comparisonDomain A.card) : ℝ)/(treeCount A : ℝ)) := by
  obtain ⟨R,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hHull.1)
  obtain ⟨S,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hHull.2.1)
  have hconn₀ := (MaximizerGeometry.connected_translateFinset_iff (-a) (-b) A).mpr hconn
  have h := normalized_integer_rigidity hconn₀ hHull.translate_to_origin
  simpa only [MaximizerGeometry.translateFinset_card,MaximizerGeometry.treeCount_translateFinset,
    Nat.succ_eq_add_one,Nat.add_sub_cancel] using h

end
end SpanningTreeIsoperimetry.IntegerRigidityComparison
