import SpanningTreeIsoperimetry.SmallTenComparison
import SpanningTreeIsoperimetry.CanonicalThirteen
import SpanningTreeIsoperimetry.CanonicalChecks

/-! Opposite singleton counts on all four small two-vacancy hulls. -/
namespace SpanningTreeIsoperimetry.SingletonPairComparisons
open CornerPrimalDomains CornerEnergy SmallCases FiniteFaceCountBridge
open SmallTenComparison
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem singleton_pair_seven : cornerPrimal 2 2 singletonPair=ConcreteCounts.winner7Domain := by decide +kernel
theorem singleton_pair_fourteen : cornerPrimal 3 3 singletonPair=ConcreteCounts.winner14Domain := by decide +kernel

theorem seven_count : treeCount (cornerPrimal 2 2 singletonPair)=16 := by
  rw [singleton_pair_seven,ConcreteCounts.winner7_treeCount]
theorem fourteen_count : treeCount (cornerPrimal 3 3 singletonPair)=8960 := by
  rw [singleton_pair_fourteen,ConcreteCounts.winner14_treeCount]

def thirteenPoints : Fin 6 → Vertex := ![(0,1),(0,2),(0,3),(1,0),(1,1),(1,2)]
theorem thirteenPoints_injective : Function.Injective thirteenPoints := by decide +kernel
theorem thirteen_face_set : cornerFaceDomain 2 4 singletonPair=Finset.univ.image thirteenPoints := by decide +kernel

def thirteenToEll : Equiv.Perm (Fin 6) where
  toFun := ![1,2,0,3,4,5]
  invFun := ![2,0,1,3,4,5]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem thirteen_matrix (z : ℝ) : pointMatrix thirteenPoints z=
    (pointMatrix ThirteenFaceCounts.ellPoints z).submatrix thirteenToEll thirteenToEll := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pointMatrix,thirteenPoints,ThirteenFaceCounts.ellPoints,thirteenToEll,Matrix.submatrix]

theorem thirteen_count : treeCount (cornerPrimal 2 4 singletonPair)=2640 := by
  have h := cornerPrimal_treeCount_eq_faceDeterminant (by decide : 1≤2) (by decide : 1≤4)
    singletonPair_ferrers (by rw [singletonPair_total]) (by rw [singletonPair_total]; decide)
  rw [thirteen_face_set,faceDeterminant_points thirteenPoints thirteenPoints_injective,
    thirteen_matrix,Matrix.det_submatrix_equiv_self,ThirteenFaceCounts.ellPoints_det] at h
  norm_num [ell13,continuant,cycle] at h
  exact_mod_cast h

theorem thirteen_not_maximal : ¬IsMaximizer (cornerPrimal 2 4 singletonPair) := by
  intro hm
  have hcard : (canonicalDomain 13).card=(cornerPrimal 2 4 singletonPair).card := by
    rw [canonicalDomain_card (by decide : 0<13),cornerPrimal_card singletonPair_ferrers
      (by rw [singletonPair_total]) (by rw [singletonPair_total]; decide),singletonPair_total]
  have h := hm.2 (canonicalDomain 13) hcard (CanonicalStrips.canonicalDomain_connected (by decide))
  rw [CanonicalThirteen.canonical13_treeCount,thirteen_count] at h
  omega

end
end SpanningTreeIsoperimetry.SingletonPairComparisons
