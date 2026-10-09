import SpanningTreeIsoperimetry.FiniteFaceCountBridge
import SpanningTreeIsoperimetry.CornerPrimalFaces
import SpanningTreeIsoperimetry.CanonicalStrips

/-! The ten-vertex opposite-singleton candidate ties the canonical strip.
Both actual primal counts reduce to the same four-vertex face path. -/
namespace SpanningTreeIsoperimetry.SmallTenComparison
open SmallCases FiniteFaceCountBridge CornerEnergy CornerPrimalDomains CornerStripBridge DomainIsometries
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def singletonPair : Corner → Ferrers.Diagram :=
  twoCornerFamily (true,true) (false,false) (Ferrers.horizontalStrip 1) (Ferrers.horizontalStrip 1)

theorem singletonPair_ferrers : ∀ c, IsFerrers (singletonPair c) :=
  twoCornerFamily_ferrers _ _ (Ferrers.horizontalStrip_isFerrers 1) (Ferrers.horizontalStrip_isFerrers 1)

theorem singletonPair_total : totalDefect singletonPair=2 := by
  rw [singletonPair,totalDefect_twoCornerFamily (by decide : (true,true)≠(false,false))]
  norm_num [Ferrers.card_horizontalStrip]

def oppositePoints : Fin 4 → Vertex := ![(1,0),(1,1),(0,1),(0,2)]
def canonicalPoints : Fin 4 → Vertex := ![(0,0),(0,1),(0,2),(0,3)]

theorem oppositePoints_injective : Function.Injective oppositePoints := by decide +kernel
theorem canonicalPoints_injective : Function.Injective canonicalPoints := by decide +kernel

theorem opposite_face_set : cornerFaceDomain 2 3 singletonPair=Finset.univ.image oppositePoints := by
  decide +kernel

theorem canonical_face_set : cornerStrip 1 4 0=Finset.univ.image canonicalPoints := by decide +kernel

theorem path_matrix_eq {R : Type*} [CommRing R] (z : R) :
    pointMatrix oppositePoints z=pointMatrix canonicalPoints z := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pointMatrix,oppositePoints,canonicalPoints]

theorem path_det {R : Type*} [CommRing R] (z : R) :
    Matrix.det (pointMatrix canonicalPoints z)=continuant z 4 := by
  have hm : pointMatrix canonicalPoints z= !![z,-1,0,0; -1,z,-1,0; 0,-1,z,-1; 0,0,-1,z] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [pointMatrix,canonicalPoints]
  rw [hm]
  simp [Matrix.det_succ_row_zero,Fin.sum_univ_succ,Matrix.submatrix,Fin.succAbove,continuant]
  ring

theorem minimumSideSum_ten : minimumSideSum 10=7 := by
  unfold minimumSideSum
  apply (Nat.ceil_eq_iff (by decide : 7≠0)).mpr
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤10)
  have hn := Real.sqrt_nonneg (10 : ℝ)
  constructor <;> norm_num <;> nlinarith

theorem canonicalDomain_ten : canonicalDomain 10=cornerStrip 2 5 0 := by
  simp only [canonicalDomain,canonicalParameters,minimumSideSum_ten]
  norm_num [selectorIndex,Nat.sqrt]

theorem canonical_ten_count : treeCount (canonicalDomain 10)=209 := by
  rw [canonicalDomain_ten]
  have h := cornerStrip_treeCount_eq_dirichlet (by decide : 1≤1) (by decide : 1≤4) (by decide : 0≤4)
  rw [face_dirichlet_det_eq_integer,integerFaces_strip_faces,canonical_face_set] at h
  change (treeCount (cornerStrip 2 5 0) : ℝ)=
    StripPolarization.faceDeterminant (Finset.univ.image canonicalPoints) 4 at h
  rw [faceDeterminant_points canonicalPoints canonicalPoints_injective,path_det] at h
  norm_num [continuant] at h
  exact_mod_cast h

theorem opposite_ten_count : treeCount (cornerPrimal 2 3 singletonPair)=209 := by
  have h := cornerPrimal_treeCount_eq_faceDeterminant (by decide : 1≤2) (by decide : 1≤3)
    singletonPair_ferrers (by rw [singletonPair_total]) (by rw [singletonPair_total]; decide)
  rw [opposite_face_set,faceDeterminant_points oppositePoints oppositePoints_injective,
    path_matrix_eq,path_det] at h
  norm_num [continuant] at h
  exact_mod_cast h

theorem opposite_ten_card : (cornerPrimal 2 3 singletonPair).card=10 := by
  rw [cornerPrimal_card singletonPair_ferrers (by rw [singletonPair_total])
    (by rw [singletonPair_total]; decide),singletonPair_total]

theorem opposite_equal_canonical : treeCount (cornerPrimal 2 3 singletonPair)=treeCount (canonicalDomain 10) := by
  rw [opposite_ten_count,canonical_ten_count]

end
end SpanningTreeIsoperimetry.SmallTenComparison
