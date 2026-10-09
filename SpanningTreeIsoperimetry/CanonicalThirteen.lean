import SpanningTreeIsoperimetry.SmallPrimalComparisons
import SpanningTreeIsoperimetry.CanonicalStrips

/-! The second thirteen-vertex maximizer candidate has the canonical count.
The full maximality classification is proved separately from this equality. -/
namespace SpanningTreeIsoperimetry.CanonicalThirteen
open SmallCases FiniteFaceCountBridge CornerEnergy CornerStripBridge DomainIsometries
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem minimumSideSum_thirteen : minimumSideSum 13=8 := by
  unfold minimumSideSum
  apply (Nat.ceil_eq_iff (by decide : 8≠0)).mpr
  have hs:=Real.sq_sqrt (by norm_num : (0 : ℝ)≤13)
  have hn:=Real.sqrt_nonneg (13 : ℝ)
  constructor <;> norm_num <;> nlinarith

theorem canonicalDomain_thirteen : canonicalDomain 13=cornerStrip 3 5 2 := by
  simp only [canonicalDomain,canonicalParameters,minimumSideSum_thirteen]
  norm_num [selectorIndex,Nat.sqrt]

def canonicalPoints : Fin 6 → Vertex := ![(1,0),(1,1),(0,2),(1,2),(0,3),(1,3)]

theorem canonicalPoints_injective : Function.Injective canonicalPoints := by decide +kernel

theorem canonicalPoints_image : Finset.univ.image canonicalPoints=cornerStrip 2 4 2 := by decide +kernel

def canonicalToOpposite : Fin 6 ≃ Fin 6 where
  toFun := ![0,3,1,2,4,5]
  invFun := ![0,2,3,1,4,5]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem canonicalPoints_matrix (z : ℝ) : pointMatrix canonicalPoints z=
    (pointMatrix ThirteenFaceCounts.oppositePoints z).submatrix canonicalToOpposite canonicalToOpposite := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pointMatrix,canonicalPoints,ThirteenFaceCounts.oppositePoints,canonicalToOpposite,Matrix.submatrix]

theorem canonical13_treeCount : treeCount (canonicalDomain 13)=2656 := by
  rw [canonicalDomain_thirteen]
  have h:=cornerStrip_treeCount_eq_dirichlet (by decide : 1≤2) (by decide : 1≤4) (by decide : 2≤4)
  rw [face_dirichlet_det_eq_integer,integerFaces_strip_faces,← canonicalPoints_image] at h
  change (treeCount (cornerStrip 3 5 2) : ℝ)=
    StripPolarization.faceDeterminant (Finset.univ.image canonicalPoints) 4 at h
  rw [faceDeterminant_points canonicalPoints canonicalPoints_injective,canonicalPoints_matrix,
    Matrix.det_submatrix_equiv_self,ThirteenFaceCounts.oppositePoints_det] at h
  norm_num [opposite13,continuant,cycle] at h
  exact_mod_cast h

theorem opposite_equal_canonical :
    treeCount (CornerPrimalDomains.cornerPrimal 3 3 SmallPrimalComparisons.oppositeFamily)=
      treeCount (canonicalDomain 13) := by
  rw [SmallPrimalComparisons.opposite_primal_count,canonical13_treeCount]

end SpanningTreeIsoperimetry.CanonicalThirteen
