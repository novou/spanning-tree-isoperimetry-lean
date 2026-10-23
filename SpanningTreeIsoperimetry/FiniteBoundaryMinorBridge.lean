module

public import SpanningTreeIsoperimetry.FiniteBoundaryMinors
public import SpanningTreeIsoperimetry.FiniteGreenMonotonicity
public import SpanningTreeIsoperimetry.CornerStripBridge
public import SpanningTreeIsoperimetry.ThreeCellEnergy
public import SpanningTreeIsoperimetry.SmallGreenEnclosures

@[expose] public section

/-! The exact finite boundary blocks are the actual corner-strip Green
minors. Their monotonicity and the five terminal comparisons follow. -/
namespace SpanningTreeIsoperimetry.FiniteBoundaryMinorBridge
open Ferrers CornerEnergy CornerStripBridge ScalarResolvent FiniteBoundaryMinors
open FiniteGreenMonotonicity SquareMaximality.Boundary
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def verticalEquiv (k : ℕ) : Fin k ≃ {p // p∈verticalDiagram k} where
  toFun i := ⟨(0,i.val),mem_verticalDiagram.mpr ⟨rfl,i.isLt⟩⟩
  invFun p := ⟨p.val.2,(mem_verticalDiagram.mp p.property).2⟩
  left_inv i := by apply Fin.ext; rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (mem_verticalDiagram.mp p.property).1.symm
    · rfl

theorem leadingBlock_det_eq_greenMinor {R S k : ℕ} (hR : 0<R) (hk : k≤S) :
    Matrix.det (leadingBlock hR hk)=
      Matrix.det (greenMinor (verticalDiagram_subset (by omega : 1≤R) hk)) := by
  let hI : verticalDiagram k⊆faceIndices R S := by
    rw [foundation_faceIndices]
    exact verticalDiagram_subset (by omega) hk
  have hinv : (rectangleDirichlet R S)⁻¹=(fourIminusAdjacency (faceIndices R S))⁻¹.submatrix
      (rectangleFacesEquiv R S) (rectangleFacesEquiv R S) := by
    rw [rectangleDirichlet_eq_faceMatrix,Matrix.inv_submatrix_equiv]
  have he : Matrix.det (leadingBlock hR hk)=Matrix.det (greenMinor hI) := by
    rw [← Matrix.det_submatrix_equiv_self (verticalEquiv k)]
    congr 1
    ext i j
    simp only [leadingBlock,boundaryGreen,Matrix.submatrix_apply,hinv,greenMinor,
      verticalEquiv,rectangleFacesEquiv,Equiv.coe_fn_mk,Equiv.coe_fn_symm_mk]
    rfl
  exact he.trans (UniformStripEnergy.greenMinor_det_transport (foundation_faceIndices R S) rfl hI
    (verticalDiagram_subset (by omega) hk))

theorem leadingMinor_monotone {R S T W k : ℕ} (hR : 0<R) (hT : 0<T)
    (hkS : k≤S) (hkW : k≤W) (hRT : R≤T) (hSW : S≤W) :
    Matrix.det (leadingBlock hR hkS)≤Matrix.det (leadingBlock hT hkW) := by
  rw [leadingBlock_det_eq_greenMinor,leadingBlock_det_eq_greenMinor]
  exact greenMinor_det_monotone (verticalDiagram_ferrers k) _ _ hRT hSW

theorem terminal_two_four : (256 : ℝ)/259*(2-(16/3)/Real.pi)^2<
    Matrix.det (leadingBlock (by decide : 0<3) (by decide : 2≤5)) := by
  have hp:=SingletonEnergy.singleton_green_pos
  have hu:=SingletonEnergy.singleton_green_lt
  have hs : (2-(16/3)/Real.pi)^2<((303 : ℝ)/1000)^2 := by nlinarith
  linarith [floor_4_6]

theorem terminal_two_five : (2-(16/3)/Real.pi)^2<
    Matrix.det (leadingBlock (by decide : 0<4) (by decide : 2≤6)) := by
  have hp:=SingletonEnergy.singleton_green_pos
  have hu:=SingletonEnergy.singleton_green_lt
  have hs : (2-(16/3)/Real.pi)^2<((303 : ℝ)/1000)^2 := by nlinarith
  linarith [floor_5_7]

theorem terminal_three : ThreeCellEnergy.ellDet (1/Real.pi)<
    Matrix.det (leadingBlock (by decide : 0<4) (by decide : 3≤7)) := by
  linarith [ThreeCellEnergy.ellDet_lt,floor_5_8]

theorem terminal_four_seven : (2401 : ℝ)/2407*SmallGreenPolynomials.squareDet (1/Real.pi)<
    Matrix.det (leadingBlock (by decide : 0<6) (by decide : 4≤10)) := by
  linarith [SmallGreenEnclosures.squareDet_upper,floor_7_11]

theorem terminal_four_eight : SmallGreenPolynomials.squareDet (1/Real.pi)<
    Matrix.det (leadingBlock (by decide : 0<7) (by decide : 4≤11)) := by
  linarith [SmallGreenEnclosures.squareDet_upper,floor_8_12]

end
end SpanningTreeIsoperimetry.FiniteBoundaryMinorBridge
