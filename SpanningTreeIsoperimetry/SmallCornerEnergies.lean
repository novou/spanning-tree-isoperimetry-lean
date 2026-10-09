import SpanningTreeIsoperimetry.SmallGreenPolynomials
import SpanningTreeIsoperimetry.CornerEnergySymmetry
import SpanningTreeIsoperimetry.UniformStripEnergy

/-! The checked small determinant polynomials are the actual quadrant
Green minors and hence the exact corner energies. -/
namespace SpanningTreeIsoperimetry.SmallCornerEnergies
open Ferrers CornerEnergy BoundaryLayerGreen SmallGreenPolynomials Filter
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def rectangleEquiv (r s : ℕ) : (Fin r × Fin s) ≃ {p // p∈faceRectangle r s} where
  toFun p := ⟨(p.1.val,p.2.val),mem_faceRectangle.mpr ⟨p.1.isLt,p.2.isLt⟩⟩
  invFun p := (⟨p.val.1,(mem_faceRectangle.mp p.property).1⟩,
    ⟨p.val.2,(mem_faceRectangle.mp p.property).2⟩)
  left_inv p := by apply Prod.ext <;> apply Fin.ext <;> rfl
  right_inv p := by apply Subtype.ext; rfl

def squareEquiv : Fin 4 ≃ {p // p∈faceRectangle 2 2} :=
  (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm.trans (rectangleEquiv 2 2)

def rectangleSixEquiv : Fin 6 ≃ {p // p∈faceRectangle 3 2} :=
  (finProdFinEquiv : Fin 3 × Fin 2 ≃ Fin 6).symm.trans (rectangleEquiv 3 2)

def stripEquiv : Fin 4 ≃ {p // p∈horizontalStrip 4} where
  toFun i := ⟨(i.val,0),mem_horizontalStrip.mpr ⟨i.isLt,rfl⟩⟩
  invFun p := ⟨p.val.1,(mem_horizontalStrip.mp p.property).1⟩
  left_inv i := by apply Fin.ext; rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (mem_horizontalStrip.mp p.property).2.symm

theorem rectangleFit {r s : ℕ} (hr : r≤5) (hs : s≤5) (N : ℕ) :
    faceRectangle r s ⊆ faceRectangle (N+5) (N+5) := by
  intro p hp
  rw [mem_faceRectangle] at hp ⊢
  omega

theorem stripFit (N : ℕ) : horizontalStrip 4 ⊆ faceRectangle (N+5) (N+5) := by
  intro p hp
  have hb := mem_horizontalStrip.mp hp
  rw [mem_faceRectangle]
  omega

theorem frame_window (N : ℕ) : faceRectangle (N+5) (N+5)=window N :=
  (foundation_faceIndices (N+5) (N+5)).symm

theorem frameFit {M : Diagram} (hfit : ∀ N, M⊆faceRectangle (N+5) (N+5)) (N : ℕ) : M⊆window N :=
  frame_window N ▸ hfit N

def frameMatrix {ι : Type*} {M : Diagram} (e : ι ≃ {p // p∈M})
    (hfit : ∀ N, M⊆faceRectangle (N+5) (N+5)) (N : ℕ) : Matrix ι ι ℝ :=
  (SquareMaximality.Boundary.fourIminusAdjacency (window N))⁻¹.submatrix
    (fun i => ⟨(e i).val,frameFit hfit N (e i).property⟩)
    (fun i => ⟨(e i).val,frameFit hfit N (e i).property⟩)

theorem frameMatrix_det {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Diagram}
    (e : ι ≃ {p // p∈M}) (hfit : ∀ N, M⊆faceRectangle (N+5) (N+5)) (N : ℕ) :
    Matrix.det (greenMinor (hfit N))=Matrix.det (frameMatrix e hfit N) := by
  rw [UniformStripEnergy.greenMinor_det_transport (frame_window N) rfl (hfit N) (frameFit hfit N)]
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

theorem energy_limit_identity {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Diagram}
    (hM : IsFerrers M) (e : ι ≃ {p // p∈M}) (hfit : ∀ N, M⊆faceRectangle (N+5) (N+5))
    (L : Matrix ι ι ℝ) (ht : Tendsto (frameMatrix e hfit) atTop (𝓝 L)) :
    Real.exp (-realEnergy M-SquareMaximality.squareLatticeEntropy*M.card)=Matrix.det L := by
  have hside : Tendsto (fun N : ℕ => N+5) atTop atTop :=
    tendsto_atTop_mono (fun N => by change N≤N+5; omega) tendsto_id
  have he := greenMinor_det_tendsto hM hfit hside hside
  simp only [frameMatrix_det e hfit] at he
  have hd := ((show Continuous (Matrix.det : Matrix ι ι ℝ → ℝ)
    from continuous_id.matrix_det).tendsto _).comp ht
  exact tendsto_nhds_unique he hd

theorem twoRowSubmatrix_tendsto {ι : Type*} (f : ι → Fin 3 × Fin 2) :
    Tendsto (fun N => (twoRowFinite N).submatrix f f) atTop
      (𝓝 ((twoRowValue (1/Real.pi)).submatrix f f)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp twoRowFinite_tendsto (f i)) (f j)

theorem squareFrame_tendsto :
    Tendsto (frameMatrix squareEquiv (rectangleFit (by decide : 2≤5) (by decide : 2≤5))) atTop
      (𝓝 (squareMatrix (1/Real.pi))) := by
  have he : frameMatrix squareEquiv (rectangleFit (by decide : 2≤5) (by decide : 2≤5))=
      (fun N => (twoRowFinite N).submatrix squarePoints squarePoints) := by
    funext N
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [he]
  exact twoRowSubmatrix_tendsto squarePoints

theorem rectangleFrame_tendsto :
    Tendsto (frameMatrix rectangleSixEquiv (rectangleFit (by decide : 3≤5) (by decide : 2≤5))) atTop
      (𝓝 (rectangleMatrix (1/Real.pi))) := by
  have he : frameMatrix rectangleSixEquiv (rectangleFit (by decide : 3≤5) (by decide : 2≤5))=
      (fun N => (twoRowFinite N).submatrix rectanglePoints rectanglePoints) := by
    funext N
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [he]
  exact twoRowSubmatrix_tendsto rectanglePoints

theorem stripFrame_tendsto : Tendsto (frameMatrix stripEquiv stripFit) atTop
    (𝓝 (stripMatrix (1/Real.pi))) := by
  have he : frameMatrix stripEquiv stripFit=(fun N i j => boundaryEntry N i j) := rfl
  rw [he]
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact boundaryEntry_tendsto i j

theorem square_exp_energy : Real.exp (-realEnergy (faceRectangle 2 2)-
    4*SquareMaximality.squareLatticeEntropy)=squareDet (1/Real.pi) := by
  have h := energy_limit_identity (faceRectangle_isFerrers 2 2) squareEquiv
    (rectangleFit (by decide : 2≤5) (by decide : 2≤5)) (squareMatrix (1/Real.pi)) squareFrame_tendsto
  rw [squareMatrix_det] at h
  norm_num [faceRectangle] at h
  simpa only [mul_comm,one_div,faceRectangle] using h

theorem rectangle_exp_energy : Real.exp (-realEnergy (faceRectangle 3 2)-
    6*SquareMaximality.squareLatticeEntropy)=rectangleDet (1/Real.pi) := by
  have h := energy_limit_identity (faceRectangle_isFerrers 3 2) rectangleSixEquiv
    (rectangleFit (by decide : 3≤5) (by decide : 2≤5)) (rectangleMatrix (1/Real.pi)) rectangleFrame_tendsto
  rw [rectangleMatrix_det] at h
  norm_num [faceRectangle] at h
  simpa only [mul_comm,one_div,faceRectangle] using h

theorem strip_exp_energy : Real.exp (-realEnergy (horizontalStrip 4)-
    4*SquareMaximality.squareLatticeEntropy)=stripDet (1/Real.pi) := by
  have h := energy_limit_identity (horizontalStrip_isFerrers 4) stripEquiv stripFit
    (stripMatrix (1/Real.pi)) stripFrame_tendsto
  rw [stripMatrix_det,card_horizontalStrip] at h
  norm_num at h
  simpa only [mul_comm,one_div] using h

theorem square_energy_exact : realEnergy (faceRectangle 2 2)=
    -Real.log (squareDet (1/Real.pi))-4*SquareMaximality.squareLatticeEntropy := by
  have h:=congrArg Real.log square_exp_energy
  rw [Real.log_exp] at h
  linarith

theorem rectangle_energy_exact : realEnergy (faceRectangle 3 2)=
    -Real.log (rectangleDet (1/Real.pi))-6*SquareMaximality.squareLatticeEntropy := by
  have h:=congrArg Real.log rectangle_exp_energy
  rw [Real.log_exp] at h
  linarith

theorem strip_energy_exact : realEnergy (horizontalStrip 4)=
    -Real.log (stripDet (1/Real.pi))-4*SquareMaximality.squareLatticeEntropy := by
  have h:=congrArg Real.log strip_exp_energy
  rw [Real.log_exp] at h
  linarith

end
end SpanningTreeIsoperimetry.SmallCornerEnergies
