module

public import SpanningTreeIsoperimetry.MatrixGreenSeries
public import SpanningTreeIsoperimetry.HalfPlaneWalks
public import SpanningTreeIsoperimetry.BoundaryHalfPlane
public import SpanningTreeIsoperimetry.StripEnergyBound
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-! Finite face-window inverse entries converge to the explicitly evaluated
half-plane boundary Green matrices. -/
namespace SpanningTreeIsoperimetry.GreenExhaustion

open HalfPlaneWalks BoundaryGreen SquareMaximality.Boundary Filter
open scoped Topology Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def boundaryDistance (i j : Fin 6) : Fin 6 :=
  ⟨Nat.dist i.val j.val,by have hi:=i.isLt; have hj:=j.isLt; unfold Nat.dist; omega⟩

def boundaryGreenEntry (N : ℕ) (i j : Fin 6) : ℝ :=
  (fourIminusAdjacency (window N))⁻¹ (boundarySite N i) (boundarySite N j)

theorem boundaryGreenEntry_hasSum (N : ℕ) (i j : Fin 6) :
    HasSum (finiteBoundaryCoefficient N i j) (boundaryGreenEntry N i j) := by
  exact MatrixGreenSeries.face_inverse_walk_hasSum (R := 2*N+6) (S := N+1)
    (Finset.Subset.refl (window N)) (boundarySite N i) (boundarySite N j)

theorem boundaryGreenEntry_tendsto (i j : Fin 6) :
    Tendsto (fun N => boundaryGreenEntry N i j) atTop (𝓝 (boundaryValue (boundaryDistance i j))) := by
  have hs := halfPlaneCoefficient_hasSum (boundaryDistance i j)
  have ht := tendsto_tsum_of_dominated_convergence hs.summable
    (f := fun N n => finiteBoundaryCoefficient N i j n)
    (g := fun n => halfPlaneCoefficient n (Nat.dist i.val j.val))
    (fun n => (tendsto_const_nhds : Tendsto (fun _ : ℕ => halfPlaneCoefficient n (Nat.dist i.val j.val))
      atTop (𝓝 (halfPlaneCoefficient n (Nat.dist i.val j.val)))).congr'
      ((eventually_ge_atTop n).mono (fun N hN => (finiteBoundaryCoefficient_eq_halfPlane_of_le i j hN).symm)))
    (Eventually.of_forall (fun N n => by
      rw [Real.norm_eq_abs,abs_of_nonneg (finiteBoundaryCoefficient_nonneg N i j n)]
      exact finiteBoundaryCoefficient_le_halfPlane N i j n))
  have hf : (fun N => ∑' n, finiteBoundaryCoefficient N i j n)=
      (fun N => boundaryGreenEntry N i j) := by
    funext N
    exact (boundaryGreenEntry_hasSum N i j).tsum_eq
  rw [hf] at ht
  change Tendsto (fun N => boundaryGreenEntry N i j) atTop
    (𝓝 (∑' n, halfPlaneCoefficient n (boundaryDistance i j).val)) at ht
  rw [hs.tsum_eq] at ht
  exact ht

def indexSix : Fin 3 ⊕ Fin 3 → Fin 6
  | .inl i => ⟨i.val,by omega⟩
  | .inr i => ⟨5-i.val,by omega⟩

def boundaryMatrixSix (N : ℕ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  fun i j => boundaryGreenEntry N (indexSix i) (indexSix j)

theorem boundarySix_entry (i j : Fin 3 ⊕ Fin 3) :
    boundaryValue (boundaryDistance (indexSix i) (indexSix j))=
      StripEnergyBound.boundarySix (1/Real.pi) i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [boundaryValue,boundaryDistance,Nat.dist,indexSix,limitSix,initialSix,
      StripEnergyBound.boundarySix,StripEnergyBound.boundaryThree,StripEnergyBound.boundaryCross,
      Matrix.fromBlocks] <;> ring

theorem boundaryMatrixSix_tendsto :
    Tendsto boundaryMatrixSix atTop (𝓝 (StripEnergyBound.boundarySix (1/Real.pi))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have h := boundaryGreenEntry_tendsto (indexSix i) (indexSix j)
  rw [boundarySix_entry] at h
  exact h

def boundaryLeftThree (N : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (boundaryMatrixSix N).toBlocks₁₁

def boundaryRightThree (N : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (boundaryMatrixSix N).toBlocks₂₂

theorem boundaryLeftThree_tendsto :
    Tendsto boundaryLeftThree atTop (𝓝 (StripEnergyBound.boundaryThree (1/Real.pi))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have h := boundaryGreenEntry_tendsto (indexSix (.inl i)) (indexSix (.inl j))
  rw [boundarySix_entry] at h
  exact h

theorem boundaryRightThree_tendsto :
    Tendsto boundaryRightThree atTop (𝓝 (StripEnergyBound.boundaryThree (1/Real.pi))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have h := boundaryGreenEntry_tendsto (indexSix (.inr i)) (indexSix (.inr j))
  rw [boundarySix_entry] at h
  exact h

theorem boundarySix_det_tendsto :
    Tendsto (fun N => Matrix.det (boundaryMatrixSix N)) atTop
      (𝓝 (Matrix.det (StripEnergyBound.boundarySix (1/Real.pi)))) :=
  ((show Continuous (Matrix.det : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ → ℝ)
    from continuous_id.matrix_det).tendsto _).comp boundaryMatrixSix_tendsto

theorem boundaryLeftThree_det_tendsto :
    Tendsto (fun N => Matrix.det (boundaryLeftThree N)) atTop
      (𝓝 (Matrix.det (StripEnergyBound.boundaryThree (1/Real.pi)))) :=
  ((show Continuous (Matrix.det : Matrix (Fin 3) (Fin 3) ℝ → ℝ)
    from continuous_id.matrix_det).tendsto _).comp boundaryLeftThree_tendsto

theorem boundaryRightThree_det_tendsto :
    Tendsto (fun N => Matrix.det (boundaryRightThree N)) atTop
      (𝓝 (Matrix.det (StripEnergyBound.boundaryThree (1/Real.pi)))) :=
  ((show Continuous (Matrix.det : Matrix (Fin 3) (Fin 3) ℝ → ℝ)
    from continuous_id.matrix_det).tendsto _).comp boundaryRightThree_tendsto

end
end SpanningTreeIsoperimetry.GreenExhaustion
