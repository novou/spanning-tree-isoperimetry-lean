import SpanningTreeIsoperimetry.CrossHullCountComparison
import SpanningTreeIsoperimetry.FiniteBoundaryMinorBridge
import SpanningTreeIsoperimetry.RefinedEntropyBounds

/-! Explicit upper bounds for actual finite strip energies. Exact rational
Green determinants and finite exponential sums prove every displayed bound. -/
namespace SpanningTreeIsoperimetry.FixedStripEnergyUpper
open Ferrers CornerEnergy CornerStripBridge CrossHullCountComparison
open FiniteBoundaryMinors FiniteBoundaryMinorBridge RefinedEntropyBounds
open ScalarResolvent FixedDirichletSystems FiniteGreenPotentials
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

theorem finiteTargetEnergy_eq_leading {R S j : ℕ} (hR : 2≤R) (hj : j≤S-1) :
    finiteTargetEnergy hR hj=
      -Real.log (Matrix.det (leadingBlock (by omega : 0<R-1) hj))-
        SquareMaximality.squareLatticeEntropy*j := by
  unfold finiteTargetEnergy dirichletEnergy
  rw [← leadingBlock_det_eq_greenMinor (by omega : 0<R-1) hj]
  simp [verticalDiagram]

theorem finiteTargetEnergy_antitone {r s R S j : ℕ}
    (hr : 2≤r) (hR : 2≤R) (hjs : j≤s-1) (hjS : j≤S-1)
    (hrR : r≤R) (hsS : s≤S) :
    finiteTargetEnergy hR hjS≤finiteTargetEnergy hr hjs := by
  have hp : 0<Matrix.det (leadingBlock (by omega : 0<r-1) hjs) := by
    rw [leadingBlock_det_eq_greenMinor]
    exact greenMinor_det_pos (Finset.Subset.refl (faceRectangle (r-1) (s-1))) _
  have hm := leadingMinor_monotone (by omega : 0<r-1) (by omega : 0<R-1)
    hjs hjS (by omega : r-1≤R-1) (by omega : s-1≤S-1)
  have hl := Real.log_le_log hp hm
  simp only [finiteTargetEnergy_eq_leading]
  linarith only [hl]

theorem finite_energy_lt_of_det {R S j : ℕ} (hR : 2≤R) (hj : j≤S-1)
    {q b : ℝ} (hq : 0<q)
    (hdet : Matrix.det (leadingBlock (by omega : 0<R-1) hj)=q)
    (hx : 0≤(11662429 : ℝ)/10000000*j+b)
    (hpoly : q⁻¹ < ∑ n∈Finset.range 32,
      ((11662429 : ℝ)/10000000*j+b)^n/(Nat.factorial n : ℝ)) :
    finiteTargetEnergy hR hj<b := by
  have hs := Real.sum_le_exp_of_nonneg hx 32
  have hl := (Real.log_lt_iff_lt_exp (inv_pos.mpr hq)).mpr (hpoly.trans_le hs)
  rw [Real.log_inv] at hl
  rw [finiteTargetEnergy_eq_leading,hdet]
  have he := mul_le_mul_of_nonneg_right entropy_lower.le (Nat.cast_nonneg (α := ℝ) j)
  linarith only [hl,he]

theorem singleton_det_4_6 :
    Matrix.det (leadingBlock (by decide : 0<3) (by decide : 1≤5))=
      (7312153 : ℝ)/24362520 := by
  rw [Matrix.det_fin_one]
  have h := congrFun (congrFun block_4_6 (0 : Fin 2)) (0 : Fin 2)
  change (boundaryGreen (by decide : 0<3) 5) 0 0=_ at h
  norm_num [potentialBlock,potential_4_6,denominator_4_6,boundarySources] at h
  exact h

theorem energy_1_4_6 :
    finiteTargetEnergy (by decide : 2≤4) (by decide : 1≤6-1)<(37266 : ℝ)/1000000 := by
  apply finite_energy_lt_of_det (by decide : 2≤4) (by decide : 1≤6-1)
    (by norm_num) singleton_det_4_6
  · norm_num
  · norm_num [Finset.sum_range_succ,Nat.factorial]

theorem energy_2_4_6 :
    finiteTargetEnergy (by decide : 2≤4) (by decide : 2≤6-1)<(62474 : ℝ)/1000000 := by
  apply finite_energy_lt_of_det (by decide : 2≤4) (by decide : 2≤6-1)
    (by norm_num) det_4_6
  · norm_num
  · norm_num [Finset.sum_range_succ,Nat.factorial]

theorem energy_2_4_7 :
    finiteTargetEnergy (by decide : 2≤4) (by decide : 2≤7-1)<(61659 : ℝ)/1000000 := by
  apply finite_energy_lt_of_det (by decide : 2≤4) (by decide : 2≤7-1)
    (by norm_num) det_4_7
  · norm_num
  · norm_num [Finset.sum_range_succ,Nat.factorial]

theorem energy_2_5_7 :
    finiteTargetEnergy (by decide : 2≤5) (by decide : 2≤7-1)<(50390 : ℝ)/1000000 := by
  apply finite_energy_lt_of_det (by decide : 2≤5) (by decide : 2≤7-1)
    (by norm_num) det_5_7
  · norm_num
  · norm_num [Finset.sum_range_succ,Nat.factorial]

theorem energy_3_5_8 :
    finiteTargetEnergy (by decide : 2≤5) (by decide : 3≤8-1)<(64522 : ℝ)/1000000 := by
  apply finite_energy_lt_of_det (by decide : 2≤5) (by decide : 3≤8-1)
    (by norm_num) det_5_8
  · norm_num
  · norm_num [Finset.sum_range_succ,Nat.factorial]

theorem energy_3_6_10 :
    finiteTargetEnergy (by decide : 2≤6) (by decide : 3≤10-1)<(55677 : ℝ)/1000000 := by
  apply finite_energy_lt_of_det (by decide : 2≤6) (by decide : 3≤10-1)
    (by norm_num) det_6_10
  · norm_num
  · norm_num [Finset.sum_range_succ,Nat.factorial]

theorem energy_4_7_11 :
    finiteTargetEnergy (by decide : 2≤7) (by decide : 4≤11-1)<(58904 : ℝ)/1000000 := by
  apply finite_energy_lt_of_det (by decide : 2≤7) (by decide : 4≤11-1)
    (by norm_num) det_7_11
  · norm_num
  · norm_num [Finset.sum_range_succ,Nat.factorial]

end
end SpanningTreeIsoperimetry.FixedStripEnergyUpper
