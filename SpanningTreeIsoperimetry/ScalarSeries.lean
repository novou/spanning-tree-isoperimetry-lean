import SpanningTreeIsoperimetry.ScalarModular
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Normed

/-! Convergent expansion at infinity for the actual Green resolvent. -/
namespace SpanningTreeIsoperimetry.ScalarSeries

open scoped BigOperators Matrix Classical Matrix.Norms.Operator
open ScalarResolvent ScalarModular
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The absolute row sums of the actual path operator are at most six. -/
theorem pathOperator_norm_le (w : ℕ) : ‖pathOperator w‖ ≤ 6 := by
  have he (i j : Fin w) : ‖pathOperator w i j‖₊ =
      (if i = j then (4 : NNReal) else 0) +
        (if i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 then 1 else 0) := by
    rw [pathOperator_apply]
    by_cases hij : i = j
    · subst j
      simp
    · by_cases hn : i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 <;> simp [hij, hn]
  have hn : ‖pathOperator w‖₊ ≤ (6 : NNReal) := by
    rw [Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro i _
    simp_rw [he]
    rw [Finset.sum_add_distrib, path_neighbor_sum]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    split_ifs <;> norm_num
  exact_mod_cast hn

/-- A genuine matrix Neumann expansion on the explicit domain `|z| > 6`. -/
theorem resolvent_hasSum (w : ℕ) (z : ℝ) (hz : 6 < |z|) :
    HasSum (fun n : ℕ => (z⁻¹) ^ (n + 1) • pathOperator w ^ n)
      (z • (1 : Matrix (Fin w) (Fin w) ℝ) - pathOperator w)⁻¹ := by
  have hzpos : 0 < |z| := by linarith
  have hz0 : z ≠ 0 := abs_pos.mp hzpos
  have hsmall : ‖z⁻¹ • pathOperator w‖ < 1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs]
    have h := (div_lt_one hzpos).mpr ((pathOperator_norm_le w).trans_lt hz)
    simpa only [div_eq_mul_inv, mul_comm] using h
  let S : Matrix (Fin w) (Fin w) ℝ := ∑' n : ℕ, (z⁻¹ • pathOperator w) ^ n
  have hs := (summable_geometric_of_norm_lt_one hsmall).hasSum
  have hinv : (z • (1 : Matrix (Fin w) (Fin w) ℝ) - pathOperator w)⁻¹ = z⁻¹ • S := by
    apply Matrix.inv_eq_right_inv
    have hfac : z • (1 : Matrix (Fin w) (Fin w) ℝ) - pathOperator w =
        z • (1 - z⁻¹ • pathOperator w) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hz0, one_smul]
    rw [hfac, smul_mul_smul_comm, mul_inv_cancel₀ hz0, one_smul]
    exact mul_neg_geom_series _ hsmall
  rw [hinv]
  simpa only [S, smul_pow, smul_smul, pow_succ'] using hs.const_smul z⁻¹

/-- The coefficients are the actual boundary Green moments, with convergence
throughout `|z| > 6`. -/
theorem boundaryGreen_moment_hasSum {R w : ℕ}
    (hR : 0 < R) (hw : 0 < w) (z : ℝ) (hz : 6 < |z|) :
    HasSum (fun n : ℕ => moment hw (boundaryGreen hR w) n / z ^ (n + 1))
      ((boundaryGreen hR w *
        (z • (1 : Matrix (Fin w) (Fin w) ℝ) - pathOperator w)⁻¹) ⟨0, hw⟩ ⟨0, hw⟩) := by
  have h := (resolvent_hasSum w z hz).mul_left (boundaryGreen hR w)
  have he := Pi.hasSum.mp (Pi.hasSum.mp h ⟨0, hw⟩) ⟨0, hw⟩
  convert he using 1
  ext n
  simp only [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, moment,
    div_eq_mul_inv, inv_pow]
  ring

/-- Full scalar expansion with the rational modular numerator from the paper. -/
theorem rational_scalar_resolvent_hasSum {R w : ℕ}
    (hR : 0 < R) (hw : 0 < w) (z : ℝ) (hz : 6 < |z|) :
    HasSum (fun n : ℕ => moment hw (boundaryGreen hR w) n / z ^ (n + 1))
      ((rationalScalarNumerator hR hw).eval₂ (algebraMap ℚ ℝ) z /
        (rationalPathPolynomial w).eval₂ (algebraMap ℚ ℝ) z) := by
  rw [← boundaryGreen_rational_scalar_resolvent hR hw z]
  exact boundaryGreen_moment_hasSum hR hw z hz

end SpanningTreeIsoperimetry.ScalarSeries
