import SpanningTreeIsoperimetry.SummableKernelProductTail
import Mathlib.Tactic.NoncommRing

/-! Multiplicativity of the actual absolutely-summable finite-section
limit, and nonvanishing for explicit inverse perturbations. -/
namespace SpanningTreeIsoperimetry.SummableKernelDeterminant
open SummableKernelProduct SummableKernelProductTail AbsolutelySummableDeterminant
open FiniteSectionPadding FiniteDeterminantContinuity Filter
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def detLimit (K : Kernel) (hK : Summable (entryNorm K)) : ℝ :=
  Classical.choose (exists_section_limit K hK)

theorem detLimit_tendsto (K : Kernel) (hK : Summable (entryNorm K)) :
    Tendsto (fun n => (1+finiteSection K n).det) atTop (𝓝 (detLimit K hK)) :=
  Classical.choose_spec (exists_section_limit K hK)

theorem detLimit_congr {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (he : A=B) : detLimit A hA=detLimit B hB := by
  subst B
  rfl

private theorem mass_sub_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    mass (A-B)≤mass A+mass B := by
  unfold mass rowMass
  simp only [Matrix.sub_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (A i j) (-B i j)

def sectionProduct (A B : Kernel) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  finiteSection A n+finiteSection B n+finiteSection A n*finiteSection B n

theorem sectionProduct_det (A B : Kernel) (n : ℕ) :
    (1+sectionProduct A B n).det=(1+finiteSection A n).det*(1+finiteSection B n).det := by
  rw [← Matrix.det_mul]
  congr 1
  unfold sectionProduct
  noncomm_ring

theorem composition_error {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (n : ℕ) :
    finiteSection (composePerturbation A B) n-sectionProduct A B n=
      finiteSection (productRemainder A B n) n := by
  have he : finiteSection (composePerturbation A B) n=
      finiteSection A n+finiteSection B n+finiteSection (product A B) n := by
    ext i j
    rfl
  rw [he,sectionProduct]
  convert finite_product_error hA hB n using 1 <;> abel

theorem composition_error_mass_le {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (n : ℕ) :
    mass (finiteSection (composePerturbation A B) n-sectionProduct A B n)≤tailMass A n*totalMass B := by
  rw [composition_error hA hB]
  exact (mass_section_le (remainder_summable hA hB n) n).trans (remainder_mass_le hA hB n)

theorem sectionProduct_mass_le {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (n : ℕ) :
    mass (sectionProduct A B n)≤totalMass (composePerturbation A B)+totalMass A*totalMass B := by
  have he : sectionProduct A B n=finiteSection (composePerturbation A B) n-
      finiteSection (productRemainder A B n) n := by
    rw [← composition_error hA hB]
    abel
  rw [he]
  have hr := (mass_section_le (remainder_summable hA hB n) n).trans (remainder_mass_le hA hB n)
  have hr' := hr.trans (mul_le_mul_of_nonneg_right (tailMass_le_total hA n) (totalMass_nonneg B))
  exact (mass_sub_le _ _).trans (add_le_add (mass_section_le (compose_summable hA hB) n) hr')

/-- The finite multiplicativity defect is bounded by a genuine kernel tail,
with a constant independent of the finite-section size. -/
theorem determinant_product_error_le {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (n : ℕ) :
    |(1+finiteSection (composePerturbation A B) n).det-
      (1+finiteSection A n).det*(1+finiteSection B n).det|≤
      tailMass A n*totalMass B*Real.exp
        (2*totalMass (composePerturbation A B)+totalMass A*totalMass B) := by
  rw [← sectionProduct_det]
  have hb := determinant_continuity (finiteSection (composePerturbation A B) n) (sectionProduct A B n)
  have hC := mass_section_le (compose_summable hA hB) n
  have hP := sectionProduct_mass_le hA hB n
  exact hb.trans (mul_le_mul (composition_error_mass_le hA hB n)
    (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
    (mul_nonneg (tsum_nonneg (tailEntry_nonneg A n)) (totalMass_nonneg B)))

theorem determinant_product_error_tendsto {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) :
    Tendsto (fun n => (1+finiteSection (composePerturbation A B) n).det-
      (1+finiteSection A n).det*(1+finiteSection B n).det) atTop (𝓝 0) := by
  have ht := ((tailMass_tendsto_zero A hA).mul_const (totalMass B)).mul_const
    (Real.exp (2*totalMass (composePerturbation A B)+totalMass A*totalMass B))
  have ht' : Tendsto (fun n => tailMass A n*totalMass B*Real.exp
      (2*totalMass (composePerturbation A B)+totalMass A*totalMass B)) atTop (𝓝 0) := by
    simpa only [zero_mul] using ht
  apply squeeze_zero_norm' _ ht'
  exact Filter.Eventually.of_forall (fun n => by
    simpa only [Real.norm_eq_abs] using determinant_product_error_le hA hB n)

/-- Multiplicativity is proved for the actual limits of finite determinants. -/
theorem detLimit_compose {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) :
    detLimit (composePerturbation A B) (compose_summable hA hB)=detLimit A hA*detLimit B hB := by
  have ht := (determinant_product_error_tendsto hA hB).add
    ((detLimit_tendsto A hA).mul (detLimit_tendsto B hB))
  have hlimit : Tendsto (fun n => (1+finiteSection (composePerturbation A B) n).det) atTop
      (𝓝 (detLimit A hA*detLimit B hB)) := by
    simpa only [sub_add_cancel,zero_add] using ht
  exact tendsto_nhds_unique (detLimit_tendsto _ (compose_summable hA hB)) hlimit

theorem zero_summable : Summable (entryNorm (0 : Kernel)) := by
  change Summable (fun _ : ℕ×ℕ => |(0 : ℝ)|)
  simp

theorem detLimit_zero : detLimit (0 : Kernel) zero_summable=1 := by
  have he (n : ℕ) : finiteSection (0 : Kernel) n=0 := by ext i j; rfl
  apply tendsto_nhds_unique (detLimit_tendsto _ zero_summable)
  simpa only [he,add_zero,Matrix.det_one] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))

theorem inverse_pair_det_mul {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (hAB : composePerturbation A B=0) :
    detLimit A hA*detLimit B hB=1 :=
  (detLimit_compose hA hB).symm.trans
    ((detLimit_congr (compose_summable hA hB) zero_summable hAB).trans detLimit_zero)

/-- An explicitly summable inverse perturbation rules out a zero limit. -/
theorem inverse_pair_nonzero {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (hAB : composePerturbation A B=0) :
    detLimit A hA≠0 ∧ detLimit B hB≠0 := by
  have h := inverse_pair_det_mul hA hB hAB
  constructor <;> intro hz <;> rw [hz] at h <;> simp at h

end
end SpanningTreeIsoperimetry.SummableKernelDeterminant
