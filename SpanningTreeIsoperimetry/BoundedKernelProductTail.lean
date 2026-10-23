module

public import SpanningTreeIsoperimetry.BoundedKernelProduct
public import SpanningTreeIsoperimetry.SummableKernelDeterminant

@[expose] public section

/-! Finite-product determinant convergence with one summable kernel and
one uniformly row-summable multiplier. The error is an actual kernel tail. -/
namespace SpanningTreeIsoperimetry.BoundedKernelProductTail
open BoundedKernelProduct SummableKernelProduct SummableKernelProductTail
open AbsolutelySummableDeterminant FiniteSectionPadding FiniteDeterminantContinuity
open SummableKernelDeterminant Filter
open scoped BigOperators Topology
noncomputable section

theorem shiftRows_bound {B : Kernel} {C : ℝ} (hB : RowBound B C) (n : ℕ) :
    RowBound (shiftRows B n) C :=
  ⟨hB.nonneg,fun i => hB.summable (i+n),fun i => hB.bound (i+n)⟩

theorem remainder_summable {A B : Kernel} (hA : Summable (entryNorm A))
    {C : ℝ} (hB : RowBound B C) (n : ℕ) :
    Summable (entryNorm (productRemainder A B n)) :=
  right_summable (shiftColumns_summable hA n) (shiftRows_bound hB n)

theorem remainder_mass_le {A B : Kernel} (hA : Summable (entryNorm A))
    {C : ℝ} (hB : RowBound B C) (n : ℕ) :
    totalMass (productRemainder A B n)≤tailMass A n*C :=
  (right_mass_le (shiftColumns_summable hA n) (shiftRows_bound hB n)).trans
    (mul_le_mul_of_nonneg_right (shiftColumns_mass_le_tail hA n) hB.nonneg)

theorem product_split {A B : Kernel} (hA : Summable (entryNorm A))
    {C : ℝ} (hB : RowBound B C) (n i j : ℕ) :
    (∑ k∈Finset.range n,A i k*B k j)+productRemainder A B n i j=product A B i j := by
  have hs : Summable (fun k => A i k*B k j) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using entry_norm_summable hA hB i j
  exact hs.sum_add_tsum_nat_add n

theorem finite_product_error {A B : Kernel} (hA : Summable (entryNorm A))
    {C : ℝ} (hB : RowBound B C) (n : ℕ) :
    finiteSection (product A B) n-finiteSection A n*finiteSection B n=
      finiteSection (productRemainder A B n) n := by
  ext i j
  simp only [Matrix.sub_apply,Matrix.mul_apply,finiteSection]
  have h := product_split hA hB n i.val j.val
  rw [← Fin.sum_univ_eq_sum_range] at h
  linarith only [h]

theorem finite_error_mass {A B : Kernel} (hA : Summable (entryNorm A))
    {C : ℝ} (hB : RowBound B C) (n : ℕ) :
    mass (finiteSection (product A B) n-finiteSection A n*finiteSection B n)≤tailMass A n*C := by
  rw [finite_product_error hA hB]
  exact (mass_section_le (remainder_summable hA hB n) n).trans (remainder_mass_le hA hB n)

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

theorem finite_product_mass {A B : Kernel} (hA : Summable (entryNorm A))
    {C : ℝ} (hB : RowBound B C) (n : ℕ) :
    mass (finiteSection A n*finiteSection B n)≤2*(totalMass A*C) := by
  have he : finiteSection A n*finiteSection B n=
      finiteSection (product A B) n-finiteSection (productRemainder A B n) n := by
    rw [← finite_product_error hA hB]
    abel
  rw [he]
  have h1 := (mass_section_le (right_summable hA hB) n).trans (right_mass_le hA hB)
  have h2 := (mass_section_le (remainder_summable hA hB n) n).trans
    ((remainder_mass_le hA hB n).trans (mul_le_mul_of_nonneg_right (tailMass_le_total hA n) hB.nonneg))
  exact (mass_sub_le _ _).trans (by linarith only [h1,h2])

theorem determinant_error_le {A B : Kernel} (hA : Summable (entryNorm A))
    {C : ℝ} (hB : RowBound B C) (n : ℕ) :
    |(1+finiteSection (product A B) n).det-(1+finiteSection A n*finiteSection B n).det|≤
      tailMass A n*C*Real.exp (3*(totalMass A*C)) := by
  have he := determinant_continuity (finiteSection (product A B) n) (finiteSection A n*finiteSection B n)
  have hm1 := (mass_section_le (right_summable hA hB) n).trans (right_mass_le hA hB)
  have hm2 := finite_product_mass hA hB n
  exact he.trans (mul_le_mul (finite_error_mass hA hB n)
    (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
    (mul_nonneg (tsum_nonneg (tailEntry_nonneg A n)) hB.nonneg))

theorem determinant_error_tendsto {A B : Kernel} (hA : Summable (entryNorm A))
    {C : ℝ} (hB : RowBound B C) :
    Tendsto (fun n => (1+finiteSection (product A B) n).det-
      (1+finiteSection A n*finiteSection B n).det) atTop (𝓝 0) := by
  have ht := ((tailMass_tendsto_zero A hA).mul_const C).mul_const (Real.exp (3*(totalMass A*C)))
  have ht' : Tendsto (fun n => tailMass A n*C*Real.exp (3*(totalMass A*C))) atTop (𝓝 0) := by
    simpa only [zero_mul] using ht
  apply squeeze_zero_norm' _ ht'
  exact Eventually.of_forall (fun n => by
    simpa only [Real.norm_eq_abs] using determinant_error_le hA hB n)

theorem finite_product_det_tendsto {A B : Kernel} (hA : Summable (entryNorm A))
    {C : ℝ} (hB : RowBound B C) :
    Tendsto (fun n => (1+finiteSection A n*finiteSection B n).det) atTop
      (𝓝 (detLimit (product A B) (right_summable hA hB))) := by
  have ht := (detLimit_tendsto (product A B) (right_summable hA hB)).sub
    (determinant_error_tendsto hA hB)
  simpa only [sub_sub_cancel,sub_zero] using ht

end
end SpanningTreeIsoperimetry.BoundedKernelProductTail
