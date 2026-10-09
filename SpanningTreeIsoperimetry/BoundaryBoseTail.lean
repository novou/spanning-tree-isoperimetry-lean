import SpanningTreeIsoperimetry.BoundaryBoseMoments
import Mathlib.MeasureTheory.Group.Integral

/-! Explicit positive polynomial tails for the Bose moments. -/
namespace SpanningTreeIsoperimetry.BoundaryBoseTail
open MeasureTheory Set Filter BoundaryBoseMoments
open scoped BigOperators Topology
noncomputable section

theorem integral_translate_Ioi (f : ℝ → ℝ) (A : ℝ) :
    (∫ x : ℝ in Ioi A, f x)=∫ x : ℝ in Ioi 0, f (x+A) := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) A).setIntegral_preimage_emb
    (MeasurableEquiv.addRight A).measurableEmbedding f (Ioi A)
  have he : (fun x : ℝ => x+A) ⁻¹' Ioi A=Ioi 0 := by
    ext x
    simp only [mem_preimage,mem_Ioi]
    constructor <;> intro hx <;> linarith
  rw [he] at h
  exact h.symm

def tailPolynomial (m : ℕ) (a A : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m+1), (m.choose j : ℝ)*A^(m-j)*(j.factorial : ℝ)/a^(j+1)

theorem translated_laplace (m : ℕ) (a A x : ℝ) :
    laplaceMoment m a (x+A)=Real.exp (-(a*A))*
      ∑ j ∈ Finset.range (m+1), ((m.choose j : ℝ)*A^(m-j))*laplaceMoment j a x := by
  have he : Real.exp (-(a*(x+A)))=Real.exp (-(a*A))*Real.exp (-(a*x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold laplaceMoment
  rw [he,add_pow,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem integral_laplace_tail (m : ℕ) {a : ℝ} (ha : 0 < a) (A : ℝ) :
    (∫ x : ℝ in Ioi A, laplaceMoment m a x)=Real.exp (-(a*A))*tailPolynomial m a A := by
  rw [integral_translate_Ioi]
  simp_rw [translated_laplace]
  rw [integral_const_mul,integral_finset_sum]
  · simp_rw [integral_const_mul,integral_laplaceMoment _ ha]
    unfold tailPolynomial
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · intro j hj
    exact (laplaceMoment_integrable j ha).const_mul _

theorem bose_tail_pointwise (m : ℕ) {r A x : ℝ} (hr : 0 < r) (hA : 0 < A) (hx : A ≤ x) :
    bose m r x≤(Real.exp (2*r*A)/(Real.exp (2*r*A)-1))*laplaceMoment m (2*r) x := by
  have hx0 : 0 < x := lt_of_lt_of_le hA hx
  have hEA : 1 < Real.exp (2*r*A) := Real.one_lt_exp_iff.mpr (by positivity)
  have hEX : 1 < Real.exp (2*r*x) := Real.one_lt_exp_iff.mpr (by positivity)
  have hle : Real.exp (2*r*A)≤Real.exp (2*r*x) := Real.exp_le_exp.mpr (by nlinarith)
  unfold bose laplaceMoment
  rw [Real.exp_neg]
  have hp : 0≤x^m := pow_nonneg hx0.le _
  have hEA0 : 0 < Real.exp (2*r*A)-1 := by linarith
  have hEX0 : 0 < Real.exp (2*r*x)-1 := by linarith
  have hbase : 1/(Real.exp (2*r*x)-1)≤
      Real.exp (2*r*A)/(Real.exp (2*r*A)-1)*(Real.exp (2*r*x))⁻¹ := by
    rw [← div_eq_mul_inv,div_div,div_le_div_iff₀ hEX0 (mul_pos hEA0 (Real.exp_pos _))]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hbase hp
  convert hm using 1 <;> ring

theorem integral_bose_tail_le (m : ℕ) {r A : ℝ} (hr : 0 < r) (hA : 0 < A) :
    (∫ x : ℝ in Ioi A, bose m r x)≤tailPolynomial m (2*r) A/(Real.exp (2*r*A)-1) := by
  let C := Real.exp (2*r*A)/(Real.exp (2*r*A)-1)
  have hC : 0≤C := by
    have h := Real.one_lt_exp_iff.mpr (show 0 < 2*r*A by positivity)
    unfold C
    positivity
  have hi : IntegrableOn (fun x => C*laplaceMoment m (2*r) x) (Ioi A) :=
    ((laplaceMoment_integrable m (show 0 < 2*r by positivity)).mono_set (Ioi_subset_Ioi hA.le)).const_mul C
  have hb : IntegrableOn (bose m r) (Ioi A) := by
    apply hi.mono'
    · have hm : Measurable (bose m r) := by unfold bose; fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hnon : 0≤bose m r x := by
        unfold bose
        have hx0 := lt_trans hA hx
        have he := Real.one_lt_exp_iff.mpr (show 0 < 2*r*x by positivity)
        positivity
      rw [Real.norm_of_nonneg hnon]
      exact bose_tail_pointwise m hr hA hx.le
  calc
    _≤∫ x : ℝ in Ioi A, C*laplaceMoment m (2*r) x := by
      apply integral_mono_ae hb hi
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      exact bose_tail_pointwise m hr hA hx.le
    _=C*(Real.exp (-(2*r*A))*tailPolynomial m (2*r) A) := by
      rw [integral_const_mul,integral_laplace_tail m (by positivity)]
    _=_ := by
      unfold C
      rw [Real.exp_neg]
      have he : Real.exp (2*r*A)≠0 := (Real.exp_pos _).ne'
      field_simp
      <;> ring

end
end SpanningTreeIsoperimetry.BoundaryBoseTail
