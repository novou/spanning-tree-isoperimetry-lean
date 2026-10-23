module

public import SpanningTreeIsoperimetry.PotentialKernelHarmonic

@[expose] public section

/-! Finite evaluation of the one-dimensional diagonal integral. The identity
is valid also where sin x=0, and introduces no unproved potential-kernel
identification; that separate reduction will use this evaluation. -/
namespace SpanningTreeIsoperimetry.PotentialDiagonalSine
open MeasureTheory
open scoped BigOperators
noncomputable section

def oddHarmonic (j : ℕ) : ℝ := ∑ i ∈ Finset.range j,1/(2*(i : ℝ)+1)

theorem cosine_step (i : ℕ) (x : ℝ) :
    Real.cos (2*(i : ℝ)*x)-Real.cos (2*((i : ℝ)+1)*x)=
      2*Real.sin x*Real.sin ((2*(i : ℝ)+1)*x) := by
  have hm : 2*(i : ℝ)*x=(2*(i : ℝ)+1)*x-x := by ring
  have hp : 2*((i : ℝ)+1)*x=(2*(i : ℝ)+1)*x+x := by ring
  rw [hm,hp,Real.cos_sub,Real.cos_add]
  ring

theorem telescoping_sine_sum (j : ℕ) (x : ℝ) :
    2*Real.sin x*(∑ i ∈ Finset.range j,Real.sin ((2*(i : ℝ)+1)*x))=
      1-Real.cos (2*(j : ℝ)*x) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ,mul_add,ih]
    have h := cosine_step j x
    push_cast
    linarith only [h]

/-- Exact finite identity, including the removable denominator-zero cases. -/
theorem sine_quotient_eq_sum (j : ℕ) (x : ℝ) :
    (1-Real.cos (2*(j : ℝ)*x))/Real.sin x=
      2*∑ i ∈ Finset.range j,Real.sin ((2*(i : ℝ)+1)*x) := by
  by_cases hx : Real.sin x=0
  · have hz (i : ℕ) : Real.sin ((2*(i : ℝ)+1)*x)=0 := by
      have h := BoundaryKernelBounds.abs_sin_nat_mul_le (2*i+1) x
      simp only [hx,abs_zero,mul_zero] at h
      push_cast at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    simp only [hx,div_zero,hz,Finset.sum_const_zero,mul_zero]
  · apply (div_eq_iff hx).mpr
    have h := telescoping_sine_sum j x
    nlinarith only [h]

theorem integral_odd_sine (i : ℕ) :
    (∫ x in (0 : ℝ)..Real.pi,Real.sin ((2*(i : ℝ)+1)*x))=2/(2*(i : ℝ)+1) := by
  have hn : 2*(i : ℝ)+1≠0 := by positivity
  have hc : Real.cos ((2*(i : ℝ)+1)*Real.pi)= -1 := by
    have he : 2*(i : ℝ)+1=((2*i+1 : ℕ) : ℝ) := by push_cast; ring
    rw [he,Real.cos_nat_mul_pi]
    norm_num [pow_add,pow_mul]
  rw [intervalIntegral.integral_comp_mul_left _ hn,integral_sin]
  simp only [mul_zero,Real.cos_zero,hc,smul_eq_mul]
  ring

def diagonalIntegral (j : ℕ) : ℝ :=
  (1/Real.pi)*∫ x in (0 : ℝ)..Real.pi,(1-Real.cos (2*(j : ℝ)*x))/Real.sin x

theorem diagonalIntegral_eq (j : ℕ) : diagonalIntegral j=(4/Real.pi)*oddHarmonic j := by
  unfold diagonalIntegral
  simp_rw [sine_quotient_eq_sum]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finsetSum]
  · simp_rw [integral_odd_sine]
    have hs : (∑ i ∈ Finset.range j,2/(2*(i : ℝ)+1))=2*oddHarmonic j := by
      rw [oddHarmonic,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs]
    ring
  · intro i _
    exact (show Continuous (fun x : ℝ => Real.sin ((2*(i : ℝ)+1)*x)) by fun_prop).intervalIntegrable _ _

end
end SpanningTreeIsoperimetry.PotentialDiagonalSine
