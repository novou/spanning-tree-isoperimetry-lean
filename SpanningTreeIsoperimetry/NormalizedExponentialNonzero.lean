module

public import SpanningTreeIsoperimetry.NormalizedExponentialInverse

@[expose] public section

/-! The actual normalized exponential kernel has an explicitly entrywise
summable inverse perturbation, so its finite-section determinant limit is
nonzero. No determinant identity or sign is assumed. -/
namespace SpanningTreeIsoperimetry.NormalizedExponentialNonzero
open NormalizedExponentialInverse OneSidedLaurentCompatibility
open ToeplitzHankelKernels LaurentConvolutionAlgebra ToeplitzHankelMassBounds
open WeightedPowerSeries SummableKernelProduct AbsolutelySummableDeterminant
open BoundedKernelProduct BoundedKernelAlgebra SummableKernelDeterminant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def perturbation (V : PowerSeries ℝ) (t : ℝ) : Kernel := C V t-identity
def inversePerturbation (V : PowerSeries ℝ) (t : ℝ) : Kernel :=
  -product (inverse V t) (perturbation V t)

theorem perturbation_summable {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (t : ℝ) : Summable (entryNorm (perturbation V t)) :=
  NormalizedToeplitzFactorization.C_difference_summable
    (positive_weighted hV0 hV t) (positive_weighted hV0 hV (-t))
    (positive_support V t) (positive_support V (-t)) (positive_inverse hV0 hV t)

theorem inversePerturbation_summable {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (t : ℝ) : Summable (entryNorm (inversePerturbation V t)) := by
  have h := left_summable (column_inverse hV0 hV t) (perturbation_summable hV0 hV t)
  change Summable (fun p : ℕ×ℕ => |product (inverse V t) (perturbation V t) p.1 p.2|) at h
  change Summable (fun p : ℕ×ℕ => abs (-(product (inverse V t) (perturbation V t) p.1 p.2)))
  simpa only [abs_neg] using h

private theorem row_identity : RowBound identity 1 := by
  simpa only [weightedMass_unit] using rowBound_T_weighted weighted_unit

private theorem row_of_summable {A : Kernel} (hA : Summable (entryNorm A)) :
    RowBound A (totalMass A) := by
  refine ⟨totalMass_nonneg A,row_summable hA,?_⟩
  intro i
  exact tsum_comp_le_tsum_of_inj hA (fun _ => abs_nonneg _)
    (show Function.Injective (fun j : ℕ => (i,j)) by intro j k h; exact congrArg Prod.snd h)

private theorem entry_summable {A B : Kernel} {a b : ℝ}
    (hA : RowBound A a) (hB : RowBound B b) (i j : ℕ) :
    Summable (fun k => A i k*B k j) :=
  (BoundedKernelAlgebra.entry_product_summable hA hB i j).of_abs

private theorem product_sub_right {A B D : Kernel} {a b d : ℝ}
    (hA : RowBound A a) (hB : RowBound B b) (hD : RowBound D d) :
    product A (B-D)=product A B-product A D := by
  ext i j
  simp only [product,Pi.sub_apply,mul_sub]
  exact (entry_summable hA hB i j).tsum_sub (entry_summable hA hD i j)

private theorem product_sub_left {A B D : Kernel} {a b d : ℝ}
    (hA : RowBound A a) (hB : RowBound B b) (hD : RowBound D d) :
    product (A-B) D=product A D-product B D := by
  ext i j
  simp only [product,Pi.sub_apply,sub_mul]
  exact (entry_summable hA hD i j).tsum_sub (entry_summable hB hD i j)

/-- The explicitly summable formula is exactly C inverse minus identity. -/
theorem inversePerturbation_eq {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (t : ℝ) : inversePerturbation V t=inverse V t-identity := by
  have he : product (inverse V t) (perturbation V t)=identity-inverse V t := by
    rw [perturbation,product_sub_right (row_inverse hV0 hV t) (row_C hV0 hV t) row_identity,
      left_inverse hV0 hV t,unit_right]
  rw [inversePerturbation,he]
  abel

/-- The actual summable perturbations multiply to the identity. -/
theorem compose_inverse {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (t : ℝ) :
    composePerturbation (perturbation V t) (inversePerturbation V t)=0 := by
  have hj := row_of_summable (inversePerturbation_summable hV0 hV t)
  have hCJ : product (C V t) (inversePerturbation V t)=identity-C V t := by
    rw [inversePerturbation_eq hV0 hV t,
      product_sub_right (row_C hV0 hV t) (row_inverse hV0 hV t) row_identity,
      right_inverse hV0 hV t,unit_right]
  have hprod : product (perturbation V t) (inversePerturbation V t)=
      identity-C V t-inversePerturbation V t := by
    rw [perturbation,product_sub_left (row_C hV0 hV t) row_identity hj,unit_left,hCJ]
  unfold composePerturbation
  rw [hprod]
  unfold perturbation
  ext i j
  simp only [Pi.sub_apply,Pi.add_apply,Pi.zero_apply]
  ring

/-- Nonvanishing for every real deformation parameter, obtained from the
actual bounded inverse and its summable perturbation. -/
theorem determinant_ne_zero {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (t : ℝ) :
    detLimit (perturbation V t) (perturbation_summable hV0 hV t)≠0 :=
  (inverse_pair_nonzero (perturbation_summable hV0 hV t)
    (inversePerturbation_summable hV0 hV t) (compose_inverse hV0 hV t)).1

end
end SpanningTreeIsoperimetry.NormalizedExponentialNonzero
