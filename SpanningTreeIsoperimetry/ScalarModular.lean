import SpanningTreeIsoperimetry.ScalarResolvent
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Algebra.Polynomial.Degree.Units

/-! Modular construction of the scalar boundary resolvent. -/
namespace SpanningTreeIsoperimetry.ScalarModular

open scoped BigOperators Matrix Classical
open ScalarResolvent Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The endpoint is cyclic: a polynomial of degree below the width cannot
annihilate the actual path operator. -/
theorem aeval_pathOperator_eq_zero {w : ℕ} (hw : 0 < w) {p : Polynomial ℝ}
    (hp : p.natDegree < w) (hz : aeval (pathOperator w) p = 0) : p = 0 := by
  have hdet : (krylovLeading hw (le_refl w)).det ≠ 0 := by
    intro h
    have hs := krylovLeading_det_sq hw (le_refl w)
    rw [h] at hs
    norm_num at hs
  have hu : IsUnit (krylovLeading hw (le_refl w)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hv : (krylovLeading hw (le_refl w)) *ᵥ (fun j : Fin w => p.coeff j.1) = 0 := by
    ext i
    have hentry := congrArg (fun M : Matrix (Fin w) (Fin w) ℝ => M i ⟨0, hw⟩) hz
    rw [aeval_eq_sum_range' hp, ← Fin.sum_univ_eq_sum_range] at hentry
    simpa [Matrix.mulVec, dotProduct, krylovLeading, Matrix.sum_apply,
      Matrix.smul_apply, mul_comm] using hentry
  have hc : (fun j : Fin w => p.coeff j.1) = 0 :=
    Matrix.mulVec_injective_of_isUnit hu (hv.trans (Matrix.mulVec_zero _).symm)
  apply Polynomial.ext
  intro n
  by_cases hn : n < w
  · exact congrFun hc ⟨n, hn⟩
  · simpa using Polynomial.coeff_eq_zero_of_natDegree_lt (p := p) (by omega : p.natDegree < n)

/-- Cayley--Hamilton with the manuscript's explicit denominator. -/
theorem aeval_pathPolynomial (w : ℕ) :
    aeval (pathOperator w) (pathPolynomial w) = 0 := by
  rw [← pathOperator_charpoly]
  exact Matrix.aeval_self_charpoly _

/-- Dirichlet positivity and endpoint cyclicity imply the exact coprimality
needed by the scalar modular algorithm. -/
theorem pathPolynomial_isCoprime_continuant {R w : ℕ} (hR : 0 < R) (hw : 0 < w) :
    IsCoprime (pathPolynomial w) (SmallCases.continuant (X : Polynomial ℝ) R) := by
  apply EuclideanDomain.isCoprime_of_dvd
    (fun h => (pathPolynomial_monic w).ne_zero h.1)
  intro d hd hd0 hdP hdf
  have hdegree : 0 < d.natDegree :=
    Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic (pathPolynomial_monic w) hd hdP
  obtain ⟨a, ha⟩ := hdP
  obtain ⟨b, hb⟩ := hdf
  have ha0 : a ≠ 0 := by
    intro hz
    simp [hz] at ha
    exact (pathPolynomial_monic w).ne_zero ha
  have halow : a.natDegree < w := by
    have hdeg := Polynomial.natDegree_mul hd0 ha0
    rw [← ha, pathPolynomial_natDegree] at hdeg
    omega
  have hprod : SmallCases.continuant (X : Polynomial ℝ) R * a = b * pathPolynomial w := by
    rw [ha, hb]
    ring
  have hmatrix := congrArg (aeval (pathOperator w)) hprod
  simp only [map_mul, aeval_pathPolynomial, mul_zero,
    ← operatorContinuant_eq_aeval] at hmatrix
  have hu : IsUnit (operatorContinuant w R) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (operatorContinuant_det_ne_zero hR w))
  have hzero : aeval (pathOperator w) a = 0 :=
    hu.mul_left_cancel (hmatrix.trans (mul_zero _).symm)
  exact ha0 (aeval_pathOperator_eq_zero hw halow hzero)

/-- A Bezout coefficient for the layer continuant modulo the path polynomial. -/
noncomputable def inverseCoefficient {R w : ℕ} (hR : 0 < R) (hw : 0 < w) : Polynomial ℝ :=
  Classical.choose (pathPolynomial_isCoprime_continuant hR hw).symm

theorem inverseCoefficient_bezout {R w : ℕ} (hR : 0 < R) (hw : 0 < w) :
    ∃ b : Polynomial ℝ,
      inverseCoefficient hR hw * SmallCases.continuant (X : Polynomial ℝ) R +
        b * pathPolynomial w = 1 :=
  Classical.choose_spec (pathPolynomial_isCoprime_continuant hR hw).symm

/-- The reduced polynomial representing the actual boundary Green operator. -/
noncomputable def greenPolynomial {R w : ℕ} (hR : 0 < R) (hw : 0 < w) : Polynomial ℝ :=
  (SmallCases.continuant (X : Polynomial ℝ) (R - 1) * inverseCoefficient hR hw) %ₘ
    pathPolynomial w

theorem inverseCoefficient_aeval {R w : ℕ} (hR : 0 < R) (hw : 0 < w) :
    aeval (pathOperator w) (inverseCoefficient hR hw) = (operatorContinuant w R)⁻¹ := by
  obtain ⟨b, hb⟩ := inverseCoefficient_bezout hR hw
  have hm := congrArg (aeval (pathOperator w)) hb
  simp only [map_add, map_mul, map_one, aeval_pathPolynomial, mul_zero, add_zero,
    ← operatorContinuant_eq_aeval] at hm
  have hu : IsUnit (operatorContinuant w R).det :=
    isUnit_iff_ne_zero.mpr (operatorContinuant_det_ne_zero hR w)
  calc
    aeval (pathOperator w) (inverseCoefficient hR hw) =
        aeval (pathOperator w) (inverseCoefficient hR hw) *
          (operatorContinuant w R * (operatorContinuant w R)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ hu, mul_one]
    _ = _ := by rw [← mul_assoc, hm, one_mul]

theorem greenPolynomial_aeval {R w : ℕ} (hR : 0 < R) (hw : 0 < w) :
    aeval (pathOperator w) (greenPolynomial hR hw) = boundaryGreen hR w := by
  rw [greenPolynomial, aeval_modByMonic_eq_self_of_root (aeval_pathPolynomial w),
    map_mul, inverseCoefficient_aeval, ← operatorContinuant_eq_aeval,
    boundaryGreen_eq_continuants]

theorem pathPolynomial_ne_one {w : ℕ} (hw : 0 < w) : pathPolynomial w ≠ 1 := by
  intro h
  have hd := pathPolynomial_natDegree w
  rw [h, natDegree_one] at hd
  omega

theorem greenPolynomial_natDegree_lt {R w : ℕ} (hR : 0 < R) (hw : 0 < w) :
    (greenPolynomial hR hw).natDegree < w := by
  simpa only [greenPolynomial, pathPolynomial_natDegree] using
    natDegree_modByMonic_lt
      (SmallCases.continuant (X : Polynomial ℝ) (R - 1) * inverseCoefficient hR hw)
      (pathPolynomial_monic w) (pathPolynomial_ne_one hw)

/-- Multiplication by the path operator induces the scalar numerator recurrence. -/
theorem weightedNumerator_mul_pathOperator {w : ℕ} (hw : 0 < w)
    (G : Matrix (Fin w) (Fin w) ℝ) :
    weightedNumerator hw (G * pathOperator w) =
      X * weightedNumerator hw G - pathPolynomial w * C (G ⟨0, hw⟩ ⟨0, hw⟩) := by
  apply Polynomial.funext
  intro z
  simp only [weightedNumerator_eval, eval_sub, eval_mul, eval_X, eval_C]
  let A := (z • (1 : Matrix (Fin w) (Fin w) ℝ) - pathOperator w).adjugate
  have h := Matrix.mul_adjugate (z • (1 : Matrix (Fin w) (Fin w) ℝ) - pathOperator w)
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul,
    shifted_pathOperator_det, ← pathPolynomial_eval] at h
  have hBA : pathOperator w * A = z • A - (pathPolynomial w).eval z • 1 := by
    apply eq_sub_iff_add_eq.mpr
    exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp h).symm
  change ((G * pathOperator w) * A) ⟨0, hw⟩ ⟨0, hw⟩ = _
  rw [Matrix.mul_assoc, hBA, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply]
  rfl

theorem weightedNumerator_one {w : ℕ} (hw : 0 < w) :
    weightedNumerator hw (1 : Matrix (Fin w) (Fin w) ℝ) = pathPolynomial (w - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hw)
  apply Polynomial.funext
  intro z
  rw [weightedNumerator_eval, Matrix.one_mul, shifted_pathOperator,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp [Fin.succAbove_zero, continuantMatrix_tail, continuantMatrix_det, pathPolynomial_eval]

theorem weightedNumerator_add {w : ℕ} (hw : 0 < w)
    (G H : Matrix (Fin w) (Fin w) ℝ) :
    weightedNumerator hw (G + H) = weightedNumerator hw G + weightedNumerator hw H := by
  simp [weightedNumerator, Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem weightedNumerator_smul {w : ℕ} (hw : 0 < w)
    (c : ℝ) (G : Matrix (Fin w) (Fin w) ℝ) :
    weightedNumerator hw (c • G) = C c * weightedNumerator hw G := by
  simp [weightedNumerator, Matrix.smul_apply, map_mul, mul_assoc, Finset.mul_sum]

/-- The adjugate numerator of any polynomial in the path operator has the
expected congruence modulo its actual characteristic polynomial. -/
theorem weightedNumerator_aeval_dvd {w : ℕ} (hw : 0 < w) (p : Polynomial ℝ) :
    pathPolynomial w ∣ weightedNumerator hw (aeval (pathOperator w) p) -
      p * pathPolynomial (w - 1) := by
  induction p using Polynomial.induction_on with
  | C c =>
    rw [aeval_C, Algebra.algebraMap_eq_smul_one, weightedNumerator_smul,
      weightedNumerator_one, sub_self]
    exact dvd_zero _
  | add p q hp hq =>
    rw [map_add, weightedNumerator_add, add_mul]
    convert dvd_add hp hq using 1 <;> ring
  | monomial n c ih =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, weightedNumerator_mul_pathOperator]
    have h := dvd_sub (dvd_mul_of_dvd_right ih (X : Polynomial ℝ))
      (dvd_mul_right (pathPolynomial w) (C ((aeval (pathOperator w)
        (C c * X ^ n)) ⟨0, hw⟩ ⟨0, hw⟩)))
    convert h using 1 <;> ring

/-- The proper adjugate numerator equals the explicit modular remainder. -/
theorem weightedNumerator_aeval_eq_mod {w : ℕ} (hw : 0 < w) (p : Polynomial ℝ) :
    weightedNumerator hw (aeval (pathOperator w) p) =
      (p * pathPolynomial (w - 1)) %ₘ pathPolynomial w := by
  have he := modByMonic_eq_of_dvd_sub (pathPolynomial_monic w)
    (weightedNumerator_aeval_dvd hw p)
  have hdeg : (weightedNumerator hw (aeval (pathOperator w) p)).degree <
      (pathPolynomial w).degree := by
    apply degree_lt_degree
    simpa [pathPolynomial_natDegree] using weightedNumerator_natDegree_lt hw (aeval (pathOperator w) p)
  rwa [(modByMonic_eq_self_iff (pathPolynomial_monic w)).mpr hdeg] at he

/-- The manuscript's modular numerator, attached to the actual Green block. -/
noncomputable def scalarNumerator {R w : ℕ} (hR : 0 < R) (hw : 0 < w) : Polynomial ℝ :=
  (greenPolynomial hR hw * pathPolynomial (w - 1)) %ₘ pathPolynomial w

theorem boundaryGreen_weightedNumerator_eq {R w : ℕ} (hR : 0 < R) (hw : 0 < w) :
    weightedNumerator hw (boundaryGreen hR w) = scalarNumerator hR hw := by
  rw [← greenPolynomial_aeval hR hw, weightedNumerator_aeval_eq_mod, scalarNumerator]

/-- The explicit denominator, now over the manuscript's coefficient field. -/
noncomputable def rationalPathPolynomial (w : ℕ) : Polynomial ℚ :=
  SmallCases.continuant (X - C 4 : Polynomial ℚ) w

private theorem map_continuant {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (x : K) (n : ℕ) :
    f (SmallCases.continuant x n) = SmallCases.continuant (f x) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [SmallCases.continuant]
  | one => simp [SmallCases.continuant]
  | more n ih ih1 => simp only [SmallCases.continuant_recurrence, map_sub, map_mul, ih, ih1]

@[simp] theorem rationalPathPolynomial_map (w : ℕ) :
    (rationalPathPolynomial w).map (algebraMap ℚ ℝ) = pathPolynomial w := by
  change (Polynomial.mapRingHom (algebraMap ℚ ℝ))
    (SmallCases.continuant (X - C 4 : Polynomial ℚ) w) = _
  rw [map_continuant]
  simp [pathPolynomial]

@[simp] theorem rationalContinuant_map (n : ℕ) :
    (SmallCases.continuant (X : Polynomial ℚ) n).map (algebraMap ℚ ℝ) =
      SmallCases.continuant (X : Polynomial ℝ) n := by
  change (Polynomial.mapRingHom (algebraMap ℚ ℝ))
    (SmallCases.continuant (X : Polynomial ℚ) n) = _
  rw [map_continuant]
  simp

theorem rationalPathPolynomial_monic (w : ℕ) : (rationalPathPolynomial w).Monic := by
  apply (algebraMap ℚ ℝ).injective.monic_map_iff.mpr
  rw [rationalPathPolynomial_map]
  exact pathPolynomial_monic w

theorem rationalPathPolynomial_isCoprime_continuant {R w : ℕ}
    (hR : 0 < R) (hw : 0 < w) :
    IsCoprime (rationalPathPolynomial w) (SmallCases.continuant (X : Polynomial ℚ) R) := by
  apply (Polynomial.isCoprime_map (algebraMap ℚ ℝ)).mp
  simpa using pathPolynomial_isCoprime_continuant hR hw

noncomputable def rationalInverseCoefficient {R w : ℕ} (hR : 0 < R) (hw : 0 < w) :
    Polynomial ℚ :=
  Classical.choose (rationalPathPolynomial_isCoprime_continuant hR hw).symm

theorem rationalInverseCoefficient_bezout {R w : ℕ} (hR : 0 < R) (hw : 0 < w) :
    ∃ b : Polynomial ℚ,
      rationalInverseCoefficient hR hw * SmallCases.continuant (X : Polynomial ℚ) R +
        b * rationalPathPolynomial w = 1 :=
  Classical.choose_spec (rationalPathPolynomial_isCoprime_continuant hR hw).symm

noncomputable def rationalGreenPolynomial {R w : ℕ} (hR : 0 < R) (hw : 0 < w) : Polynomial ℚ :=
  (SmallCases.continuant (X : Polynomial ℚ) (R - 1) * rationalInverseCoefficient hR hw) %ₘ
    rationalPathPolynomial w

noncomputable def rationalScalarNumerator {R w : ℕ} (hR : 0 < R) (hw : 0 < w) : Polynomial ℚ :=
  (rationalGreenPolynomial hR hw * rationalPathPolynomial (w - 1)) %ₘ rationalPathPolynomial w

theorem rationalInverseCoefficient_aeval {R w : ℕ} (hR : 0 < R) (hw : 0 < w) :
    aeval (pathOperator w) ((rationalInverseCoefficient hR hw).map (algebraMap ℚ ℝ)) =
      (operatorContinuant w R)⁻¹ := by
  obtain ⟨b, hb⟩ := rationalInverseCoefficient_bezout hR hw
  have hb' := congrArg (Polynomial.map (algebraMap ℚ ℝ)) hb
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one,
    rationalContinuant_map, rationalPathPolynomial_map] at hb'
  have hm := congrArg (aeval (pathOperator w)) hb'
  simp only [map_add, map_mul, map_one, aeval_pathPolynomial, mul_zero, add_zero,
    ← operatorContinuant_eq_aeval] at hm
  have hu : IsUnit (operatorContinuant w R).det :=
    isUnit_iff_ne_zero.mpr (operatorContinuant_det_ne_zero hR w)
  calc
    aeval (pathOperator w) ((rationalInverseCoefficient hR hw).map (algebraMap ℚ ℝ)) =
        aeval (pathOperator w) ((rationalInverseCoefficient hR hw).map (algebraMap ℚ ℝ)) *
          (operatorContinuant w R * (operatorContinuant w R)⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ hu, mul_one]
    _ = _ := by rw [← mul_assoc, hm, one_mul]

/-- Rational modular construction evaluates to the actual Green matrix. -/
theorem rationalGreenPolynomial_aeval {R w : ℕ} (hR : 0 < R) (hw : 0 < w) :
    aeval (pathOperator w) ((rationalGreenPolynomial hR hw).map (algebraMap ℚ ℝ)) =
      boundaryGreen hR w := by
  rw [rationalGreenPolynomial, map_modByMonic _ (rationalPathPolynomial_monic w),
    rationalPathPolynomial_map, aeval_modByMonic_eq_self_of_root (aeval_pathPolynomial w),
    Polynomial.map_mul, rationalContinuant_map, map_mul, rationalInverseCoefficient_aeval,
    ← operatorContinuant_eq_aeval, boundaryGreen_eq_continuants]

/-- The exact rational remainder q is the adjugate numerator of the actual
boundary Green resolvent. -/
theorem rationalScalarNumerator_map {R w : ℕ} (hR : 0 < R) (hw : 0 < w) :
    (rationalScalarNumerator hR hw).map (algebraMap ℚ ℝ) =
      weightedNumerator hw (boundaryGreen hR w) := by
  rw [rationalScalarNumerator, map_modByMonic _ (rationalPathPolynomial_monic w),
    Polynomial.map_mul, rationalPathPolynomial_map, rationalPathPolynomial_map,
    ← weightedNumerator_aeval_eq_mod, rationalGreenPolynomial_aeval]

/-- The scalar ratio uses precisely the manuscript's rational modular q. -/
theorem boundaryGreen_rational_scalar_resolvent {R w : ℕ}
    (hR : 0 < R) (hw : 0 < w) (z : ℝ) :
    (boundaryGreen hR w * (z • (1 : Matrix (Fin w) (Fin w) ℝ) - pathOperator w)⁻¹)
        ⟨0, hw⟩ ⟨0, hw⟩ =
      (rationalScalarNumerator hR hw).eval₂ (algebraMap ℚ ℝ) z /
        (rationalPathPolynomial w).eval₂ (algebraMap ℚ ℝ) z := by
  rw [boundaryGreen_scalar_resolvent, ← rationalScalarNumerator_map hR hw,
    ← rationalPathPolynomial_map w, Polynomial.eval_map, Polynomial.eval_map]

theorem rationalPathPolynomial_natDegree (w : ℕ) :
    (rationalPathPolynomial w).natDegree = w := by
  rw [← natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective,
    rationalPathPolynomial_map, pathPolynomial_natDegree]

theorem rationalScalarNumerator_natDegree_lt {R w : ℕ} (hR : 0 < R) (hw : 0 < w) :
    (rationalScalarNumerator hR hw).natDegree < w := by
  have h := weightedNumerator_natDegree_lt hw (boundaryGreen hR w)
  rw [← rationalScalarNumerator_map hR hw,
    natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective] at h
  exact h

/-- Bezout's coefficient is an inverse in the rational polynomial quotient. -/
theorem rationalInverseCoefficient_mod {R w : ℕ} (hR : 0 < R) (hw : 0 < w) :
    (rationalInverseCoefficient hR hw * SmallCases.continuant (X : Polynomial ℚ) R) %ₘ
      rationalPathPolynomial w = 1 := by
  obtain ⟨b, hb⟩ := rationalInverseCoefficient_bezout hR hw
  have hd : rationalPathPolynomial w ∣
      rationalInverseCoefficient hR hw * SmallCases.continuant (X : Polynomial ℚ) R - 1 := by
    refine ⟨-b, ?_⟩
    linear_combination hb
  have h := modByMonic_eq_of_dvd_sub (rationalPathPolynomial_monic w) hd
  have hdeg : (1 : Polynomial ℚ).degree < (rationalPathPolynomial w).degree := by
    apply degree_lt_degree
    simpa only [natDegree_one, rationalPathPolynomial_natDegree] using hw
  rwa [(modByMonic_eq_self_iff (rationalPathPolynomial_monic w)).mpr hdeg] at h

end SpanningTreeIsoperimetry.ScalarModular
