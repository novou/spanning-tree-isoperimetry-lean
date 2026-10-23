module

public import SpanningTreeIsoperimetry.JacobiReduction
public import SpanningTreeIsoperimetry.SignedJacobiChain
public import SpanningTreeIsoperimetry.ScalarModular
public import SpanningTreeIsoperimetry.FiniteBoundaryMinorBridge

@[expose] public section

/-! The manuscript's signed-Euclidean product for the actual corner-strip
counts. All recurrence parameters are derived from the positive Green form. -/
namespace SpanningTreeIsoperimetry.ScalarProduct

open scoped BigOperators Matrix Classical
open ScalarResolvent ScalarModular JacobiReduction JacobiPolynomials SignedJacobiChain Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R w : ℕ} (hR : 0 < R)

theorem jacobi_eq_jacobiMatrix : jacobi (w := w) hR =
    jacobiMatrix (diagonalSequence (w := w) hR) (beta (normSequence (w := w) hR)) w := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [jacobiMatrix, tri, diagonalSequence, i.2]
  · by_cases hn : i.1 + 1 = j.1
    · rw [jacobi_superdiagonal hR hn.symm]
      have hp : j.1 - 1 = i.1 := by omega
      simp [jacobiMatrix, tri, hij, hn, beta, normSequence, j.2, i.2, hp]
    · by_cases hp : j.1 + 1 = i.1
      · rw [jacobi_unitSubdiagonal hR i j hp.symm]
        simp [jacobiMatrix, tri, hij, hn, hp]
      · have hne : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
        have hf : i.1 + 1 < j.1 ∨ j.1 + 1 < i.1 := by omega
        rcases hf with hf | hf
        · rw [jacobi_above hR hf]
          simp [jacobiMatrix, tri, hij, hn, hp]
        · rw [jacobi_upperHessenberg hR i j hf]
          simp [jacobiMatrix, tri, hij, hn, hp]

theorem denominator_eq_tailPolynomial : pathPolynomial w =
    tailPolynomial (diagonalSequence (w := w) hR) (beta (normSequence (w := w) hR)) w := by
  rw [tailPolynomial_eq_charpoly, ← jacobi_eq_jacobiMatrix hR, jacobi_charpoly]

/-- The actual modular numerator is the positive Jacobi mass times the first
trailing characteristic polynomial. -/
theorem numerator_eq_tailPolynomial (hw : 0 < w) :
    weightedNumerator hw (boundaryGreen hR w) =
      C (normSequence (w := w) hR 0) *
        tailPolynomial (fun i => diagonalSequence (w := w) hR (i + 1))
          (fun i => beta (normSequence (w := w) hR) (i + 1)) (w - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hw)
  have hinf : Set.Infinite {z : ℝ | (pathPolynomial (n + 1)).eval z ≠ 0} := by
    simpa only [Polynomial.IsRoot, Set.compl_ofPred] using
      (Polynomial.finite_setOfPred_isRoot (pathPolynomial_monic (n + 1)).ne_zero).infinite_compl
  apply Polynomial.eq_of_infinite_eval_eq
  apply hinf.mono
  intro z hz
  apply (div_left_inj' hz).mp
  rw [← boundaryGreen_scalar_resolvent hR hw z, scalar_resolvent_eq_jacobi hR hw z,
    jacobi_eq_jacobiMatrix hR]
  have hzero : (⟨0, hw⟩ : Fin (n + 1)) = 0 := by apply Fin.ext; rfl
  rw [hzero, JacobiPolynomials.endpoint_resolvent
    (diagonalSequence (w := n + 1) hR) (beta (normSequence (w := n + 1) hR)) n z,
    Polynomial.eval_mul, Polynomial.eval_C, denominator_eq_tailPolynomial hR]
  simp only [normSequence, Nat.zero_lt_succ, dite_true, Nat.succ_sub_one, hzero]
  ring

/-- These are the actual rational quotient leading coefficients from the
paper's signed Euclidean chain, not an independently chosen parameter list. -/
noncomputable def scalarCoefficient (hw : 0 < w) (n : ℕ) : ℚ :=
  quotientLeading (rationalPathPolynomial w) (rationalScalarNumerator hR hw) n

theorem scalarCoefficient_cast (hw : 0 < w) (n : ℕ) (hn : n < w) :
    (algebraMap ℚ ℝ) (scalarCoefficient hR hw n) = weight (normSequence (w := w) hR) n := by
  rw [scalarCoefficient, quotientLeading_map, rationalPathPolynomial_map,
    rationalScalarNumerator_map, denominator_eq_tailPolynomial hR,
    numerator_eq_tailPolynomial hR hw]
  exact quotientLeading_eq_weight (normSequence_pos hR) (diagonalSequence hR) hw n hn

theorem scalarCoefficient_pos (hw : 0 < w) (n : ℕ) (hn : n < w) :
    0 < scalarCoefficient hR hw n := by
  have hp := weight_pos (normSequence_pos (w := w) hR) n
  rw [← scalarCoefficient_cast hR hw n hn] at hp
  change (0 : ℝ) < (scalarCoefficient hR hw n : ℝ) at hp
  exact Rat.cast_pos.mp hp

/-- The actual rational signed chain drops exactly one degree at each step. -/
theorem scalarRemainder_natDegree (hw : 0 < w) (n : ℕ) (hn : n ≤ w) :
    (signedRemainders (rationalPathPolynomial w) (rationalScalarNumerator hR hw) n).natDegree =
      w - n := by
  rw [← Polynomial.natDegree_map (algebraMap ℚ ℝ), signedRemainders_map,
    rationalPathPolynomial_map, rationalScalarNumerator_map,
    denominator_eq_tailPolynomial hR, numerator_eq_tailPolynomial hR hw]
  exact signedRemainders_natDegree (normSequence_pos hR) (diagonalSequence hR) hw n hn

/-- Every nonterminal quotient in the actual rational chain is linear. -/
theorem scalarQuotient_natDegree (hw : 0 < w) (n : ℕ) (hn : n < w) :
    (signedRemainders (rationalPathPolynomial w) (rationalScalarNumerator hR hw) n /
      signedRemainders (rationalPathPolynomial w) (rationalScalarNumerator hR hw) (n + 1)).natDegree = 1 := by
  rw [← Polynomial.natDegree_map (algebraMap ℚ ℝ), Polynomial.map_div,
    signedRemainders_map, signedRemainders_map, rationalPathPolynomial_map,
    rationalScalarNumerator_map, denominator_eq_tailPolynomial hR, numerator_eq_tailPolynomial hR hw]
  exact quotient_natDegree (normSequence_pos hR) (diagonalSequence hR) hw n hn

/-- Product formula for every actual leading Green minor. -/
theorem boundaryGreen_product (hw : 0 < w) {k : ℕ} (hk : k ≤ w) :
    ((boundaryGreen hR w).submatrix (Fin.castLE hk) (Fin.castLE hk)).det =
      ∏ j ∈ Finset.range k, ((scalarCoefficient hR hw j : ℝ)⁻¹) ^ (2 * k - 2 * j - 1) := by
  rw [green_leading_det_eq_prod hR hk]
  calc
    _ = ∏ j ∈ Finset.range k, normSequence (w := w) hR j := by
      rw [← Fin.prod_univ_eq_prod_range]
      apply Finset.prod_congr rfl
      intro i _
      simp only [normSequence, dif_pos (i.2.trans_le hk)]
      congr 1 <;> rfl
    _ = ∏ j ∈ Finset.range k, (weight (normSequence (w := w) hR) j)⁻¹ ^
        (2 * k - 2 * j - 1) := norm_product (normSequence_pos hR) k
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [← scalarCoefficient_cast hR hw j ((Finset.mem_range.mp hj).trans_le hk)]
      rfl

/-- The manuscript's exact product for the actual corner-strip tree count. -/
theorem cornerStrip_product (hw : 0 < w) {k : ℕ} (hk : k ≤ w) :
    (treeCount (cornerStrip (R + 1) (w + 1) k) : ℝ) =
      (treeCount (rectangle (R + 1) (w + 1)) : ℝ) *
        ∏ j ∈ Finset.range k, ((scalarCoefficient hR hw j : ℝ)⁻¹) ^ (2 * k - 2 * j - 1) := by
  rw [CornerStripBridge.cornerStrip_treeCount_eq_greenMinor (by omega : 1 ≤ R)
    (by omega : 1 ≤ w) hk,
    ← FiniteBoundaryMinorBridge.leadingBlock_det_eq_greenMinor hR hk]
  exact congrArg (fun x : ℝ => (treeCount (rectangle (R + 1) (w + 1)) : ℝ) * x)
    (boundaryGreen_product hR hw hk)

end SpanningTreeIsoperimetry.ScalarProduct
