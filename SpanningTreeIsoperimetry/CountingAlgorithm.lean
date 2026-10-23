module

public import SpanningTreeIsoperimetry.ScalarProduct
public import SpanningTreeIsoperimetry.LayerDeterminant
public import SpanningTreeIsoperimetry.ScalarResultant

@[expose] public section

/-! Exact rational counting from explicit extended-gcd and signed Euclidean
data. This module does not assert the fast bit-complexity bound or the modular
degree-jump rule. -/
namespace SpanningTreeIsoperimetry.CountingAlgorithm

open scoped BigOperators Matrix Classical
open Polynomial ScalarResolvent ScalarModular ScalarProduct SignedJacobiChain
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Recurrence
variable {K : Type*} [Field K]

def prefixProduct (b : ℕ → K) : ℕ → K
  | 0 => 1
  | n + 1 => b n * prefixProduct b n

def countRecurrence (T : K) (b : ℕ → K) : ℕ → K
  | 0 => T
  | n + 1 => countRecurrence T b n / (b n * prefixProduct b n ^ 2)

theorem prefixProduct_eq_prod (b : ℕ → K) (k : ℕ) :
    prefixProduct b k = ∏ j ∈ Finset.range k, b j := by
  induction k with
  | zero => simp [prefixProduct]
  | succ k ih => rw [prefixProduct, Finset.prod_range_succ, ih, mul_comm]

/-- The batch recurrence is exactly the finite product, even with total
field inversion. Its application to the rational chain uses positive b_j. -/
theorem countRecurrence_eq_product (T : K) (b : ℕ → K) (k : ℕ) :
    countRecurrence T b k = T * ∏ j ∈ Finset.range k, (b j)⁻¹ ^ (2 * k - 2 * j - 1) := by
  induction k with
  | zero => simp [countRecurrence]
  | succ k ih =>
    rw [countRecurrence, ih, prefixProduct_eq_prod]
    have he : (∏ j ∈ Finset.range (k + 1), (b j)⁻¹ ^ (2 * (k + 1) - 2 * j - 1)) =
        ((∏ j ∈ Finset.range k, (b j)⁻¹ ^ (2 * k - 2 * j - 1)) *
          (∏ j ∈ Finset.range k, (b j)⁻¹) ^ 2) * (b k)⁻¹ := by
      rw [Finset.prod_range_succ, show 2 * (k + 1) - 2 * k - 1 = 1 by omega, pow_one]
      congr 1
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j hj
      rw [← pow_add]
      congr 1
      have := Finset.mem_range.mp hj
      omega
    rw [he]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, Finset.prod_inv_distrib]
    ring

end Recurrence

section Bezout
variable {K : Type*} [Field K]

/-- Normalize the explicit extended-gcd coefficient by the constant gcd. -/
noncomputable def normalizedGcdA (f P : Polynomial K) : Polynomial K :=
  C ((EuclideanDomain.gcd f P).coeff 0)⁻¹ * EuclideanDomain.gcdA f P

noncomputable def normalizedGcdB (f P : Polynomial K) : Polynomial K :=
  C ((EuclideanDomain.gcd f P).coeff 0)⁻¹ * EuclideanDomain.gcdB f P

theorem normalizedGcd_bezout (f P : Polynomial K) (hcop : IsCoprime f P) :
    normalizedGcdA f P * f + normalizedGcdB f P * P = 1 := by
  let g := EuclideanDomain.gcd f P
  have hg : IsUnit g := EuclideanDomain.gcd_isUnit_iff.mpr hcop
  have he : g = C (g.coeff 0) := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit hg)
  have hc : g.coeff 0 ≠ 0 := by
    intro hc
    apply hg.ne_zero
    rw [he, hc, C_0]
  have hb := EuclideanDomain.gcd_eq_gcd_ab f P
  change g = _ at hb
  calc
    normalizedGcdA f P * f + normalizedGcdB f P * P =
        C (g.coeff 0)⁻¹ * (f * EuclideanDomain.gcdA f P + P * EuclideanDomain.gcdB f P) := by
      unfold normalizedGcdA normalizedGcdB
      dsimp only [g]
      ring
    _ = C (g.coeff 0)⁻¹ * g := by rw [← hb]
    _ = 1 := by rw [he, coeff_C_zero, ← C_mul, inv_mul_cancel₀ hc, C_1]

/-- Two proved Bezout inverses give the same reduced polynomial. -/
theorem reduced_inverse_unique {f P u v s t : Polynomial K} (hP : P.Monic)
    (hu : u * f + s * P = 1) (hv : v * f + t * P = 1) (a : Polynomial K) :
    (a * u) %ₘ P = (a * v) %ₘ P := by
  apply modByMonic_eq_of_dvd_sub hP
  refine ⟨a * (u * t - v * s), ?_⟩
  have h : u - v = P * (u * t - v * s) := by
    calc
      u - v = u * (v * f + t * P) - v * (u * f + s * P) := by rw [hu, hv]; ring
      _ = _ := by ring
  calc
    a * u - a * v = a * (u - v) := by ring
    _ = _ := by rw [h]; ring

end Bezout

noncomputable def algorithmInverse (R w : ℕ) : Polynomial ℚ :=
  normalizedGcdA (SmallCases.continuant (X : Polynomial ℚ) R) (rationalPathPolynomial w)

noncomputable def algorithmGreen (R w : ℕ) : Polynomial ℚ :=
  (SmallCases.continuant (X : Polynomial ℚ) (R - 1) * algorithmInverse R w) %ₘ
    rationalPathPolynomial w

noncomputable def algorithmNumerator (R w : ℕ) : Polynomial ℚ :=
  (algorithmGreen R w * rationalPathPolynomial (w - 1)) %ₘ rationalPathPolynomial w

noncomputable def algorithmCoefficient (R w n : ℕ) : ℚ :=
  quotientLeading (rationalPathPolynomial w) (algorithmNumerator R w) n

theorem algorithmGreen_eq {R w : ℕ} (hR : 0 < R) (hw : 0 < w) :
    algorithmGreen R w = rationalGreenPolynomial hR hw := by
  obtain ⟨b, hb⟩ := rationalInverseCoefficient_bezout hR hw
  exact reduced_inverse_unique (rationalPathPolynomial_monic w)
    (normalizedGcd_bezout _ _ (rationalPathPolynomial_isCoprime_continuant hR hw).symm) hb _

theorem algorithmNumerator_eq {R w : ℕ} (hR : 0 < R) (hw : 0 < w) :
    algorithmNumerator R w = rationalScalarNumerator hR hw := by
  rw [algorithmNumerator, algorithmGreen_eq hR hw]
  rfl

theorem algorithmCoefficient_eq {R w : ℕ} (hR : 0 < R) (hw : 0 < w) (n : ℕ) :
    algorithmCoefficient R w n = scalarCoefficient hR hw n := by
  rw [algorithmCoefficient, algorithmNumerator_eq hR hw]
  rfl

/-- Rational recurrence initialized by the rectangle count is exact for every
strip, and uses the explicitly normalized extended-gcd numerator. -/
theorem countRecurrence_treeCount {R w k : ℕ} (hR : 0 < R) (hw : 0 < w) (hk : k ≤ w) :
    countRecurrence (treeCount (rectangle (R + 1) (w + 1)) : ℚ)
      (algorithmCoefficient R w) k = (treeCount (cornerStrip (R + 1) (w + 1) k) : ℚ) := by
  apply (Rat.cast_injective (α := ℝ))
  rw [countRecurrence_eq_product]
  push_cast
  rw [cornerStrip_product hR hw hk]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [algorithmCoefficient_eq hR hw]

theorem rectangleFactor_eq_treeCount {R w : ℕ} (hR : 0 < R) (hw : 0 < w) :
    ScalarResultant.rectangleFactor R w = (treeCount (rectangle (R + 1) (w + 1)) : ℚ) := by
  apply (Rat.cast_injective (α := ℝ))
  change (algebraMap ℚ ℝ) (ScalarResultant.rectangleFactor R w) = _
  rw [ScalarResultant.rectangleFactor_cast, rectangleDirichlet_eq_faceMatrix,
    Matrix.det_submatrix_equiv_self, CornerEnergy.foundation_faceIndices]
  have hf := (PrimalDirichlet.treeCount_pair_eq_dirichlet (by omega : 1 ≤ R) (by omega : 1 ≤ w)
    (CornerStripBridge.cornerStrip_hull (k := 0) (by omega : 1 ≤ R) (Nat.zero_le w))
    (CornerStripBridge.cornerStrip_connected (k := 0) (by omega : 1 ≤ R) (Nat.zero_le w))
    (CornerStripBridge.cornerStrip_no_interior (k := 0) (Nat.zero_le w))).1
  simpa only [Rat.cast_natCast] using hf.symm

/-- Complete scalar rational computation from R,w,k: a resultant, one
normalized extended gcd, the signed Euclidean chain, and prefix updates. -/
noncomputable def algorithmCount (R w k : ℕ) : ℚ :=
  countRecurrence (ScalarResultant.rectangleFactor R w) (algorithmCoefficient R w) k

theorem algorithmCount_eq_treeCount {R w k : ℕ}
    (hR : 0 < R) (hw : 0 < w) (hk : k ≤ w) :
    algorithmCount R w k = (treeCount (cornerStrip (R + 1) (w + 1) k) : ℚ) := by
  rw [algorithmCount, rectangleFactor_eq_treeCount hR hw]
  exact countRecurrence_treeCount hR hw hk

end SpanningTreeIsoperimetry.CountingAlgorithm
