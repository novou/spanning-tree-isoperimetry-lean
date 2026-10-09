import SquareMaximality.Rectangle.Kernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

set_option autoImplicit false

/-!
# The rectangular spectral product

This file evaluates the finite cosine product occurring in the spectrum of
the Laplacian of `pathGraph a □ pathGraph t`.  The zero mode in the second
coordinate cancels the usual factor `t` in the product-of-eigenvalues
formula, leaving the positive product `rectangularSpectralProduct` below.

The main result is an exact logarithmic hyperbolic reduction.  Thus the
formerly bundled `rectangularProductLog` input can be constructed from the
single upstream statement identifying a rectangular cofactor with its
standard cosine spectral product.
-/

namespace SquareMaximality.Rectangle.Product

open Concrete

noncomputable section

namespace Chebyshev

open Polynomial Polynomial.Chebyshev

/-- Factorization of `U_n` by its real cosine roots. -/
theorem eval_U_eq_cosine_product (n : ℕ) (x : ℝ) :
    (U ℝ n).eval x =
      2 ^ n * ∏ k ∈ Finset.range n,
        (x - Real.cos (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1))) := by
  let root : ℕ → ℝ := fun k =>
    Real.cos (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1))
  have hinj : Set.InjOn root (Finset.range n) := by
    exact (Finset.range n).nodup_map_iff_injOn.mp
      (Polynomial.Chebyshev.roots_U_real_nodup n)
  have hcard : (U ℝ n).roots.card = (U ℝ n).natDegree := by
    rw [Polynomial.Chebyshev.natDegree_U_natCast,
      Polynomial.Chebyshev.roots_U_real]
    change (Finset.image root (Finset.range n)).card = n
    rw [Finset.card_image_of_injOn, Finset.card_range]
    exact hinj
  have hsplit : (U ℝ n).Splits := Polynomial.splits_iff_card_roots.mpr hcard
  have heval := hsplit.eval_eq_prod_roots x
  rw [Polynomial.Chebyshev.leadingCoeff_U_natCast,
    Polynomial.Chebyshev.roots_U_real] at heval
  change (U ℝ n).eval x = 2 ^ n * ∏ k ∈ Finset.range n, (x - root k)
  rw [heval]
  change 2 ^ n * ∏ y ∈ Finset.image root (Finset.range n), (x - y) = _
  congr 1
  rw [Finset.prod_image]
  exact hinj

end Chebyshev

/-- The Laplacian eigenvalue indexed by the two path frequencies `j,k`. -/
noncomputable def eigenvalue (a t j k : ℕ) : ℝ :=
  2 * (2 - Real.cos (Real.pi * ((j : ℝ) / (a : ℝ))) -
    Real.cos (Real.pi * ((k : ℝ) / (t : ℝ))))

/-- Product over the second-coordinate frequencies for a fixed nonzero
first-coordinate frequency. -/
noncomputable def eigenRowProduct (a t j : ℕ) : ℝ :=
  ∏ k ∈ Finset.range t, eigenvalue a t j k

/-- Product of the nonzero frequencies in the zero first-coordinate row. -/
noncomputable def zeroRowProduct (t : ℕ) : ℝ :=
  ∏ k ∈ Finset.range (t - 1),
    2 * (1 - Real.cos
      (((k : ℝ) + 1) * Real.pi / (t : ℝ)))

/-- The product of all nonzero rectangular Laplacian eigenvalues, divided by
the number `a*t` of vertices.  The modes are grouped into the zero row and
the rows with `1 ≤ j < a`. -/
noncomputable def fullSpectralTreeProduct (a t : ℕ) : ℝ :=
  ((a : ℝ) * (t : ℝ))⁻¹ * zeroRowProduct t *
    ∏ j ∈ Finset.Ico 1 a, eigenRowProduct a t j

/-- The positive spectral product after cancelling the zero-frequency row
against the normalization in the product-of-nonzero-eigenvalues formula. -/
noncomputable def rectangularSpectralProduct (a t : ℕ) : ℝ :=
  (a : ℝ)⁻¹ * ∏ j ∈ Finset.Ico 1 a, eigenRowProduct a t j

/-- The `a`-dependent factor in the hyperbolic product. -/
noncomputable def spectralBase (a : ℕ) : ℝ :=
  Real.log (a : ℝ)⁻¹ +
    ∑ j ∈ Finset.Ico 1 a,
      Real.log (Real.tanh
        (kernel ((j : ℝ) / (a : ℝ)) / 2))

theorem cosh_kernel (x : ℝ) :
    Real.cosh (kernel x) = 2 - Real.cos (Real.pi * x) := by
  rw [kernel]
  apply Real.cosh_arcosh
  linarith [Real.cos_le_one (Real.pi * x)]

theorem kernel_pos_of_mem_Ico {a j : ℕ} (ha : 0 < a)
    (hj : j ∈ Finset.Ico 1 a) :
    0 < kernel ((j : ℝ) / (a : ℝ)) := by
  rw [Finset.mem_Ico] at hj
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj.1
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hratio : (0 : ℝ) < (j : ℝ) / (a : ℝ) := div_pos hjR haR
  exact lt_of_lt_of_le
    (mul_pos (mul_pos (by norm_num) Concrete.alpha_pos) hratio)
    (Kernel.kernel_chord_lower ha hj.1 hj.2)

/-- The zero-frequency row contributes exactly `t`; this is the familiar
product of the nonzero eigenvalues of a path. -/
theorem zeroRowProduct_eq {t : ℕ} (ht : 0 < t) :
    zeroRowProduct t = (t : ℝ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  have hcheb := Chebyshev.eval_U_eq_cosine_product n (1 : ℝ)
  have hone := Polynomial.Chebyshev.U_eval_one (R := ℝ) (n : ℤ)
  have hprod :
      (∏ k ∈ Finset.range n,
          2 * (1 - Real.cos
            (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1)))) =
        2 ^ n * ∏ k ∈ Finset.range n,
          (1 - Real.cos
            (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1))) := by
    rw [Finset.prod_mul_distrib]
    simp
  rw [zeroRowProduct]
  simp only [Nat.succ_sub_one, Nat.cast_succ]
  rw [hprod, ← hcheb, hone]
  push_cast
  rfl

/-- Hence the grouped full spectral product reduces to the cancelled form
used by `rectangularSpectralProduct`. -/
theorem fullSpectralTreeProduct_eq {a t : ℕ} (ha : 0 < a) (ht : 0 < t) :
    fullSpectralTreeProduct a t = rectangularSpectralProduct a t := by
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  rw [fullSpectralTreeProduct, zeroRowProduct_eq ht,
    rectangularSpectralProduct]
  field_simp

/-- Elementary half-angle identity used to turn the endpoint factor into a
hyperbolic tangent. -/
theorem cosh_sub_one_eq_sinh_mul_tanh_half (z : ℝ) :
    Real.cosh z - 1 = Real.sinh z * Real.tanh (z / 2) := by
  have hz : z = 2 * (z / 2) := by ring
  rw [hz, Real.cosh_two_mul, Real.sinh_two_mul,
    Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh (z / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  field_simp [hc]
  nlinarith [Real.cosh_sq_sub_sinh_sq (z / 2)]

/-- Exponential form of `2 sinh z`. -/
theorem two_mul_sinh_eq_exp_mul_correction (z : ℝ) :
    2 * Real.sinh z = Real.exp z * (1 - Real.exp (-2 * z)) := by
  rw [Real.sinh_eq]
  have he2 : Real.exp z * Real.exp (-2 * z) = Real.exp (-z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_sub, mul_one, he2]
  ring

/-- A complete row of path-frequency eigenvalues is the standard hyperbolic
factor.  This is the finite Chebyshev evaluation behind the rectangular
product formula. -/
theorem eigenRowProduct_eq_hyperbolic {a t j : ℕ} (ht : 0 < t) :
    eigenRowProduct a t j =
      2 * Real.sinh ((t : ℝ) * kernel ((j : ℝ) / (a : ℝ))) *
        Real.tanh (kernel ((j : ℝ) / (a : ℝ)) / 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  let z := kernel ((j : ℝ) / (a : ℝ))
  have hfactor (k : ℕ) :
      eigenvalue a (n + 1) j (k + 1) =
        2 * (Real.cosh z -
          Real.cos (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1))) := by
    simp only [eigenvalue, z]
    rw [cosh_kernel]
    congr 3
    all_goals push_cast; ring_nf
  have hzero : eigenvalue a (n + 1) j 0 = 2 * (Real.cosh z - 1) := by
    simp only [eigenvalue, z, Nat.cast_zero, zero_div, mul_zero, Real.cos_zero]
    rw [cosh_kernel]
  have hinterior :
      (∏ k ∈ Finset.range n, eigenvalue a (n + 1) j (k + 1)) =
        (Polynomial.Chebyshev.U ℝ n).eval (Real.cosh z) := by
    calc
      (∏ k ∈ Finset.range n, eigenvalue a (n + 1) j (k + 1)) =
          ∏ k ∈ Finset.range n,
            2 * (Real.cosh z -
              Real.cos (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1))) := by
                apply Finset.prod_congr rfl
                intro k _hk
                exact hfactor k
      _ = 2 ^ n * ∏ k ∈ Finset.range n,
          (Real.cosh z -
            Real.cos (((k : ℝ) + 1) * Real.pi / ((n : ℝ) + 1))) := by
              rw [Finset.prod_mul_distrib]
              simp
      _ = (Polynomial.Chebyshev.U ℝ n).eval (Real.cosh z) :=
        (Chebyshev.eval_U_eq_cosine_product n (Real.cosh z)).symm
  have hU := Polynomial.Chebyshev.U_real_cosh z (n : ℤ)
  have hU' :
      (Polynomial.Chebyshev.U ℝ n).eval (Real.cosh z) * Real.sinh z =
        Real.sinh (((n + 1 : ℕ) : ℝ) * z) := by
    simpa only [Int.cast_natCast, Int.cast_add, Int.cast_one,
      Nat.cast_add, Nat.cast_one] using hU
  rw [eigenRowProduct, Finset.prod_range_succ', hzero, hinterior,
    cosh_sub_one_eq_sinh_mul_tanh_half]
  change (Polynomial.Chebyshev.U ℝ n).eval (Real.cosh z) *
      (2 * (Real.sinh z * Real.tanh (z / 2))) =
    2 * Real.sinh (((n + 1 : ℕ) : ℝ) * z) * Real.tanh (z / 2)
  rw [← hU']
  ring

theorem tanh_half_pos {z : ℝ} (hz : 0 < z) :
    0 < Real.tanh (z / 2) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)

theorem eigenRowProduct_pos {a t j : ℕ} (ha : 0 < a) (ht : 0 < t)
    (hj : j ∈ Finset.Ico 1 a) :
    0 < eigenRowProduct a t j := by
  have hz := kernel_pos_of_mem_Ico ha hj
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  rw [eigenRowProduct_eq_hyperbolic ht]
  exact mul_pos
    (mul_pos (by norm_num)
      (Real.sinh_pos_iff.mpr (mul_pos htR hz)))
    (tanh_half_pos hz)

/-- Logarithmic form of the row evaluation. -/
theorem log_eigenRowProduct {a t j : ℕ} (ha : 0 < a) (ht : 0 < t)
    (hj : j ∈ Finset.Ico 1 a) :
    Real.log (eigenRowProduct a t j) =
      (t : ℝ) * kernel ((j : ℝ) / (a : ℝ)) +
        Real.log (1 - Real.exp
          (-2 * (t : ℝ) * kernel ((j : ℝ) / (a : ℝ)))) +
        Real.log (Real.tanh
          (kernel ((j : ℝ) / (a : ℝ)) / 2)) := by
  let z := kernel ((j : ℝ) / (a : ℝ))
  let w := (t : ℝ) * z
  have hz : 0 < z := kernel_pos_of_mem_Ico ha hj
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hw : 0 < w := mul_pos htR hz
  have hcorr : 0 < 1 - Real.exp (-2 * w) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith
  have hsinh : 2 * Real.sinh w ≠ 0 := by
    exact ne_of_gt (mul_pos (by norm_num) (Real.sinh_pos_iff.mpr hw))
  have htanh : Real.tanh (z / 2) ≠ 0 := ne_of_gt (tanh_half_pos hz)
  rw [eigenRowProduct_eq_hyperbolic ht]
  change Real.log ((2 * Real.sinh w) * Real.tanh (z / 2)) = _
  rw [Real.log_mul hsinh htanh,
    two_mul_sinh_eq_exp_mul_correction,
    Real.log_mul (ne_of_gt (Real.exp_pos w)) (ne_of_gt hcorr),
    Real.log_exp]
  simp only [w, z]
  congr 3
  ring_nf

theorem rectangularSpectralProduct_pos {a t : ℕ} (ha : 0 < a) (ht : 0 < t) :
    0 < rectangularSpectralProduct a t := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  apply mul_pos (inv_pos.mpr haR)
  exact Finset.prod_pos fun j hj => eigenRowProduct_pos ha ht hj

/-- Exact spectral-to-hyperbolic logarithmic reduction. -/
theorem log_rectangularSpectralProduct {a t : ℕ} (ha : 0 < a) (ht : 0 < t) :
    Real.log (rectangularSpectralProduct a t) =
      Concrete.logProduct spectralBase a t := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hinv : (a : ℝ)⁻¹ ≠ 0 := ne_of_gt (inv_pos.mpr haR)
  have hprod : (∏ j ∈ Finset.Ico 1 a, eigenRowProduct a t j) ≠ 0 := by
    exact ne_of_gt (Finset.prod_pos fun j hj => eigenRowProduct_pos ha ht hj)
  have hlogprod :
      Real.log (∏ j ∈ Finset.Ico 1 a, eigenRowProduct a t j) =
        ∑ j ∈ Finset.Ico 1 a, Real.log (eigenRowProduct a t j) := by
    rw [Real.log_prod]
    intro j hj
    exact ne_of_gt (eigenRowProduct_pos ha ht hj)
  have hrowsum :
      (∑ j ∈ Finset.Ico 1 a, Real.log (eigenRowProduct a t j)) =
        ∑ j ∈ Finset.Ico 1 a,
          ((t : ℝ) * kernel ((j : ℝ) / (a : ℝ)) +
            Real.log (1 - Real.exp
              (-2 * (t : ℝ) * kernel ((j : ℝ) / (a : ℝ)))) +
            Real.log (Real.tanh
              (kernel ((j : ℝ) / (a : ℝ)) / 2))) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact log_eigenRowProduct ha ht hj
  rw [rectangularSpectralProduct, Real.log_mul hinv hprod, hlogprod, hrowsum]
  simp only [Finset.sum_add_distrib]
  simp only [Concrete.logProduct, spectralBase, Concrete.C,
    Concrete.residualPotential]
  rw [Finset.mul_sum]
  ring

end

end SquareMaximality.Rectangle.Product
