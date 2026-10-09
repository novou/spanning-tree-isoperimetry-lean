import SpanningTreeIsoperimetry.FoundationsBridge
import SpanningTreeIsoperimetry.EpsilonBounds
import SquareMaximality.Paper
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The area–boundary comparison for rectangles

The logarithmic interpolation below is the hyperbolic product in Appendix A,
written in its exponential normalization. Its agreement with actual spanning-
tree counts follows from the included, closed Matrix–Tree and spectral proofs.
The current manuscript's stronger area–boundary comparison is developed here;
the older bulk-only rectangular penalty is not treated as its proof.
-/

namespace SpanningTreeIsoperimetry.RectangularComparison

open SquareMaximality SquareMaximality.Rectangle
open scoped BigOperators

noncomputable section

/-- The residual sum for a real long side. -/
def realResidual (r : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico 1 r,
    Real.log (1 - Real.exp (-2 * t * Concrete.kernel ((j : ℝ) / r)))

/-- The rectangular logarithmic tree-count interpolation. -/
def ell (r : ℕ) (t : ℝ) : ℝ :=
  Product.spectralBase r + t * Concrete.C r + realResidual r t

/-- The normalized remainder `D_r(t)` from Appendix A. -/
def remainder (r : ℕ) (t : ℝ) : ℝ :=
  squareLatticeEntropy * r * t - Concrete.alpha * (r + t) - ell r t

@[simp] theorem realResidual_nat (r s : ℕ) :
    realResidual r s = Concrete.residualPotential r s := rfl

@[simp] theorem ell_nat (r s : ℕ) :
    ell r s = Concrete.logProduct Product.spectralBase r s := rfl

/-- At every positive integer pair, the interpolation is the actual log count. -/
theorem ell_nat_eq_log_treeCount {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    ell r s = Real.log (SpanningTreeIsoperimetry.treeCount
      (SpanningTreeIsoperimetry.rectangle r s) : ℝ) := by
  rw [rectangle_treeCount_eq_foundation]
  let hMT := rectangleCofactorInput_of_labeledMatrixTree labeledMultigraphCofactorInput
  rw [ProductInputs.log_tauRect_eq_spectral hMT
    (Spectral.rectangularSpectralCofactor hMT) hr hs,
    Product.log_rectangularSpectralProduct hr hs]
  rfl

/-- The correction appearing in the equal-area pairing. -/
def stretchCorrection (v z : ℝ) : ℝ :=
  Real.log (1 - Real.exp (-2 * v * z)) - Real.log (1 - Real.exp (-2 * z))

private theorem correction_arg_pos {z : ℝ} (hz : 0 < z) :
    0 < 1 - Real.exp (-2 * z) := by
  rw [sub_pos, Real.exp_lt_one_iff]
  linarith

theorem stretchCorrection_pos {v z : ℝ} (hv : 1 < v) (hz : 0 < z) :
    0 < stretchCorrection v z := by
  unfold stretchCorrection
  apply sub_pos.mpr
  apply Real.log_lt_log (correction_arg_pos hz)
  apply sub_lt_sub_left
  apply Real.exp_lt_exp.mpr
  nlinarith

/-- Strict convexity of the exponential controls the derivative of the
stretch correction, with no numerical approximation. -/
private theorem exp_stretch_strict {v x : ℝ} (hv : 1 < v) (hx : 0 < x) :
    v * (Real.exp x - 1) < Real.exp (v * x) - 1 := by
  have hv0 : 0 < v := by linarith
  have h := strictConvexOn_exp.2
    (show (0 : ℝ) ∈ Set.univ from trivial)
    (show v * x ∈ Set.univ from trivial)
    (ne_of_lt (mul_pos hv0 hx))
    (show 0 < 1 - 1 / v by rw [sub_pos, div_lt_one hv0]; exact hv)
    (show 0 < 1 / v from div_pos zero_lt_one hv0)
    (show 1 - 1 / v + 1 / v = 1 by ring)
  have harg : (1 - 1 / v) * (0 : ℝ) + (1 / v) * (v * x) = x := by
    field_simp
    ring
  simp only [smul_eq_mul, harg, Real.exp_zero, mul_one] at h
  have hm := mul_lt_mul_of_pos_left h hv0
  field_simp at hm
  nlinarith

private theorem hasDerivAt_logCorrection {a z : ℝ} (ha : 0 < a) (hz : 0 < z) :
    HasDerivAt (fun x => Real.log (1 - Real.exp (-2 * a * x)))
      (2 * a / (Real.exp (2 * a * z) - 1)) z := by
  have hlin : HasDerivAt (fun x : ℝ => -2 * a * x) (-2 * a) z := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id z).const_mul (-2 * a)
  have hpos : 0 < 1 - Real.exp (-2 * a * z) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    nlinarith
  have hder := ((hasDerivAt_const z 1).sub hlin.exp).log (ne_of_gt hpos)
  change HasDerivAt (fun x => Real.log (1 - Real.exp (-2 * a * x)))
    ((0 - Real.exp (-2 * a * z) * (-2 * a)) /
      (1 - Real.exp (-2 * a * z))) z at hder
  convert hder using 1
  have hp : Real.exp (2 * a * z) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hm : Real.exp (2 * a * z) - 1 ≠ 0 := by
    apply ne_of_gt
    rw [sub_pos, Real.one_lt_exp_iff]
    positivity
  rw [show -2 * a * z = -(2 * a * z) by ring, Real.exp_neg]
  field_simp
  ring

private theorem hasDerivAt_stretchCorrection {v z : ℝ}
    (hv : 0 < v) (hz : 0 < z) :
    HasDerivAt (stretchCorrection v)
      (2 * v / (Real.exp (2 * v * z) - 1) -
       2 / (Real.exp (2 * z) - 1)) z := by
  have h := (hasDerivAt_logCorrection hv hz).sub
    (hasDerivAt_logCorrection (a := 1) zero_lt_one hz)
  convert h using 1 <;> simp only [mul_one]
  funext x
  rfl

/-- The pairing kernel in Appendix A is strictly decreasing in its argument. -/
theorem stretchCorrection_strictAntiOn {v : ℝ} (hv : 1 < v) :
    StrictAntiOn (stretchCorrection v) (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ))
  · intro z hz
    exact (hasDerivAt_stretchCorrection (by linarith) hz).continuousAt.continuousWithinAt
  · intro z hz
    have hz0 : 0 < z := by simpa only [interior_Ioi, Set.mem_Ioi] using hz
    rw [(hasDerivAt_stretchCorrection (by linarith) hz0).deriv]
    have h1 : 0 < Real.exp (2 * z) - 1 := by
      rw [sub_pos, Real.one_lt_exp_iff]
      linarith
    have h2 : 0 < Real.exp (2 * v * z) - 1 := by
      rw [sub_pos, Real.one_lt_exp_iff]
      have : 0 < v := by linarith
      positivity
    apply sub_neg.mpr
    rw [div_lt_div_iff₀ h2 h1]
    have h := exp_stretch_strict hv (show 0 < 2 * z by linarith)
    rw [show v * (2 * z) = 2 * v * z by ring] at h
    nlinarith

/-- The floor-index matching in the equal-area comparison. -/
def matchingIndex (r n j : ℕ) : ℕ := j * n / r

private theorem matchingIndex_strictMono {r n : ℕ} (hr : 0 < r) (hrn : r ≤ n) :
    StrictMono (matchingIndex r n) := by
  intro j k hjk
  have hfloor := Nat.div_mul_le_self (j * n) r
  have hstep : (j * n / r + 1) * r ≤ k * n := by
    have := Nat.mul_le_mul_right n (show j + 1 ≤ k by omega)
    nlinarith
  have h := (Nat.le_div_iff_mul_le hr).mpr hstep
  exact h

private theorem matchingIndex_mem {r n j : ℕ} (hr : 0 < r) (hrn : r ≤ n)
    (hj : j ∈ Finset.Ico 1 r) : matchingIndex r n j ∈ Finset.Ico 1 n := by
  obtain ⟨hj1, hjr⟩ := Finset.mem_Ico.mp hj
  apply Finset.mem_Ico.mpr
  constructor
  · apply (Nat.le_div_iff_mul_le hr).mpr
    nlinarith
  · apply (Nat.div_lt_iff_lt_mul hr).mpr
    nlinarith

private theorem matchingIndex_lt_last {r n j : ℕ} (hr : 0 < r) (hrn : r < n)
    (hj : j ∈ Finset.Ico 1 r) : matchingIndex r n j < n - 1 := by
  obtain ⟨hj1, hjr⟩ := Finset.mem_Ico.mp hj
  apply (Nat.div_lt_iff_lt_mul hr).mpr
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hmul := Nat.mul_le_mul_right n (show j + 1 ≤ r by omega)
  nlinarith

private theorem kernel_argument_pos {n k : ℕ} (hn : 0 < n)
    (hk : k ∈ Finset.Ico 1 n) :
    0 < Concrete.kernel ((k : ℝ) / n) :=
  Product.kernel_pos_of_mem_Ico hn hk

/-- Every term of the shorter correction sum pairs with a term of the
longer one, and the last term of the longer sum remains unpaired. -/
theorem equal_area_correction_strict {r n : ℕ} (hr : 0 < r) (hrn : r < n) :
    (∑ j ∈ Finset.Ico 1 r,
      stretchCorrection ((n : ℝ) / r) (n * Concrete.kernel ((j : ℝ) / r))) <
    ∑ k ∈ Finset.Ico 1 n,
      stretchCorrection ((n : ℝ) / r) (r * Concrete.kernel ((k : ℝ) / n)) := by
  have hn : 0 < n := lt_trans hr hrn
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrnR : (r : ℝ) < n := by exact_mod_cast hrn
  have hv : 1 < (n : ℝ) / r := (one_lt_div hrR).mpr hrnR
  let f : ℕ → ℝ := fun k =>
    stretchCorrection ((n : ℝ) / r) (r * Concrete.kernel ((k : ℝ) / n))
  let selected := (Finset.Ico 1 r).image (matchingIndex r n)
  have hsubset : selected ⊆ Finset.Ico 1 n := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    exact matchingIndex_mem hr hrn.le hj
  have hpair (j : ℕ) (hj : j ∈ Finset.Ico 1 r) :
      stretchCorrection ((n : ℝ) / r) (n * Concrete.kernel ((j : ℝ) / r)) ≤
        f (matchingIndex r n j) := by
    have hk := matchingIndex_mem hr hrn.le hj
    have hjpos := kernel_argument_pos hr hj
    have hkpos := kernel_argument_pos hn hk
    have hfloor : (matchingIndex r n j : ℝ) * r ≤ (j : ℝ) * n := by
      exact_mod_cast Nat.div_mul_le_self (j * n) r
    have hfrac : (matchingIndex r n j : ℝ) / n ≤ (j : ℝ) / r := by
      exact (div_le_div_iff₀ hnR hrR).mpr hfloor
    have hkarg : (matchingIndex r n j : ℝ) / n ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · apply (div_le_one hnR).mpr
        exact_mod_cast (Finset.mem_Ico.mp hk).2.le
    have hjarg : (j : ℝ) / r ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · apply (div_le_one hrR).mpr
        exact_mod_cast (Finset.mem_Ico.mp hj).2.le
    have hkernel := Kernel.kernel_monotoneOn hkarg hjarg hfrac
    have hscaled : (r : ℝ) * Concrete.kernel ((matchingIndex r n j : ℝ) / n) ≤
        n * Concrete.kernel ((j : ℝ) / r) := by
      nlinarith
    exact (stretchCorrection_strictAntiOn hv).antitoneOn
      (mul_pos hrR hkpos) (mul_pos hnR hjpos) hscaled
  have hsum :
      (∑ j ∈ Finset.Ico 1 r,
        stretchCorrection ((n : ℝ) / r) (n * Concrete.kernel ((j : ℝ) / r))) ≤
      ∑ k ∈ selected, f k := by
    rw [show selected = (Finset.Ico 1 r).image (matchingIndex r n) from rfl,
      Finset.sum_image (matchingIndex_strictMono hr hrn.le).injective.injOn]
    exact Finset.sum_le_sum hpair
  have hlast : n - 1 ∈ Finset.Ico 1 n := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hmissing : n - 1 ∉ selected := by
    intro hm
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hm
    have h := matchingIndex_lt_last hr hrn hj
    omega
  have hpositive (k : ℕ) (hk : k ∈ Finset.Ico 1 n) : 0 < f k :=
    stretchCorrection_pos hv (mul_pos hrR (kernel_argument_pos hn hk))
  exact lt_of_le_of_lt hsum (Finset.sum_lt_sum_of_subset hsubset hlast hmissing
    (hpositive _ hlast) (fun k hk _ => (hpositive k hk).le))

private theorem realResidual_stretch (a : ℕ) (v t : ℝ) :
    realResidual a (v * t) - realResidual a t =
      ∑ j ∈ Finset.Ico 1 a,
        stretchCorrection v (t * Concrete.kernel ((j : ℝ) / a)) := by
  unfold realResidual
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold stretchCorrection
  congr 2 <;> congr 1 <;> ring

private theorem ell_integer_symmetry {r n : ℕ} (hr : 0 < r) (hn : 0 < n) :
    ell r n = ell n r := by
  rw [ell_nat_eq_log_treeCount hr hn, ell_nat_eq_log_treeCount hn hr,
    rectangle_treeCount_eq_foundation, rectangle_treeCount_eq_foundation,
    tauRect_comm]

/-- The intermediate rectangle gives the exact equal-area identity printed
in Appendix A. -/
theorem equal_area_identity {r n : ℕ} (hr : 0 < r) (hn : 0 < n) :
    ell n n - ell r ((n : ℝ) ^ 2 / r) =
      ((n : ℝ) / r - 1) * (r * Concrete.C n - n * Concrete.C r) +
      ((∑ k ∈ Finset.Ico 1 n,
          stretchCorrection ((n : ℝ) / r) (r * Concrete.kernel ((k : ℝ) / n))) -
       (∑ j ∈ Finset.Ico 1 r,
          stretchCorrection ((n : ℝ) / r) (n * Concrete.kernel ((j : ℝ) / r)))) := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  have hfirst := realResidual_stretch n ((n : ℝ) / r) r
  have hsecond := realResidual_stretch r ((n : ℝ) / r) n
  rw [div_mul_cancel₀ _ hr0] at hfirst
  rw [show (n : ℝ) / r * n = (n : ℝ) ^ 2 / r by ring] at hsecond
  rw [← hfirst, ← hsecond]
  have hmid := ell_integer_symmetry hr hn
  unfold ell at hmid ⊢
  field_simp
  have hm := congrArg (fun z : ℝ => z * r) hmid
  nlinarith

/-- At equal area, a strictly shorter first side has strictly larger
normalized remainder. This is a closed analytic theorem for the actual
rectangular product, including nonintegral interpolated long sides. -/
theorem equal_area_remainder_strict {r n : ℕ} (hr : 0 < r) (hrn : r < n) :
    remainder n n < remainder r ((n : ℝ) ^ 2 / r) := by
  have hn : 0 < n := lt_trans hr hrn
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrnR : (r : ℝ) < n := by exact_mod_cast hrn
  have hv : 0 < (n : ℝ) / r - 1 := sub_pos.mpr ((one_lt_div hrR).mpr hrnR)
  have heps := Trapezoid.SharpTrapezoidFormula.epsilon_scaled_antitone
    SharpTrapezoid.sharpTrapezoidFormula hr hrn.le
  have hC : Concrete.alpha * ((n : ℝ) - r) ≤
      r * Concrete.C n - n * Concrete.C r := by
    unfold Concrete.epsilon at heps
    nlinarith
  have hCscaled := mul_le_mul_of_nonneg_left hC hv.le
  have hGamma := equal_area_correction_strict hr hrn
  have hidentity := equal_area_identity hr hn
  have hfactor : ((n : ℝ) / r - 1) * (Concrete.alpha * ((n : ℝ) - r)) =
      Concrete.alpha * ((r : ℝ) + (n : ℝ) ^ 2 / r - 2 * n) := by
    field_simp
    ring
  rw [hfactor] at hCscaled
  have hell : Concrete.alpha * ((r : ℝ) + (n : ℝ) ^ 2 / r - 2 * n) <
      ell n n - ell r ((n : ℝ) ^ 2 / r) := by linarith
  have harea : squareLatticeEntropy * r * ((n : ℝ) ^ 2 / r) =
      squareLatticeEntropy * n * n := by
    field_simp <;> ring
  unfold remainder
  rw [harea]
  nlinarith

/-- The strong rectangular comparison is completely proved on the equal-area
locus, with the full boundary coefficient retained. -/
theorem equal_area_comparison_strict {r s n : ℕ}
    (hr : 0 < r) (hn : 0 < n) (hrn : r < n) (harea : r * s = n ^ 2) :
    Real.log (SpanningTreeIsoperimetry.treeCount
        (SpanningTreeIsoperimetry.rectangle r s) : ℝ) -
      Real.log (SpanningTreeIsoperimetry.treeCount
        (SpanningTreeIsoperimetry.rectangle n n) : ℝ) <
      -Concrete.alpha * ((r : ℝ) + s - 2 * n) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hareaR : (r : ℝ) * s = (n : ℝ) ^ 2 := by exact_mod_cast harea
  have hs : 0 < s := by nlinarith
  have hsreal : (n : ℝ) ^ 2 / r = s := by
    apply (div_eq_iff (ne_of_gt hrR)).mpr
    nlinarith
  have h := equal_area_remainder_strict hr hrn
  rw [hsreal] at h
  unfold remainder at h
  rw [ell_nat_eq_log_treeCount hn hn, ell_nat_eq_log_treeCount hr hs] at h
  have hscaled : squareLatticeEntropy * r * s = squareLatticeEntropy * n * n := by
    calc
      squareLatticeEntropy * r * s = squareLatticeEntropy * ((r : ℝ) * s) := by ring
      _ = squareLatticeEntropy * ((n : ℝ) ^ 2) := by rw [hareaR]
      _ = squareLatticeEntropy * n * n := by ring
  rw [hscaled] at h
  linarith

private theorem alpha_eq_log : Concrete.alpha = Real.log (1 + Real.sqrt 2) := by
  rw [← Concrete.exp_alpha, Real.log_exp]

private theorem rectangularLog_comm {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    Real.log (SpanningTreeIsoperimetry.treeCount
        (SpanningTreeIsoperimetry.rectangle r s) : ℝ) =
      Real.log (SpanningTreeIsoperimetry.treeCount
        (SpanningTreeIsoperimetry.rectangle s r) : ℝ) := by
  rw [← ell_nat_eq_log_treeCount hr hs, ← ell_nat_eq_log_treeCount hs hr]
  exact ell_integer_symmetry hr hs

/-- Every nonsquare rectangle of square area satisfies the strict boundary
comparison, regardless of its orientation. -/
theorem equal_area_strict {r s n : ℕ} (hr : 0 < r) (hs : 0 < s) (hn : 0 < n)
    (harea : r * s = n ^ 2) (hne : (r, s) ≠ (n, n)) :
    Real.log (SpanningTreeIsoperimetry.treeCount
        (SpanningTreeIsoperimetry.rectangle r s) : ℝ) -
      Real.log (SpanningTreeIsoperimetry.treeCount
        (SpanningTreeIsoperimetry.rectangle n n) : ℝ) <
      -Real.log (1 + Real.sqrt 2) * ((r : ℝ) + s - 2 * n) := by
  by_cases hrn : r < n
  · simpa [alpha_eq_log] using equal_area_comparison_strict hr hn hrn harea
  · have hsn : s < n := by
      by_contra hnot
      have hnr : n ≤ r := by omega
      have hns : n ≤ s := by omega
      have hrEq : r = n := by nlinarith [Nat.mul_le_mul_left r hns]
      have hsEq : s = n := by nlinarith
      exact hne (Prod.ext hrEq hsEq)
    have h := equal_area_comparison_strict hs hn hsn
      (show s * r = n ^ 2 by simpa [Nat.mul_comm] using harea)
    rw [rectangularLog_comm hs hr, alpha_eq_log] at h
    simpa [add_comm] using h

/-- The full area–boundary bound on the equal-area locus. The general
`r*s ≥ n²` theorem is not asserted by this declaration. -/
theorem equal_area_comparison {r s n : ℕ} (hr : 0 < r) (hs : 0 < s) (hn : 0 < n)
    (harea : r * s = n ^ 2) :
    Real.log (SpanningTreeIsoperimetry.treeCount
        (SpanningTreeIsoperimetry.rectangle r s) : ℝ) -
      Real.log (SpanningTreeIsoperimetry.treeCount
        (SpanningTreeIsoperimetry.rectangle n n) : ℝ) ≤
      -Real.log (1 + Real.sqrt 2) * ((r : ℝ) + s - 2 * n) := by
  by_cases heq : (r, s) = (n, n)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    nlinarith
  · exact (equal_area_strict hr hs hn harea heq).le

/-- Equality on the equal-area locus occurs exactly at the square. -/
theorem equal_area_equality_iff {r s n : ℕ} (hr : 0 < r) (hs : 0 < s) (hn : 0 < n)
    (harea : r * s = n ^ 2) :
    (Real.log (SpanningTreeIsoperimetry.treeCount
        (SpanningTreeIsoperimetry.rectangle r s) : ℝ) -
      Real.log (SpanningTreeIsoperimetry.treeCount
        (SpanningTreeIsoperimetry.rectangle n n) : ℝ) =
      -Real.log (1 + Real.sqrt 2) * ((r : ℝ) + s - 2 * n)) ↔
      r = n ∧ s = n := by
  constructor
  · intro heq
    by_contra hnot
    have hne : (r, s) ≠ (n, n) := by simpa using hnot
    exact (ne_of_lt (equal_area_strict hr hs hn harea hne)) heq
  · rintro ⟨rfl, rfl⟩
    ring

/-- The exponentially decaying derivative correction in Appendix A. -/
def residualDerivative (r : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.Ico 1 r,
    2 * Concrete.kernel ((j : ℝ) / r) /
      (Real.exp (2 * Concrete.kernel ((j : ℝ) / r) * t) - 1)

theorem hasDerivAt_realResidual {r : ℕ} {t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    HasDerivAt (realResidual r) (residualDerivative r t) t := by
  have h := HasDerivAt.fun_sum (u := Finset.Ico 1 r) (fun j hj =>
    hasDerivAt_logCorrection (kernel_argument_pos hr hj) ht)
  convert h using 1
  · funext x
    unfold realResidual
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    ring
  · rfl

theorem hasDerivAt_ell {r : ℕ} {t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    HasDerivAt (ell r) (Concrete.C r + residualDerivative r t) t := by
  have hlin : HasDerivAt (fun x : ℝ => Product.spectralBase r + x * Concrete.C r)
      (Concrete.C r) t := by
    simpa using ((hasDerivAt_id t).mul_const (Concrete.C r)).const_add (Product.spectralBase r)
  convert hlin.add (hasDerivAt_realResidual hr ht) using 1
  rfl

/-- The exact derivative identity for the normalized remainder. -/
theorem hasDerivAt_remainder {r : ℕ} {t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    HasDerivAt (remainder r)
      (Concrete.epsilon squareLatticeEntropy r - residualDerivative r t) t := by
  have harea : HasDerivAt (fun x : ℝ => squareLatticeEntropy * r * x)
      (squareLatticeEntropy * r) t := by
    simpa using (hasDerivAt_id t).const_mul (squareLatticeEntropy * r)
  have hboundary : HasDerivAt (fun x : ℝ => Concrete.alpha * (r + x))
      Concrete.alpha t := by
    simpa using ((hasDerivAt_id t).const_add (r : ℝ)).const_mul Concrete.alpha
  convert (harea.sub hboundary).sub (hasDerivAt_ell hr ht) using 1
  · rfl
  · unfold Concrete.epsilon
    ring

private theorem derivativeTerm_antitone_kernel {a b t : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t) :
    2 * b / (Real.exp (2 * b * t) - 1) ≤
      2 * a / (Real.exp (2 * a * t) - 1) := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · rfl
  have hb : 0 < b := lt_trans ha hab
  have hda : 0 < Real.exp (2 * a * t) - 1 := by
    rw [sub_pos, Real.one_lt_exp_iff]
    positivity
  have hdb : 0 < Real.exp (2 * b * t) - 1 := by
    rw [sub_pos, Real.one_lt_exp_iff]
    positivity
  have h := exp_stretch_strict ((one_lt_div ha).mpr hab)
    (show 0 < 2 * a * t by positivity)
  rw [show b / a * (2 * a * t) = 2 * b * t by field_simp <;> ring] at h
  have hm := mul_lt_mul_of_pos_left h ha
  have hba : a * (b / a * (Real.exp (2 * a * t) - 1)) =
      b * (Real.exp (2 * a * t) - 1) := by field_simp
  rw [hba] at hm
  apply le_of_lt
  rw [div_lt_div_iff₀ hdb hda]
  nlinarith

private theorem derivativeTerm_antitone_side {a t u : ℝ}
    (ha : 0 < a) (ht : 0 < t) (htu : t ≤ u) :
    2 * a / (Real.exp (2 * a * u) - 1) ≤
      2 * a / (Real.exp (2 * a * t) - 1) := by
  apply div_le_div_of_nonneg_left (by positivity)
  · rw [sub_pos, Real.one_lt_exp_iff]
    positivity
  · apply sub_le_sub_right
    apply Real.exp_le_exp.mpr
    gcongr

private theorem alpha_lt_nineteen_twentieths : Concrete.alpha < (19 : ℝ) / 20 := by
  have hsq : Real.sqrt 2 < (3 : ℝ) / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hx : 0 < (1 + Real.sqrt 2) / 2 := by positivity
  have hlog := Real.log_le_sub_one_of_pos hx
  rw [Real.log_div (by positivity) (by norm_num)] at hlog
  rw [alpha_eq_log]
  linarith [Real.log_two_lt_d9]

private theorem q_lt_one_thirtysecond : Concrete.q < (1 : ℝ) / 32 := by
  have hq := Concrete.q_pos
  have hq1 := Concrete.q_lt_one
  have hfrac := Concrete.q_fraction
  have hden : 0 < (1 - Concrete.q) ^ 2 := sq_pos_of_pos (by linarith)
  have hEq := (div_eq_iff (ne_of_gt hden)).mp hfrac
  nlinarith

private theorem alpha_lt_one_sub_q : Concrete.alpha < 1 - Concrete.q := by
  linarith [alpha_lt_nineteen_twentieths, q_lt_one_thirtysecond]

private theorem reciprocal_exp_sub {x : ℝ} (hx : 0 < x) :
    1 / (Real.exp x - 1) = Real.exp (-x) / (1 - Real.exp (-x)) := by
  have he : Real.exp x ≠ 0 := ne_of_gt (Real.exp_pos x)
  have hd : Real.exp x - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx))
  rw [Real.exp_neg]
  field_simp <;> ring

private theorem geometric_derivative_sum_le (r : ℕ) :
    (∑ j ∈ Finset.Ico 1 r,
      (j : ℝ) / (Real.exp (4 * Concrete.alpha * j) - 1)) ≤
      (1 : ℝ) / (32 * (1 - Concrete.q)) := by
  have hq := Concrete.q_pos
  have hq1 := Concrete.q_lt_one
  have hqn : ‖Concrete.q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hq] using hq1
  have hsum := hasSum_coe_mul_geometric_of_norm_lt_one hqn
  have hfinite : (∑ j ∈ Finset.Ico 1 r, (j : ℝ) * Concrete.q ^ j) ≤
      Concrete.q / (1 - Concrete.q) ^ 2 :=
    sum_le_hasSum (Finset.Ico 1 r) (fun j _ => by positivity) hsum
  have hpoint (j : ℕ) (hj : j ∈ Finset.Ico 1 r) :
      (j : ℝ) / (Real.exp (4 * Concrete.alpha * j) - 1) ≤
        ((j : ℝ) * Concrete.q ^ j) / (1 - Concrete.q) := by
    have hjpos : 0 < j := (Finset.mem_Ico.mp hj).1
    have hpower : Real.exp (-(4 * Concrete.alpha * j)) = Concrete.q ^ j := by
      rw [Concrete.q, ← Real.exp_nat_mul]
      congr 1
      ring
    have hsmall : Concrete.q ^ j ≤ Concrete.q := by
      simpa using pow_le_pow_of_le_one hq.le hq1.le (show 1 ≤ j by omega)
    have hrep : (j : ℝ) / (Real.exp (4 * Concrete.alpha * j) - 1) =
        (j : ℝ) * Concrete.q ^ j / (1 - Concrete.q ^ j) := by
      rw [div_eq_mul_one_div, reciprocal_exp_sub (by have := Concrete.alpha_pos; positivity), hpower]
      ring
    rw [hrep]
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  calc
    (∑ j ∈ Finset.Ico 1 r, (j : ℝ) / (Real.exp (4 * Concrete.alpha * j) - 1)) ≤
        ∑ j ∈ Finset.Ico 1 r, ((j : ℝ) * Concrete.q ^ j) / (1 - Concrete.q) :=
      Finset.sum_le_sum hpoint
    _ = (∑ j ∈ Finset.Ico 1 r, (j : ℝ) * Concrete.q ^ j) / (1 - Concrete.q) := by
      rw [Finset.sum_div]
    _ ≤ (Concrete.q / (1 - Concrete.q) ^ 2) / (1 - Concrete.q) :=
      div_le_div_of_nonneg_right hfinite (by linarith)
    _ = (1 : ℝ) / (32 * (1 - Concrete.q)) := by
      rw [Concrete.q_fraction]
      field_simp <;> ring

/-- The uniform derivative estimate used for long-side monotonicity. -/
theorem residualDerivative_lt {r : ℕ} {t : ℝ} (hr : 0 < r) (hrt : (r : ℝ) ≤ t) :
    residualDerivative r t < 1 / (8 * (r : ℝ)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hα := Concrete.alpha_pos
  have ht : 0 < t := lt_of_lt_of_le hrR hrt
  have hpoint (j : ℕ) (hj : j ∈ Finset.Ico 1 r) :
      2 * Concrete.kernel ((j : ℝ) / r) /
          (Real.exp (2 * Concrete.kernel ((j : ℝ) / r) * t) - 1) ≤
        (4 * Concrete.alpha / r) *
          ((j : ℝ) / (Real.exp (4 * Concrete.alpha * j) - 1)) := by
    have hj0 : 0 < j := (Finset.mem_Ico.mp hj).1
    have hjr : j < r := (Finset.mem_Ico.mp hj).2
    have hchord := Kernel.kernel_chord_lower hr hj0 hjr
    have hz : 0 < 2 * Concrete.alpha * ((j : ℝ) / r) := by positivity
    have h1 := derivativeTerm_antitone_kernel hz hchord ht
    have h2 := derivativeTerm_antitone_side hz hrR hrt
    apply (h1.trans h2).trans_eq
    have heq : 2 * (2 * Concrete.alpha * ((j : ℝ) / r)) * r =
        4 * Concrete.alpha * j := by field_simp; ring
    rw [heq]
    ring
  have hsum := Finset.sum_le_sum hpoint
  have hgeom := mul_le_mul_of_nonneg_left (geometric_derivative_sum_le r)
    (show 0 ≤ 4 * Concrete.alpha / r by positivity)
  rw [Finset.mul_sum] at hgeom
  have hbound : residualDerivative r t ≤
      (4 * Concrete.alpha / r) * (1 / (32 * (1 - Concrete.q))) :=
    hsum.trans hgeom
  apply lt_of_le_of_lt hbound
  have hq1 := Concrete.q_lt_one
  have hden : 0 < 1 - Concrete.q := by linarith
  have hcross := alpha_lt_one_sub_q
  apply (mul_lt_mul_iff_right₀ (show 0 < 8 * (r : ℝ) * (1 - Concrete.q) by positivity)).mp
  field_simp
  nlinarith

private theorem alpha_lt_nine_tenths : Concrete.alpha < (9 : ℝ) / 10 := by
  have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 10) 5
  norm_num [Finset.sum_range_succ] at ht
  have hs : Real.sqrt 2 < (10 : ℝ) / 7 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  apply Real.exp_lt_exp.mp
  rw [Concrete.exp_alpha]
  linarith

private theorem exp_three_alpha_gt_fourteen : (14 : ℝ) < Real.exp (3 * Concrete.alpha) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hl : (7 : ℝ) / 5 < Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hc : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    rw [pow_succ, hs]
  rw [show 3 * Concrete.alpha = Concrete.alpha + Concrete.alpha + Concrete.alpha by ring,
    Real.exp_add, Real.exp_add, Concrete.exp_alpha]
  nlinarith

private theorem geometric_exponential_sum_le {a : ℝ} (ha : 0 < a) (r : ℕ) :
    (∑ j ∈ Finset.Ico 1 r, (j : ℝ) / (Real.exp (a * j) - 1)) ≤
      Real.exp (-a) / (1 - Real.exp (-a)) ^ 3 := by
  let q := Real.exp (-a)
  have hq : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hqn : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hq] using hq1
  have hsum := hasSum_coe_mul_geometric_of_norm_lt_one hqn
  have hfinite : (∑ j ∈ Finset.Ico 1 r, (j : ℝ) * q ^ j) ≤ q / (1 - q) ^ 2 :=
    sum_le_hasSum (Finset.Ico 1 r) (fun j _ => by positivity) hsum
  have hpoint (j : ℕ) (hj : j ∈ Finset.Ico 1 r) :
      (j : ℝ) / (Real.exp (a * j) - 1) ≤ ((j : ℝ) * q ^ j) / (1 - q) := by
    have hjpos : 0 < j := (Finset.mem_Ico.mp hj).1
    have hpower : Real.exp (-(a * j)) = q ^ j := by
      rw [show q = Real.exp (-a) from rfl, ← Real.exp_nat_mul]
      congr 1
      ring
    have hsmall : q ^ j ≤ q := by
      simpa using pow_le_pow_of_le_one hq.le hq1.le (show 1 ≤ j by omega)
    have hrep : (j : ℝ) / (Real.exp (a * j) - 1) =
        (j : ℝ) * q ^ j / (1 - q ^ j) := by
      rw [div_eq_mul_one_div, reciprocal_exp_sub (by positivity), hpower]
      ring
    rw [hrep]
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  calc
    (∑ j ∈ Finset.Ico 1 r, (j : ℝ) / (Real.exp (a * j) - 1)) ≤
        ∑ j ∈ Finset.Ico 1 r, ((j : ℝ) * q ^ j) / (1 - q) := Finset.sum_le_sum hpoint
    _ = (∑ j ∈ Finset.Ico 1 r, (j : ℝ) * q ^ j) / (1 - q) := by rw [Finset.sum_div]
    _ ≤ (q / (1 - q) ^ 2) / (1 - q) := div_le_div_of_nonneg_right hfinite (by linarith)
    _ = q / (1 - q) ^ 3 := by field_simp <;> ring

private theorem third_exponential_coefficient_lt :
    4 * Concrete.alpha *
      (Real.exp (-(3 * Concrete.alpha)) / (1 - Real.exp (-(3 * Concrete.alpha))) ^ 3) <
      (1 : ℝ) / 3 := by
  let q := Real.exp (-(3 * Concrete.alpha))
  have hq : 0 < q := Real.exp_pos _
  have hqsmall : q < (1 : ℝ) / 14 := by
    dsimp [q]
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num) exp_three_alpha_gt_fourteen
  have hquot : q / (1 - q) ^ 3 ≤ ((1 : ℝ) / 14) / ((13 : ℝ) / 14) ^ 3 := by
    apply div_le_div₀ (by norm_num) hqsmall.le (by norm_num)
    gcongr
    linarith
  have hden : 0 < 1 - q := by linarith
  have hquot0 : 0 ≤ q / (1 - q) ^ 3 := by positivity
  have hα := alpha_lt_nine_tenths
  have hc := mul_le_mul hα.le hquot hquot0 (by norm_num : (0 : ℝ) ≤ 9 / 10)
  change 4 * Concrete.alpha * (q / (1 - q) ^ 3) < 1 / 3
  norm_num at hc
  nlinarith

/-- The second diagonal requires only the range `t ≥ 3r/4`. -/
theorem residualDerivative_three_quarters_lt {r : ℕ} {t : ℝ}
    (hr : 0 < r) (hrt : 3 * (r : ℝ) / 4 ≤ t) :
    residualDerivative r t < 1 / (3 * (r : ℝ)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hα := Concrete.alpha_pos
  have hu : 0 < 3 * (r : ℝ) / 4 := by positivity
  have ht : 0 < t := lt_of_lt_of_le hu hrt
  have hpoint (j : ℕ) (hj : j ∈ Finset.Ico 1 r) :
      2 * Concrete.kernel ((j : ℝ) / r) /
          (Real.exp (2 * Concrete.kernel ((j : ℝ) / r) * t) - 1) ≤
        (4 * Concrete.alpha / r) *
          ((j : ℝ) / (Real.exp (3 * Concrete.alpha * j) - 1)) := by
    have hj0 : 0 < j := (Finset.mem_Ico.mp hj).1
    have hjr : j < r := (Finset.mem_Ico.mp hj).2
    have hz : 0 < 2 * Concrete.alpha * ((j : ℝ) / r) := by positivity
    have h1 := derivativeTerm_antitone_kernel hz (Kernel.kernel_chord_lower hr hj0 hjr) ht
    have h2 := derivativeTerm_antitone_side hz hu hrt
    apply (h1.trans h2).trans_eq
    have heq : 2 * (2 * Concrete.alpha * ((j : ℝ) / r)) * (3 * r / 4) =
        3 * Concrete.alpha * j := by field_simp <;> ring
    rw [heq]
    ring
  have hsum := Finset.sum_le_sum hpoint
  have hgeom := mul_le_mul_of_nonneg_left
    (geometric_exponential_sum_le (show 0 < 3 * Concrete.alpha by positivity) r)
    (show 0 ≤ 4 * Concrete.alpha / r by positivity)
  rw [Finset.mul_sum] at hgeom
  have hbound : residualDerivative r t ≤
      (4 * Concrete.alpha / r) *
        (Real.exp (-(3 * Concrete.alpha)) / (1 - Real.exp (-(3 * Concrete.alpha))) ^ 3) :=
    hsum.trans hgeom
  apply lt_of_le_of_lt hbound
  apply (mul_lt_mul_iff_right₀ hrR).mp
  convert third_exponential_coefficient_lt using 1 <;> field_simp <;> ring

/-- The normalized remainder increases strictly with the long side. -/
theorem remainder_strictMonoOn {r : ℕ} (hr : 0 < r) :
    StrictMonoOn (remainder r) (Set.Ici (r : ℝ)) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  apply strictMonoOn_of_deriv_pos (convex_Ici (r : ℝ))
  · intro t ht
    exact (hasDerivAt_remainder hr (hrR.trans_le ht)).continuousAt.continuousWithinAt
  · intro t ht
    have hrt : (r : ℝ) < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    rw [(hasDerivAt_remainder hr (hrR.trans hrt)).deriv]
    have hε := EpsilonBounds.quarter_div_lt_epsilon hr
    have hsum := residualDerivative_lt hr hrt.le
    have hmargin : 1 / (8 * (r : ℝ)) < 1 / (4 * (r : ℝ)) :=
      one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
    linarith

private theorem residual_increment_lt_of_bound {r : ℕ} {t b C : ℝ}
    (hr : 0 < r) (hb : 0 < b) (hbt : b ≤ t)
    (hbound : ∀ u, b ≤ u → residualDerivative r u < C) :
    realResidual r (t + 1) - realResidual r t < C := by
  have hcontinuity : ContinuousOn (realResidual r) (Set.Ici b) := by
    intro u hu
    exact (hasDerivAt_realResidual hr (hb.trans_le hu)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (realResidual r) (interior (Set.Ici b)) := by
    intro u hu
    have hbu : b < u := by simpa only [interior_Ici, Set.mem_Ioi] using hu
    exact (hasDerivAt_realResidual hr (hb.trans hbu)).differentiableAt.differentiableWithinAt
  have hderiv (u : ℝ) (hu : u ∈ interior (Set.Ici b)) : deriv (realResidual r) u < C := by
    have hbu : b < u := by simpa only [interior_Ici, Set.mem_Ioi] using hu
    rw [(hasDerivAt_realResidual hr (hb.trans hbu)).deriv]
    exact hbound u hbu.le
  have h := (convex_Ici b).image_sub_lt_mul_sub_of_deriv_lt
    hcontinuity hdiff hderiv t hbt (t + 1) (by change b ≤ t + 1; linarith) (by linarith)
  simpa using h

/-- The first residual bound in the square-increment identity. -/
theorem residual_diagonal_lt {r : ℕ} (hr : 0 < r) :
    Concrete.residual r r < 1 / (8 * (r : ℝ)) := by
  have h := residual_increment_lt_of_bound (r := r) (t := (r : ℝ)) hr
    (show (0 : ℝ) < r by exact_mod_cast hr) le_rfl (fun _ hu => residualDerivative_lt hr hu)
  rw [← show ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 by push_cast; rfl] at h
  rw [realResidual_nat, realResidual_nat] at h
  simpa [Concrete.residual] using h

/-- The second residual bound applies from the third square onward. -/
theorem residual_second_diagonal_lt {u : ℕ} (hu : 3 ≤ u) :
    Concrete.residual (u + 1) u < 1 / (3 * ((u : ℝ) + 1)) := by
  have hr : 0 < u + 1 := by omega
  have huR : (3 : ℝ) ≤ u := by exact_mod_cast hu
  have hstart : 3 * ((u + 1 : ℕ) : ℝ) / 4 ≤ (u : ℝ) := by push_cast; linarith
  have h := residual_increment_lt_of_bound (r := u + 1) (t := (u : ℝ)) hr
    (show 0 < 3 * ((u + 1 : ℕ) : ℝ) / 4 by positivity) hstart
    (fun _ ht => residualDerivative_three_quarters_lt hr ht)
  rw [← show ((u + 1 : ℕ) : ℝ) = (u : ℝ) + 1 by push_cast; rfl] at h
  rw [realResidual_nat, realResidual_nat] at h
  simpa [Concrete.residual] using h

private theorem alpha_lt_kernel_third : Concrete.alpha < Concrete.kernel ((1 : ℝ) / 3) := by
  have hα := Concrete.alpha_pos
  have hs : Real.sqrt 2 < (3 : ℝ) / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hc : Real.cosh Concrete.alpha = Real.sqrt 2 := by
    norm_num [Concrete.alpha, Real.cosh_arsinh]
  have hleft : Concrete.alpha = Real.arcosh (Real.cosh Concrete.alpha) :=
    (Real.arcosh_cosh hα.le).symm
  rw [hleft, hc]
  change Real.arcosh (Real.sqrt 2) < Real.arcosh (2 - Real.cos (Real.pi * (1 / 3)))
  rw [show Real.pi * (1 / 3) = Real.pi / 3 by ring, Real.cos_pi_div_three]
  apply (Real.arcosh_lt_arcosh (by positivity) (by norm_num)).mpr
  linarith

/-- The one small second-diagonal estimate follows from the exact cosine
at one third, rather than an external finite tree-count computation. -/
theorem residual_three_two_lt : Concrete.residual 3 2 < (1 : ℝ) / 16 := by
  have hq := Concrete.q_pos
  have hq1 := Concrete.q_lt_one
  have hα := Concrete.alpha_pos
  have hden : 0 < 1 - Concrete.q := by linarith
  have hfrac := Concrete.q_fraction
  have hratio : Concrete.q / (1 - Concrete.q) < (1 : ℝ) / 32 := by
    rw [← hfrac]
    apply div_lt_div_of_pos_left hq (sq_pos_of_pos hden)
    nlinarith
  have hterm (j : ℕ) (hj : j ∈ Finset.Ico 1 3) :
      -Real.log (1 - Real.exp (-2 * (2 : ℝ) * Concrete.kernel ((j : ℝ) / 3))) ≤
        Concrete.q / (1 - Concrete.q) := by
    have hj1 : (1 : ℝ) / 3 ≤ (j : ℝ) / 3 := by
      have h : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Ico.mp hj).1
      linarith
    have hj3 : (j : ℝ) / 3 ≤ 1 := by
      have h : j ≤ 3 := (Finset.mem_Ico.mp hj).2.le
      exact (div_le_one (by norm_num : (0 : ℝ) < 3)).mpr (by exact_mod_cast h)
    have hk := Kernel.kernel_monotoneOn (show (1 : ℝ) / 3 ∈ Set.Icc 0 1 by constructor <;> norm_num)
      ⟨by positivity, hj3⟩ hj1
    have hka : Concrete.alpha < Concrete.kernel ((j : ℝ) / 3) := alpha_lt_kernel_third.trans_le hk
    let x := Real.exp (-2 * (2 : ℝ) * Concrete.kernel ((j : ℝ) / 3))
    have hx : 0 < x := Real.exp_pos _
    have hxq : x ≤ Concrete.q := by
      apply Real.exp_le_exp.mpr
      change -2 * 2 * Concrete.kernel ((j : ℝ) / 3) ≤ -4 * Concrete.alpha
      linarith
    have hx1 : x < 1 := hxq.trans_lt hq1
    have hlog := Concrete.Inputs.neg_log_one_sub_le hx.le hx1
    apply hlog.trans
    exact div_le_div₀ hq.le hxq hden (by linarith)
  have hs := Finset.sum_le_sum hterm
  have hnegative : -Concrete.residualPotential 3 2 < (1 : ℝ) / 16 := by
    rw [Finset.sum_neg_distrib] at hs
    change -Concrete.residualPotential 3 2 ≤ _ at hs
    norm_num [Finset.sum_const] at hs
    linarith
  have htop := fullyFormalizedStagedEqualityInputs.rectangle.toConcreteInputs.potential_nonpos
    (a := 3) (t := 3) (by norm_num) (by norm_num)
  unfold Concrete.residual
  norm_num
  linarith

/-- Exact increment identity for the normalized square sequence. -/
theorem remainder_square_increment (u : ℕ) (hu : 0 < u) :
    remainder (u + 1) (u + 1) - remainder u u =
      Concrete.epsilon squareLatticeEntropy u + Concrete.epsilon squareLatticeEntropy (u + 1) -
        Concrete.residual u u - Concrete.residual (u + 1) u := by
  have hmid := ell_integer_symmetry hu (show 0 < u + 1 by omega)
  unfold ell at hmid
  unfold remainder ell Concrete.epsilon Concrete.residual
  simp only [realResidual, Concrete.residualPotential] at hmid ⊢
  push_cast at hmid ⊢
  nlinarith

/-- Every successive square has strictly larger normalized remainder. -/
theorem remainder_square_step {u : ℕ} (hu : 0 < u) :
    remainder u u < remainder (u + 1) ((u + 1 : ℕ) : ℝ) := by
  apply sub_pos.mp
  rw [show remainder (u + 1) ((u + 1 : ℕ) : ℝ) - remainder u u =
      Concrete.epsilon squareLatticeEntropy u + Concrete.epsilon squareLatticeEntropy (u + 1) -
        Concrete.residual u u - Concrete.residual (u + 1) u by
    simpa only [Nat.cast_add, Nat.cast_one] using remainder_square_increment u hu]
  have he1 := EpsilonBounds.quarter_div_lt_epsilon hu
  have he2 := EpsilonBounds.quarter_div_lt_epsilon (show 0 < u + 1 by omega)
  by_cases h1 : u = 1
  · subst u
    have hq0 : Concrete.residual 1 1 = 0 := by
      norm_num [Concrete.residual, Concrete.residualPotential]
    have hq2 := fullyFormalizedStagedEqualityInputs.rectangle.toConcreteInputs.secondDiagonalResidual_lt_quarter
      (a := 1) (by norm_num)
    norm_num at he1 he2 hq2 ⊢
    rw [hq0]
    linarith
  · by_cases h2 : u = 2
    · subst u
      have hq1 := residual_diagonal_lt (r := 2) (by norm_num)
      have hq2 := residual_three_two_lt
      norm_num at he1 he2 hq1 ⊢
      linarith
    · have h3 : 3 ≤ u := by omega
      have huR : (0 : ℝ) < u := by exact_mod_cast hu
      have hq1 := residual_diagonal_lt hu
      have hq2 := residual_second_diagonal_lt h3
      push_cast at he2
      have hgap : 0 < 1 / (8 * (u : ℝ)) - 1 / (12 * ((u : ℝ) + 1)) := by
        apply sub_pos.mpr
        exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
      have hid :
          1 / (4 * (u : ℝ)) + 1 / (4 * ((u : ℝ) + 1)) -
            (1 / (8 * (u : ℝ)) + 1 / (3 * ((u : ℝ) + 1))) =
          1 / (8 * (u : ℝ)) - 1 / (12 * ((u : ℝ) + 1)) := by
        field_simp <;> ring
      linarith

/-- Monotonicity of the square sequence over all positive integer sizes. -/
theorem remainder_square_mono {n r : ℕ} (hn : 0 < n) (hnr : n ≤ r) :
    remainder n n ≤ remainder r r := by
  induction r, hnr using Nat.le_induction with
  | base => exact le_rfl
  | succ r hnr ih =>
    exact ih.trans (remainder_square_step (show 0 < r by omega)).le

theorem remainder_square_strict {n r : ℕ} (hn : 0 < n) (hnr : n < r) :
    remainder n n < remainder r r :=
  (remainder_square_step hn).trans_le
    (remainder_square_mono (by omega : 0 < n + 1) (by omega : n + 1 ≤ r))

/-- The normalized remainder is strictly minimized at the original square
among ordered rectangles of at least its area. -/
theorem remainder_strict_of_area {n r s : ℕ}
    (hn : 0 < n) (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s)
    (harea : n ^ 2 ≤ r * s) (hne : (r, s) ≠ (n, n)) :
    remainder n n < remainder r s := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrsR : (r : ℝ) ≤ s := by exact_mod_cast hrs
  have hareaR : (n : ℝ) ^ 2 ≤ (r : ℝ) * s := by exact_mod_cast harea
  by_cases hrn : r < n
  · have hrnR : (r : ℝ) < n := by exact_mod_cast hrn
    have ht0 : (r : ℝ) ≤ (n : ℝ) ^ 2 / r := by
      apply (le_div_iff₀ hrR).mpr
      nlinarith
    have hts : (n : ℝ) ^ 2 / r ≤ s := by
      apply (div_le_iff₀ hrR).mpr
      nlinarith
    exact (equal_area_remainder_strict hr hrn).trans_le
      ((remainder_strictMonoOn hr).monotoneOn ht0 hrsR hts)
  · have hnr : n ≤ r := by omega
    by_cases hrEq : r = n
    · subst r
      have hns : n < s := by
        apply lt_of_le_of_ne hrs
        intro hEq
        exact hne (Prod.ext rfl hEq.symm)
      exact remainder_strictMonoOn hn (by change (n : ℝ) ≤ (n : ℝ); exact le_rfl)
        (show (n : ℝ) ≤ s by exact_mod_cast hrs)
        (show (n : ℝ) < s by exact_mod_cast hns)
    · exact (remainder_square_strict hn (by omega : n < r)).trans_le
        ((remainder_strictMonoOn hr).monotoneOn (by change (r : ℝ) ≤ (r : ℝ); exact le_rfl) hrsR hrsR)

/-- The strict area–boundary comparison for the current grid/tree-count model. -/
theorem rectangular_comparison_strict {n r s : ℕ}
    (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (harea : n ^ 2 ≤ r * s) (hne : (r, s) ≠ (n, n)) :
    Real.log (SpanningTreeIsoperimetry.treeCount
        (SpanningTreeIsoperimetry.rectangle r s) : ℝ) -
      Real.log (SpanningTreeIsoperimetry.treeCount
        (SpanningTreeIsoperimetry.rectangle n n) : ℝ) <
      LocalBounds.entropyConstant * ((r : ℝ) * s - (n : ℝ) ^ 2) -
        Real.log (1 + Real.sqrt 2) * ((r : ℝ) + s - 2 * n) := by
  have hordered {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s)
      (harea : n ^ 2 ≤ r * s) (hne : (r, s) ≠ (n, n)) :
      Real.log (SpanningTreeIsoperimetry.treeCount
          (SpanningTreeIsoperimetry.rectangle r s) : ℝ) -
        Real.log (SpanningTreeIsoperimetry.treeCount
          (SpanningTreeIsoperimetry.rectangle n n) : ℝ) <
        LocalBounds.entropyConstant * ((r : ℝ) * s - (n : ℝ) ^ 2) -
          Real.log (1 + Real.sqrt 2) * ((r : ℝ) + s - 2 * n) := by
    have h := remainder_strict_of_area hn hr hs hrs harea hne
    unfold remainder at h
    rw [ell_nat_eq_log_treeCount hn hn, ell_nat_eq_log_treeCount hr hs, alpha_eq_log] at h
    rw [entropy_eq_foundation]
    nlinarith
  rcases le_total r s with hrs | hsr
  · exact hordered hr hs hrs harea hne
  · have hne' : (s, r) ≠ (n, n) := by
      intro heq
      exact hne (Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq))
    have h := hordered hs hr hsr (by simpa [Nat.mul_comm] using harea) hne'
    rw [rectangularLog_comm hs hr] at h
    simpa [mul_comm, add_comm] using h

/-- Proposition `prop:rectangular-comparison`: the full area–boundary bound
for every positive integer rectangle of at least the square's area. -/
theorem rectangular_comparison {n r s : ℕ}
    (hn : 0 < n) (hr : 0 < r) (hs : 0 < s) (harea : n ^ 2 ≤ r * s) :
    Real.log (SpanningTreeIsoperimetry.treeCount
        (SpanningTreeIsoperimetry.rectangle r s) : ℝ) -
      Real.log (SpanningTreeIsoperimetry.treeCount
        (SpanningTreeIsoperimetry.rectangle n n) : ℝ) ≤
      LocalBounds.entropyConstant * ((r : ℝ) * s - (n : ℝ) ^ 2) -
        Real.log (1 + Real.sqrt 2) * ((r : ℝ) + s - 2 * n) := by
  by_cases heq : (r, s) = (n, n)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    nlinarith
  · exact (rectangular_comparison_strict hn hr hs harea heq).le

/-- Equality in the full area–boundary comparison occurs only at the square. -/
theorem rectangular_comparison_equality_iff {n r s : ℕ}
    (hn : 0 < n) (hr : 0 < r) (hs : 0 < s) (harea : n ^ 2 ≤ r * s) :
    (Real.log (SpanningTreeIsoperimetry.treeCount
        (SpanningTreeIsoperimetry.rectangle r s) : ℝ) -
      Real.log (SpanningTreeIsoperimetry.treeCount
        (SpanningTreeIsoperimetry.rectangle n n) : ℝ) =
      LocalBounds.entropyConstant * ((r : ℝ) * s - (n : ℝ) ^ 2) -
        Real.log (1 + Real.sqrt 2) * ((r : ℝ) + s - 2 * n)) ↔
      r = n ∧ s = n := by
  constructor
  · intro heq
    by_contra hnot
    have hne : (r, s) ≠ (n, n) := by simpa using hnot
    exact (ne_of_lt (rectangular_comparison_strict hn hr hs harea hne)) heq
  · rintro ⟨rfl, rfl⟩
    ring

end
end SpanningTreeIsoperimetry.RectangularComparison
