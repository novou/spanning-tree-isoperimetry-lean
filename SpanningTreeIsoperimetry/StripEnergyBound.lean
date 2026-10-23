module

public import SpanningTreeIsoperimetry.StripLoopBound
public import SpanningTreeIsoperimetry.FoundationsBridge
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Tactic.Abel

@[expose] public section

set_option backward.privateInPublic true

/-!
# Scalar estimates for the uniform strip-energy comparison

These exact numerical estimates are closed separately from the remaining
half-plane Green exhaustion. They do not assert the final uniform strip bound.
-/

namespace SpanningTreeIsoperimetry.StripEnergyBound

open scoped BigOperators
open LocalBounds

noncomputable section

/-- Forty-one alternating Catalan terms give the required entropy precision. -/
theorem catalan_lt_45803_50000 : catalanConstant < (45803 : ℝ) / 50000 := by
  have hb := Antitone.tendsto_le_alternating_series
    catalanTerm_summable.tendsto_alternating_series_tsum catalanTerm_antitone 20
  change catalanConstant ≤ _ at hb
  norm_num [Finset.sum_range_succ, catalanTerm] at hb
  linarith

theorem entropy_lt_729_625 : SquareMaximality.squareLatticeEntropy < (729 : ℝ) / 625 := by
  rw [← entropy_eq_foundation, entropyConstant, div_lt_iff₀ Real.pi_pos]
  nlinarith [catalan_lt_45803_50000, Real.pi_gt_d6]

/-- Five positive logarithm terms and a rational lower bound for sqrt 2. -/
theorem alpha_gt_8813_10000 :
    (8813 : ℝ) / 10000 < Real.log (1 + Real.sqrt 2) := by
  have hs := Real.hasSum_log_one_add (a := (140 : ℝ) / 99) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 5) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  have hlog : (8813 : ℝ) / 10000 < Real.log ((239 : ℝ) / 99) := by
    linarith
  have hsqrt : (140 : ℝ) / 99 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  exact hlog.trans (Real.log_lt_log (by norm_num) (by linarith))

/-- Two positive terms suffice after the six-point minor ratio enclosure. -/
theorem minor_log_lower : (311 : ℝ) / 2000 < Real.log ((4673 : ℝ) / 4000) := by
  have hs := Real.hasSum_log_one_add (a := (673 : ℝ) / 4000) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 2) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  linarith

/-- Scalar margin remaining after a loop-correlation lower bound of 311/2000. -/
theorem remaining_margin_lt :
    (SquareMaximality.squareLatticeEntropy - Real.log (1 + Real.sqrt 2) -
      (311 : ℝ) / 2000) / 2 < (81 : ℝ) / 1250 := by
  linarith [entropy_lt_729_625, alpha_gt_8813_10000]

theorem margin_lt_target : (81 : ℝ) / 1250 < (13 : ℝ) / 200 := by norm_num

/-- The three determinant polynomials arising from the six boundary entries. -/
def detThree (t : ℝ) : ℝ := (-9 + 120*t - 448*t^2 + 512*t^3) / 9

def detPlus (t : ℝ) : ℝ := (-106875 + 614400*t - 874496*t^2) / 1800

def detMinus (t : ℝ) : ℝ :=
  (833625 - 6852240*t + 18640896*t^2 - 16777216*t^3) / 5400

private def reciprocalPiLower : ℝ :=
  100000000000000000000 / 314159265358979323847

private def reciprocalPiUpper : ℝ :=
  100000000000000000000 / 314159265358979323846

private theorem reciprocalPi_bounds :
    reciprocalPiLower ≤ 1 / Real.pi ∧ 1 / Real.pi ≤ reciprocalPiUpper := by
  constructor
  · apply le_of_lt
    have h := div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 1) Real.pi_pos Real.pi_lt_d20
    norm_num [reciprocalPiLower] at h ⊢
    exact h
  · apply le_of_lt
    have h := div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 3.14159265358979323846) Real.pi_gt_d20
    norm_num [reciprocalPiUpper] at h ⊢
    exact h

/-- Rational enclosures, with enough margin to avoid decimal approximation in
any subsequent determinant comparison. -/
theorem determinant_polynomial_bounds :
    (3534241 : ℝ) / 100000000 < detThree (1 / Real.pi) ∧
    (4979125 : ℝ) / 100000000 < detPlus (1 / Real.pi) ∧
    detPlus (1 / Real.pi) < (4979126 : ℝ) / 100000000 ∧
    (2147275 : ℝ) / 100000000 < detMinus (1 / Real.pi) ∧
    detMinus (1 / Real.pi) < (2147276 : ℝ) / 100000000 := by
  obtain ⟨hl, hu⟩ := reciprocalPi_bounds
  have hl0 : 0 ≤ reciprocalPiLower := by norm_num [reciprocalPiLower]
  have ht0 : 0 ≤ 1 / Real.pi := by positivity
  have hl2 : reciprocalPiLower ^ 2 ≤ (1 / Real.pi) ^ 2 := by gcongr
  have hu2 : (1 / Real.pi) ^ 2 ≤ reciprocalPiUpper ^ 2 := by gcongr
  have hl3 : reciprocalPiLower ^ 3 ≤ (1 / Real.pi) ^ 3 := by gcongr
  have hu3 : (1 / Real.pi) ^ 3 ≤ reciprocalPiUpper ^ 3 := by gcongr
  norm_num [reciprocalPiLower, reciprocalPiUpper] at hl hu hl2 hu2 hl3 hu3
  dsimp only [detThree, detPlus, detMinus]
  simp only [one_div, inv_pow]
  constructor
  · nlinarith only [hl, hu2, hl3]
  constructor
  · nlinarith only [hl, hu2]
  constructor
  · nlinarith only [hu, hl2]
  constructor
  · nlinarith only [hu, hl2, hu3]
  · nlinarith only [hl, hu2, hl3]

/-- Exact scalar six-point determinant ratio bound. Identifying these
polynomials with the exhausted Green minors is still a separate step. -/
theorem determinant_polynomial_ratio_lower :
    (4673 : ℝ) / 4000 <
      detThree (1 / Real.pi)^2 / (detPlus (1 / Real.pi) * detMinus (1 / Real.pi)) := by
  obtain ⟨h3, hp0, hp, hm0, hm⟩ := determinant_polynomial_bounds
  have hplus : 0 < detPlus (1 / Real.pi) := by linarith
  have hminus : 0 < detMinus (1 / Real.pi) := by linarith
  rw [lt_div_iff₀ (mul_pos hplus hminus)]
  have hden : detPlus (1 / Real.pi) * detMinus (1 / Real.pi) <
      (4979126 : ℝ) / 100000000 * ((2147276 : ℝ) / 100000000) :=
    mul_lt_mul hp hm.le hminus (by norm_num)
  have hnum : ((3534241 : ℝ) / 100000000)^2 < detThree (1 / Real.pi)^2 := by
    nlinarith
  nlinarith

/-- The resulting scalar loop-correlation lower bound. -/
theorem determinant_polynomial_log_lower :
    (311 : ℝ) / 2000 < Real.log
      (detThree (1 / Real.pi)^2 / (detPlus (1 / Real.pi) * detMinus (1 / Real.pi))) :=
  minor_log_lower.trans (Real.log_lt_log (by norm_num) determinant_polynomial_ratio_lower)

/-- The boundary Toeplitz block on three consecutive sites. -/
def boundaryThree (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1-2*t, -1/2+2*t, -1+(10/3)*t;
     -1/2+2*t, 1-2*t, -1/2+2*t;
     -1+(10/3)*t, -1/2+2*t, 1-2*t]

/-- The cross block after reversing the order of the second three sites. -/
def boundaryCross (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-76+(1194/5)*t, -17+(802/15)*t, -4+(38/3)*t;
     -17+(802/15)*t, -4+(38/3)*t, -1+(10/3)*t;
     -4+(38/3)*t, -1+(10/3)*t, -1/2+2*t]

theorem boundaryThree_det (t : ℝ) : Matrix.det (boundaryThree t) = detThree t := by
  norm_num [Matrix.det_fin_three, boundaryThree, detThree]
  <;> ring

theorem boundaryPlus_det (t : ℝ) :
    Matrix.det (boundaryThree t + boundaryCross t) = detPlus t := by
  norm_num [Matrix.det_fin_three, boundaryThree, boundaryCross, detPlus]
  <;> ring

theorem boundaryMinus_det (t : ℝ) :
    Matrix.det (boundaryThree t - boundaryCross t) = detMinus t := by
  norm_num [Matrix.det_fin_three, boundaryThree, boundaryCross, detMinus]
  <;> ring

/-- The centrosymmetric block factorization, proved by an explicit invertible
change of basis, works for arbitrary real square blocks. -/
theorem det_centrosymmetric_blocks {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) :
    Matrix.det (Matrix.fromBlocks A B B A) = Matrix.det (A+B) * Matrix.det (A-B) := by
  let P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ := Matrix.fromBlocks 1 1 1 (-1)
  have hP : Matrix.det P = (-2 : ℝ) ^ Fintype.card ι := by
    dsimp only [P]
    rw [Matrix.det_fromBlocks_one₁₁, Matrix.one_mul]
    have he : -(1 : Matrix ι ι ℝ) - 1 = (-2 : ℝ) • (1 : Matrix ι ι ℝ) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [he, Matrix.det_smul, Matrix.det_one, mul_one]
  have hne : Matrix.det P ≠ 0 := by rw [hP]; exact pow_ne_zero _ (by norm_num)
  have hm : P * Matrix.fromBlocks A B B A = Matrix.fromBlocks (A+B) 0 0 (A-B) * P := by
    dsimp only [P]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.neg_mul, Matrix.mul_one, Matrix.mul_neg,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    congr 1 <;> abel
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁] at hd
  exact mul_left_cancel₀ hne (hd.trans (mul_comm _ _))

def boundarySix (t : ℝ) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks (boundaryThree t) (boundaryCross t) (boundaryCross t) (boundaryThree t)

theorem boundarySix_det (t : ℝ) : Matrix.det (boundarySix t) = detPlus t * detMinus t := by
  rw [boundarySix, det_centrosymmetric_blocks, boundaryPlus_det, boundaryMinus_det]

/-- The fully evaluated six-point matrix minor inequality. Its remaining use
in the strip proof requires identifying this matrix as the half-plane limit. -/
theorem boundarySix_log_ratio_lower :
    (311 : ℝ) / 2000 < Real.log
      ((Matrix.det (boundaryThree (1 / Real.pi)))^2 /
        Matrix.det (boundarySix (1 / Real.pi))) := by
  rw [boundaryThree_det, boundarySix_det]
  exact determinant_polynomial_log_lower

end
end SpanningTreeIsoperimetry.StripEnergyBound
