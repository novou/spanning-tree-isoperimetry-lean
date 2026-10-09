import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Exact fourth-order summation bound used after separating the one-boundary
Green-loss kernel. This module makes no claim identifying a Green kernel. -/
namespace SpanningTreeIsoperimetry.BoundaryLossSeries

open scoped BigOperators
noncomputable section

def imageDifference (b c : ℝ) : ℝ := 1/(b-c)^2+1/(b+c)^2-2/b^2

theorem imageDifference_eq {b c : ℝ} (hc : 0≤c) (hbc : c<b) :
    imageDifference b c=2*c^2*(3*b^2-c^2)/(b^2*(b^2-c^2)^2) := by
  have hb : 0<b := lt_of_le_of_lt hc hbc
  have hm : b-c≠0 := by linarith
  have hp : b+c≠0 := by linarith
  have hs : b^2-c^2≠0 := by nlinarith
  unfold imageDifference
  field_simp
  <;> ring

theorem imageDifference_nonneg {b c : ℝ} (hc : 0≤c) (hbc : c<b) :
    0 ≤ imageDifference b c := by
  rw [imageDifference_eq hc hbc]
  have hnum : 0≤3*b^2-c^2 := by nlinarith
  positivity

theorem imageDifference_le {b c : ℝ} (hc : 0≤c) (hbc : c<b) :
    imageDifference b c≤6*c^2/(b^2-c^2)^2 := by
  rw [imageDifference_eq hc hbc]
  have hb : 0<b := lt_of_le_of_lt hc hbc
  have hs : 0<b^2-c^2 := by nlinarith
  have hb2 : 0<b^2 := sq_pos_of_pos hb
  rw [div_le_div_iff₀ (mul_pos hb2 (sq_pos_of_pos hs)) (sq_pos_of_pos hs)]
  have hnon := mul_nonneg (sq_nonneg (c^2)) (sq_nonneg (b^2-c^2))
  nlinarith only [hnon]

theorem imageDifference_scaled_le {r c : ℝ} (hc : 0≤c) (hr : c<r) (n : ℕ) :
    imageDifference (r*(n+1)) c≤
      (6*c^2/(r^2-c^2)^2)*(1/(n+1 : ℝ)^4) := by
  have hn : (1 : ℝ)≤n+1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hr0 : 0<r := lt_of_le_of_lt hc hr
  have hrc : c<r*(n+1) := by nlinarith
  have hgap : 0<r^2-c^2 := by nlinarith
  have hden : (n+1 : ℝ)^2*(r^2-c^2)≤(r*(n+1))^2-c^2 := by
    have hn2 : (1 : ℝ)≤(n+1 : ℝ)^2 := by nlinarith
    have hm := mul_nonneg (sq_nonneg c) (sub_nonneg.mpr hn2)
    nlinarith only [hm]
  calc
    imageDifference (r*(n+1)) c≤6*c^2/((r*(n+1))^2-c^2)^2 := imageDifference_le hc hrc
    _≤6*c^2/((n+1 : ℝ)^2*(r^2-c^2))^2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact pow_le_pow_left₀ (by positivity) hden 2
    _=(6*c^2/(r^2-c^2)^2)*(1/(n+1 : ℝ)^4) := by
      have hn0 : (n+1 : ℝ)≠0 := by positivity
      field_simp
      <;> ring

private theorem zeta_four_succ_hasSum :
    HasSum (fun n : ℕ => (1 : ℝ)/(n+1 : ℝ)^4) (Real.pi^4/90) := by
  have h := (hasSum_nat_add_iff' 1).2 hasSum_zeta_four
  simpa using h

theorem imageDifference_summable {r c : ℝ} (hc : 0≤c) (hr : c<r) :
    Summable (fun n : ℕ => imageDifference (r*(n+1)) c) := by
  apply Summable.of_nonneg_of_le (fun n => imageDifference_nonneg hc ?_)
    (imageDifference_scaled_le hc hr) (zeta_four_succ_hasSum.summable.mul_left _)
  have hn : (1 : ℝ)≤n+1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hr0 : 0<r := lt_of_le_of_lt hc hr
  nlinarith

/-- The exact π³/60 bound, obtained from the checked ζ(4) value. -/
theorem imageSeries_le {r c : ℝ} (hc : 0≤c) (hr : c<r) :
    (1/(4*Real.pi))*(∑' n : ℕ, imageDifference (r*(n+1)) c)≤
      Real.pi^3*c^2/(60*(r^2-c^2)^2) := by
  have hm := zeta_four_succ_hasSum.mul_left (6*c^2/(r^2-c^2)^2)
  have hs := (imageDifference_summable hc hr).tsum_le_tsum
    (imageDifference_scaled_le hc hr) hm.summable
  rw [hm.tsum_eq] at hs
  calc
    _≤(1/(4*Real.pi))*((6*c^2/(r^2-c^2)^2)*(Real.pi^4/90)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _=Real.pi^3*c^2/(60*(r^2-c^2)^2) := by
      have hp : Real.pi≠0 := Real.pi_ne_zero
      field_simp
      <;> ring

end
end SpanningTreeIsoperimetry.BoundaryLossSeries
