import SpanningTreeIsoperimetry.StripEnergyBound
import Mathlib.Analysis.Complex.Exponential

/-! Short exact entropy and logarithm enclosures for the fixed corner shapes. -/
namespace SpanningTreeIsoperimetry.CornerNumericBounds
open LocalBounds
open scoped BigOperators

theorem entropy_lt_58313_50000 : SquareMaximality.squareLatticeEntropy<(58313 : ℝ)/50000 := by
  have hb := Antitone.tendsto_le_alternating_series
    catalanTerm_summable.tendsto_alternating_series_tsum catalanTerm_antitone 50
  change catalanConstant≤_ at hb
  norm_num [Finset.sum_range_succ,catalanTerm] at hb
  have hc : catalanConstant<(915978 : ℝ)/1000000 := by linarith
  rw [← entropy_eq_foundation,entropyConstant,div_lt_iff₀ Real.pi_pos]
  nlinarith [Real.pi_gt_d6]

theorem entropy_gt_583_500 : (583 : ℝ)/500<SquareMaximality.squareLatticeEntropy := by
  have hb := Antitone.alternating_series_le_tendsto
    catalanTerm_summable.tendsto_alternating_series_tsum catalanTerm_antitone 15
  change _≤catalanConstant at hb
  norm_num [Finset.sum_range_succ,catalanTerm] at hb
  have hc : (4579 : ℝ)/5000<catalanConstant := by linarith
  rw [← entropy_eq_foundation,entropyConstant,lt_div_iff₀ Real.pi_pos]
  nlinarith [Real.pi_lt_d6]

theorem log_two_lower : (6931471805 : ℝ)/10000000000<Real.log 2 := by
  have hs := Real.hasSum_log_one_add (a := (1 : ℝ)) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 10) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  linarith

theorem log_rectangle_lower : (706266 : ℝ)/100000<Real.log ((100000000 : ℝ)/85649) := by
  have hs := Real.hasSum_log_one_add (a := (12295424 : ℝ)/87704576) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 3) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  have hy : (13119 : ℝ)/100000<Real.log ((100000000 : ℝ)/87704576) := by norm_num; linarith
  have he := Real.log_mul (by norm_num : (2 : ℝ)^10≠0)
    (by norm_num : (100000000 : ℝ)/87704576≠0)
  rw [show (2 : ℝ)^10*((100000000 : ℝ)/87704576)=(100000000 : ℝ)/85649 by norm_num,
    Real.log_pow] at he
  norm_num at he
  linarith [log_two_lower]

theorem log_square_lower : (472108 : ℝ)/100000<Real.log ((10000 : ℝ)/89) := by
  have hs := Real.hasSum_log_one_add (a := (4304 : ℝ)/5696) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 4) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  have hy : (5622 : ℝ)/10000<Real.log ((10000 : ℝ)/5696) := by norm_num; linarith
  have he := Real.log_mul (by norm_num : (2 : ℝ)^6≠0)
    (by norm_num : (10000 : ℝ)/5696≠0)
  rw [show (2 : ℝ)^6*((10000 : ℝ)/5696)=(10000 : ℝ)/89 by norm_num,Real.log_pow] at he
  norm_num at he
  linarith [log_two_lower]

theorem log_112_upper : Real.log 112<(4719 : ℝ)/1000 := by
  have hb := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤4719/1000) 25
  norm_num [Finset.sum_range_succ,Nat.factorial] at hb
  have he : (112 : ℝ)<Real.exp ((4719 : ℝ)/1000) := by linarith
  have hl := Real.log_lt_log (by norm_num : (0 : ℝ)<112) he
  simpa only [Real.log_exp] using hl

end SpanningTreeIsoperimetry.CornerNumericBounds
