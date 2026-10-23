module

public import SpanningTreeIsoperimetry.SmallGreenPolynomials
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

set_option backward.privateInPublic true

/-! Exact rational enclosures of the three checked determinant polynomials. -/
namespace SpanningTreeIsoperimetry.SmallGreenEnclosures
open SmallGreenPolynomials
noncomputable section

private def lower : ℝ := 100000000000000000000/314159265358979323847
private def upper : ℝ := 100000000000000000000/314159265358979323846

private theorem reciprocal_bounds : lower≤1/Real.pi ∧ 1/Real.pi≤upper := by
  constructor
  · have h := div_lt_div_of_pos_left (by norm_num : (0 : ℝ)<1) Real.pi_pos Real.pi_lt_d20
    norm_num [lower] at h ⊢
    exact h.le
  · have h := div_lt_div_of_pos_left (by norm_num : (0 : ℝ)<1)
      (by norm_num : (0 : ℝ)<3.14159265358979323846) Real.pi_gt_d20
    norm_num [upper] at h ⊢
    exact h.le

private theorem power_bounds :
    lower≤1/Real.pi ∧ 1/Real.pi≤upper ∧
    lower^2≤(1/Real.pi)^2 ∧ (1/Real.pi)^2≤upper^2 ∧
    lower^3≤(1/Real.pi)^3 ∧ (1/Real.pi)^3≤upper^3 ∧
    lower^4≤(1/Real.pi)^4 ∧ (1/Real.pi)^4≤upper^4 := by
  obtain ⟨hl,hu⟩:=reciprocal_bounds
  have h0 : 0≤lower := by norm_num [lower]
  have ht : 0≤1/Real.pi := by positivity
  exact ⟨hl,hu,by gcongr,by gcongr,by gcongr,by gcongr,by gcongr,by gcongr⟩

theorem squareDet_upper : squareDet (1/Real.pi)<(89 : ℝ)/10000 := by
  obtain ⟨hl,_,_,hu2,hl3,_,_,_⟩:=power_bounds
  norm_num [lower,upper] at hl hu2 hl3
  unfold squareDet
  simp only [one_div,inv_pow,pow_one] at hu2 hl3 ⊢
  nlinarith only [hl,hu2,hl3]

theorem rectangleDet_upper : rectangleDet (1/Real.pi)<(85649 : ℝ)/100000000 := by
  obtain ⟨hl,_,_,hu2,hl3,_,_,hu4⟩:=power_bounds
  norm_num [lower,upper] at hl hu2 hl3 hu4
  unfold rectangleDet
  simp only [one_div,inv_pow,pow_one] at hu2 hl3 hu4 ⊢
  nlinarith only [hl,hu2,hl3,hu4]

theorem stripDet_lower : (1 : ℝ)/112<stripDet (1/Real.pi) := by
  obtain ⟨_,hu,hl2,_,_,hu3,hl4,_⟩:=power_bounds
  norm_num [lower,upper] at hu hl2 hu3 hl4
  unfold stripDet
  simp only [one_div,inv_pow,pow_one] at hl2 hu3 hl4 ⊢
  nlinarith only [hu,hl2,hu3,hl4]

end
end SpanningTreeIsoperimetry.SmallGreenEnclosures
