import SpanningTreeIsoperimetry.StripFourierFive
import SpanningTreeIsoperimetry.RefinedPiBounds
import SpanningTreeIsoperimetry.PrintedElementaryConstants
import SpanningTreeIsoperimetry.UniformStripEnergy

/-! The displayed finite-five-coefficient upper bound, proved independently
of the still separate infinite Toeplitz--Hankel determinant identity. -/
namespace SpanningTreeIsoperimetry.StripFourierUpperBound
open StripFourierCoefficients StripFourierFive RefinedPiBounds PrintedElementaryConstants
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

def weightedPoly (t : ℝ) : ℝ :=
  (1-2*t)^2+2*(2-6*t)^2+3*(19/3-(178/9)*t)^2+
    4*(24-(226/3)*t)^2+5*(501/5-(23606/75)*t)^2

def centeredPoly (x : ℝ) : ℝ := (327276429319053809916349009427814435502433/2109375000000000000000000000000000000000000 : ℝ)+(-1298381329205032025776871/21093750000000000000000 : ℝ)*x+(1752560708/3375 : ℝ)*x^2

theorem weightedPoly_centered (t : ℝ) : weightedPoly t=centeredPoly (t-center) := by
  unfold weightedPoly centeredPoly center
  ring

def fiveCoefficientBound : ℝ :=
  (SquareMaximality.squareLatticeEntropy-Real.log (1+Real.sqrt 2))/2-
    (1/2)*∑ j : Fin 5, ((j.val+1 : ℕ) : ℝ)*coefficient (j.val+1)^2

theorem fiveCoefficientBound_eq : fiveCoefficientBound=
    (SquareMaximality.squareLatticeEntropy-Real.log (1+Real.sqrt 2))/2-
      (1/2)*weightedPoly (1/Real.pi) := by
  unfold fiveCoefficientBound
  simp only [first_five]
  norm_num [Fin.sum_univ_succ,coefficientValues,weightedPoly]
  field_simp [Real.pi_ne_zero]
  <;> ring

theorem fiveCoefficientBound_interval :
    (64858 : ℝ)/1000000<fiveCoefficientBound ∧ fiveCoefficientBound<(64859 : ℝ)/1000000 := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  norm_num [radius] at hl1 hu1 hl2 hu2
  rw [fiveCoefficientBound_eq,weightedPoly_centered]
  unfold centeredPoly
  simp only [one_div] at hl1 hu1 hl2 hu2 ⊢
  constructor <;> nlinarith only [hl1,hu1,hl2,hu2,entropy_bounds.1,entropy_bounds.2,
    alpha_bounds.1,alpha_bounds.2]

theorem strip_limit_lt_five_coefficients : UniformStripEnergy.stripEnergyLimit<fiveCoefficientBound := by
  exact UniformStripEnergy.stripEnergyLimit_lt.trans
    ((by norm_num : (81 : ℝ)/1250<64858/1000000).trans fiveCoefficientBound_interval.1)

theorem displayed_strip_upper_bound :
    UniformStripEnergy.stripEnergyLimit≤fiveCoefficientBound ∧
      fiveCoefficientBound<(64859 : ℝ)/1000000 ∧ (64859 : ℝ)/1000000<13/200 :=
  ⟨strip_limit_lt_five_coefficients.le,fiveCoefficientBound_interval.2,by norm_num⟩

end
end SpanningTreeIsoperimetry.StripFourierUpperBound
