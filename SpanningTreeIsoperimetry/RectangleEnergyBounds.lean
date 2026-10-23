module

public import SpanningTreeIsoperimetry.SmallCornerEnergies
public import SpanningTreeIsoperimetry.SmallGreenEnclosures
public import SpanningTreeIsoperimetry.CornerNumericBounds

@[expose] public section

/-! The two fixed rectangular obstructions needed for strip rigidity. -/
namespace SpanningTreeIsoperimetry.RectangleEnergyBounds
open Ferrers CornerEnergy SmallCornerEnergies SmallGreenEnclosures SmallGreenPolynomials CornerNumericBounds

theorem squareDet_pos : 0<squareDet (1/Real.pi) := by
  rw [← square_exp_energy]
  exact Real.exp_pos _

theorem rectangleDet_pos : 0<rectangleDet (1/Real.pi) := by
  rw [← rectangle_exp_energy]
  exact Real.exp_pos _

theorem square_energy_lower : (7 : ℝ)/125<realEnergy (faceRectangle 2 2) := by
  have hl := Real.log_lt_log squareDet_pos squareDet_upper
  have he : Real.log ((89 : ℝ)/10000)=-Real.log ((10000 : ℝ)/89) := by
    rw [show (89 : ℝ)/10000=((10000 : ℝ)/89)⁻¹ by norm_num,Real.log_inv]
  rw [he] at hl
  rw [square_energy_exact]
  linarith [log_square_lower,entropy_lt_58313_50000]

theorem rectangle_energy_lower : (651 : ℝ)/10000<realEnergy (faceRectangle 3 2) := by
  have hl := Real.log_lt_log rectangleDet_pos rectangleDet_upper
  have he : Real.log ((85649 : ℝ)/100000000)=-Real.log ((100000000 : ℝ)/85649) := by
    rw [show (85649 : ℝ)/100000000=((100000000 : ℝ)/85649)⁻¹ by norm_num,Real.log_inv]
  rw [he] at hl
  rw [rectangle_energy_exact]
  linarith [log_rectangle_lower,entropy_lt_58313_50000]

theorem strip_four_upper : realEnergy (horizontalStrip 4)<(11 : ℝ)/200 := by
  have hl := Real.log_lt_log (by norm_num : (0 : ℝ)<1/112) stripDet_lower
  rw [show (1 : ℝ)/112=(112 : ℝ)⁻¹ by norm_num,Real.log_inv] at hl
  rw [strip_energy_exact]
  linarith [log_112_upper,entropy_gt_583_500]

theorem square_strip_four_gap : (1 : ℝ)/1000<
    realEnergy (faceRectangle 2 2)-realEnergy (horizontalStrip 4) := by
  linarith [square_energy_lower,strip_four_upper]

theorem rectangle_strip_limit_gap : (1 : ℝ)/4000<
    realEnergy (faceRectangle 3 2)-UniformStripEnergy.stripEnergyLimit := by
  linarith [rectangle_energy_lower,UniformStripEnergy.stripEnergyLimit_lt]

end SpanningTreeIsoperimetry.RectangleEnergyBounds
