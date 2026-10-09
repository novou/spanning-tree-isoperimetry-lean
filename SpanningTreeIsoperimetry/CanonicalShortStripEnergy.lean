import SpanningTreeIsoperimetry.FiniteBoundaryMinorBridge
import SpanningTreeIsoperimetry.FiniteCornerCharges
import SpanningTreeIsoperimetry.CanonicalSmallBaseline

/-! Actual short-strip finite energies beat the exact competing quadrant
baselines plus per-cell corrections, by the checked terminal Green minors. -/
namespace SpanningTreeIsoperimetry.CanonicalShortStripEnergy
open Ferrers CornerEnergy CornerStripBridge FiniteBoundaryMinorBridge FiniteBoundaryMinors
  SingletonEnergy ThreeCellEnergy SmallCornerEnergies
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem minor_monotone_primal {R S r s k : ℕ} (hR : 0<R) (hk : k≤S)
    (hr : R+1≤r) (hs : S+1≤s) :
    Matrix.det (leadingBlock hR hk)≤Matrix.det (leadingBlock (by omega : 0<r-1) (by omega : k≤s-1)) :=
  leadingMinor_monotone hR (by omega) hk (by omega) (by omega) (by omega)

theorem strip_energy_of_minor_bound {R S k : ℕ} (hR : 1≤R) (hk : k≤S)
    {d f E : ℝ} (hd : 0<d) (hf : 0<f)
    (hminor : f*d<Matrix.det (leadingBlock (by omega : 0<R) hk))
    (hE : E= -Real.log d-SquareMaximality.squareLatticeEntropy*k) :
    dirichletEnergy (verticalDiagram_subset hR hk)<E-Real.log f := by
  rw [leadingBlock_det_eq_greenMinor] at hminor
  have hlog := Real.log_lt_log (mul_pos hf hd) hminor
  rw [Real.log_mul hf.ne' hd.ne'] at hlog
  unfold dirichletEnergy
  have hc : (verticalDiagram k).card=k := by simp [verticalDiagram]
  rw [hc,hE]
  linarith only [hlog]

theorem two_energy_det : 2*realEnergy (horizontalStrip 1)=
    -Real.log ((2-(16/3)/Real.pi)^2)-SquareMaximality.squareLatticeEntropy*(2 : ℕ) := by
  have he : horizontalStrip 1=({(0,0)} : Diagram) := by decide +kernel
  rw [he,realEnergy_singleton,Real.log_pow]
  norm_num
  ring

theorem square_energy_det : realEnergy (faceRectangle 2 2)=
    -Real.log (SmallGreenPolynomials.squareDet (1/Real.pi))-SquareMaximality.squareLatticeEntropy*(4 : ℕ) := by
  simpa only [Nat.cast_ofNat,mul_comm] using square_energy_exact

private theorem two_scale_log : -Real.log ((256 : ℝ)/259)≤(3 : ℝ)/256 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<259/256)
  rw [show (256 : ℝ)/259=((259 : ℝ)/256)⁻¹ by norm_num,Real.log_inv]
  norm_num at h ⊢
  linarith

private theorem square_scale_log : -Real.log ((2401 : ℝ)/2407)≤(6 : ℝ)/2401 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2407/2401)
  rw [show (2401 : ℝ)/2407=((2407 : ℝ)/2401)⁻¹ by norm_num,Real.log_inv]
  norm_num at h ⊢
  linarith

theorem two_strip_gap {r s : ℕ} (hr : 4≤r) (hs : r+2≤s) :
    dirichletEnergy (verticalDiagram_subset (by omega : 1≤r-1) (by omega : 2≤s-1))<
      2*realEnergy (horizontalStrip 1)+2*correction (faceRectangle (r-1) (s-1)) {(0,0)} := by
  have hd : 0<(2-(16/3)/Real.pi)^2 := sq_pos_of_pos singleton_green_pos
  by_cases hr5 : 5≤r
  · have hm := minor_monotone_primal (by decide : 0<4) (by decide : 2≤6) hr5 (by omega : 7≤s)
    have hb := terminal_two_five.trans_le hm
    have he := strip_energy_of_minor_bound (R := r-1) (S := s-1) (k := 2)
      (by omega) (by omega) hd (by norm_num : (0 : ℝ)<1) (by simpa using hb) two_energy_det
    simp only [Real.log_one,sub_zero] at he
    linarith [correction_nonneg (faceRectangle (r-1) (s-1)) ({(0,0)} : Diagram)]
  · have hr4 : r=4 := by omega
    subst r
    have hm := minor_monotone_primal (by decide : 0<3) (by decide : 2≤5)
      (by decide : 4≤4) (by omega : 6≤s)
    have hb := terminal_two_four.trans_le hm
    have he := strip_energy_of_minor_bound (R := 3) (S := s-1) (k := 2)
      (by omega) (by omega) hd (by norm_num : (0 : ℝ)<256/259) hb two_energy_det
    have hc := FiniteSingletonLower.singleton_correction_lower_left (R := 3) (S := s-1)
      (by omega) (by omega)
    norm_num at hc
    norm_num only [Nat.reduceSub] at ⊢
    linarith [two_scale_log]

theorem three_strip_gap {r s : ℕ} (hr : 5≤r) (hs : r+3≤s) :
    dirichletEnergy (verticalDiagram_subset (by omega : 1≤r-1) (by omega : 3≤s-1))<realEnergy threeCell := by
  have hm := minor_monotone_primal (by decide : 0<4) (by decide : 3≤7) hr (by omega : 8≤s)
  have hb := terminal_three.trans_le hm
  have he := strip_energy_of_minor_bound (R := r-1) (S := s-1) (k := 3)
    (by omega) (by omega) ellDet_pos (by norm_num : (0 : ℝ)<1)
    (by simpa using hb) (by simpa only [Nat.cast_ofNat,mul_comm] using realEnergy_ell_exact)
  simpa only [Real.log_one,sub_zero,mul_comm] using he

theorem four_strip_gap {r s : ℕ} (hr : 7≤r) (hs : r+4≤s) :
    dirichletEnergy (verticalDiagram_subset (by omega : 1≤r-1) (by omega : 4≤s-1))<
      realEnergy (faceRectangle 2 2)+4*correction (faceRectangle (r-1) (s-1)) {(0,0)} := by
  have hd := RectangleEnergyBounds.squareDet_pos
  by_cases hr8 : 8≤r
  · have hm := minor_monotone_primal (by decide : 0<7) (by decide : 4≤11) hr8 (by omega : 12≤s)
    have hb := terminal_four_eight.trans_le hm
    have he := strip_energy_of_minor_bound (R := r-1) (S := s-1) (k := 4)
      (by omega) (by omega) hd (by norm_num : (0 : ℝ)<1) (by simpa using hb) square_energy_det
    simp only [Real.log_one,sub_zero] at he
    linarith [correction_nonneg (faceRectangle (r-1) (s-1)) ({(0,0)} : Diagram)]
  · have hr7 : r=7 := by omega
    subst r
    have hm := minor_monotone_primal (by decide : 0<6) (by decide : 4≤10)
      (by decide : 7≤7) (by omega : 11≤s)
    have hb := terminal_four_seven.trans_le hm
    have he := strip_energy_of_minor_bound (R := 6) (S := s-1) (k := 4)
      (by omega) (by omega) hd (by norm_num : (0 : ℝ)<2401/2407) hb square_energy_det
    have hc := FiniteSingletonLower.singleton_correction_lower_left (R := 6) (S := s-1)
      (by omega) (by omega)
    norm_num at hc
    norm_num only [Nat.reduceSub] at ⊢
    linarith [square_scale_log]

end
end SpanningTreeIsoperimetry.CanonicalShortStripEnergy
