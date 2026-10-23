module

public import SpanningTreeIsoperimetry.RefinedCornerEnvelope

@[expose] public section

/-! Structural lower bounds for shallow single-corner diagrams. The finite
energy values used here are the checked obstruction energies. -/
namespace SpanningTreeIsoperimetry.SingleCornerSmallEnergyBounds
open Ferrers CornerEnergy StripRigidity TwoTierFerrers
open RefinedObstructionEnergy RefinedStripEnergy StripSupportingLines
open scoped Classical
noncomputable section

/-- Every nonrectangular Ferrers diagram of at least five cells contains one
of the three checked tier obstructions, or has at least three maximal cells. -/
theorem nonrectangle_large_lower {M : Diagram} (hM : IsFerrers M)
    (hk : 5≤M.card) (hr : ¬IsRectangle M) :
    (7421 : ℝ)/100000<realEnergy M := by
  have hne : M.Nonempty := Finset.card_pos.mp (by omega)
  by_cases hmax : 3≤(maximalCells M).card
  · have hm := realEnergy_maximalCells M
    have he : realEnergy {(0,0)}=realEnergy (horizontalStrip 1) := by congr 1
    rw [he] at hm
    have h3 : (3 : ℝ)≤(maximalCells M).card := by exact_mod_cast hmax
    have hp := mul_le_mul_of_nonneg_right h3 (realEnergy_nonneg (horizontalStrip 1))
    linarith [(strip_energy_bounds_1).1]
  · have hc : (maximalCells M).card=2 := by
      have hh := two_le_maximal_card_of_nonrectangle hM hne hr
      omega
    rcases two_maxima_large_seed_bound hM hc hk with hh|hh|hh
    · have hl := tier32.energy_lower
      change (7421 : ℝ)/100000<realEnergy (twoTier 2 1 1 1) at hl
      exact hl.trans_le hh
    · have hl := tier41.energy_lower
      change (7421 : ℝ)/100000<realEnergy (twoTier 1 3 1 1) at hl
      exact hl.trans_le hh
    · have hl := tier311.energy_lower
      change (7421 : ℝ)/100000<realEnergy (twoTier 1 2 1 2) at hl
      exact hl.trans_le hh

/-- A rectangle with at least three rows and columns has the same strong
lower bound, by monotonicity from the actual three-by-three obstruction. -/
theorem rectangle_three_lower {a b : ℕ} (ha : 3≤a) (hb : 3≤b) :
    (7421 : ℝ)/100000<realEnergy (faceRectangle a b) := by
  have hl := square33.energy_lower
  change (7421 : ℝ)/100000<realEnergy (faceRectangle 3 3) at hl
  exact hl.trans_le (rectangle_energy_mono (by decide) (by decide) ha hb)

end
end SpanningTreeIsoperimetry.SingleCornerSmallEnergyBounds
