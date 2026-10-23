module

public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-! Common exact interval for the reciprocal-pi polynomial certificates. -/
namespace SpanningTreeIsoperimetry.RefinedPiBounds
noncomputable section

def center : ℝ := 31830988618379067154/100000000000000000000
def radius : ℝ := 1/100000000000000000000

theorem center_bounds : |1/Real.pi-center|≤radius := by
  have hl := (div_lt_div_of_pos_left (by norm_num : (0 : ℝ)<1) Real.pi_pos Real.pi_lt_d20).le
  have hu := (div_lt_div_of_pos_left (by norm_num : (0 : ℝ)<1)
    (by norm_num : (0 : ℝ)<3.14159265358979323846) Real.pi_gt_d20).le
  norm_num at hl hu
  rw [abs_le]
  constructor <;> dsimp [center,radius] <;> simp only [one_div] <;> linarith

theorem power_bounds (n : ℕ) : |(1/Real.pi-center)^n|≤radius^n := by
  rw [abs_pow]
  have h := center_bounds
  gcongr

end
end SpanningTreeIsoperimetry.RefinedPiBounds
