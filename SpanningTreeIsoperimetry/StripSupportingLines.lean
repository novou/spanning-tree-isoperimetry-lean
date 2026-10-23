module

public import SpanningTreeIsoperimetry.RefinedStripEnergy

@[expose] public section

set_option backward.privateInPublic true

/-! The actual universal strip-energy supporting line used in Appendix B. -/
namespace SpanningTreeIsoperimetry.StripSupportingLines
open Ferrers CornerEnergy RefinedStripEnergy

private theorem increments_antitone : Antitone (fun n : ℕ =>
    realEnergy (horizontalStrip (n+1))-realEnergy (horizontalStrip n)) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := realEnergy_strip_concave n
  linarith

/-- Among two nonempty strips of fixed total size, the most unequal split
has the smallest combined energy. -/
theorem two_strip_energy_minimum (a b : ℕ) (ha : 1≤a) (hb : 1≤b) :
    realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip (a+b-1)) ≤
      realEnergy (horizontalStrip a)+realEnergy (horizontalStrip b) := by
  have h (m n : ℕ) :
      realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip (m+n+1)) ≤
        realEnergy (horizontalStrip (m+1))+realEnergy (horizontalStrip (n+1)) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hd := increments_antitone (show m+1≤m+n+1 by omega)
      change realEnergy (horizontalStrip (m+n+1+1))-
          realEnergy (horizontalStrip (m+n+1)) ≤
        realEnergy (horizontalStrip (m+1+1))-realEnergy (horizontalStrip (m+1)) at hd
      rw [show m+1+n+1=m+n+1+1 by omega]
      linarith
  have hh := h (a-1) (b-1)
  simpa only [show a-1+1=a by omega,show b-1+1=b by omega,
    show a-1+(b-1)+1=a+b-1 by omega] using hh

theorem fifth_energy_bound : realEnergy (horizontalStrip 5)<(4 : ℝ)/75 := by
  linarith [(strip_energy_bounds_5).2]

theorem fifth_increment_lower : (1 : ℝ)/600<
    realEnergy (horizontalStrip 5)-realEnergy (horizontalStrip 4) := by
  linarith [(strip_energy_bounds_5).1,(strip_energy_bounds_4).2]

theorem sixth_increment_upper : realEnergy (horizontalStrip 6)-realEnergy (horizontalStrip 5)<
    (1 : ℝ)/600 := by
  linarith [(strip_energy_bounds_6).2,(strip_energy_bounds_5).1]

/-- This is the actual E_k supporting line, with all six numerical premises
proved from genuine quadrant Green determinants. -/
theorem strip_supporting_line (k : ℕ) :
    realEnergy (horizontalStrip k)<((k : ℝ)+27)/600 := by
  have hright (n : ℕ) : realEnergy (horizontalStrip (5+n))≤
      realEnergy (horizontalStrip 5)+(n : ℝ)/600 := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hinc := increments_antitone (show 5≤5+n by omega)
      change realEnergy (horizontalStrip (5+n+1))-realEnergy (horizontalStrip (5+n))≤
        realEnergy (horizontalStrip 6)-realEnergy (horizontalStrip 5) at hinc
      rw [show 5+(n+1)=5+n+1 by omega]
      push_cast
      linarith [sixth_increment_upper]
  by_cases hk : 5≤k
  · have h := hright (k-5)
    rw [show 5+(k-5)=k by omega] at h
    have hc : ((k-5 : ℕ) : ℝ)=(k : ℝ)-5 := by rw [Nat.cast_sub hk]; norm_num
    rw [hc] at h
    linarith [fifth_energy_bound]
  · have hk4 : k≤4 := by omega
    interval_cases k
    · norm_num [horizontalStrip]
    · norm_num
      linarith [(strip_energy_bounds_1).2]
    · norm_num
      linarith [(strip_energy_bounds_2).2]
    · norm_num
      linarith [(strip_energy_bounds_3).2]
    · norm_num
      linarith [(strip_energy_bounds_4).2]

end SpanningTreeIsoperimetry.StripSupportingLines
