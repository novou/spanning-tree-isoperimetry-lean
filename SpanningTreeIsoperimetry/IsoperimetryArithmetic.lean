module

public import SpanningTreeIsoperimetry.HullArithmetic

@[expose] public section

/-! Square-remainder arithmetic used by the all-cardinality hull comparison. -/
namespace SpanningTreeIsoperimetry

theorem minimum_side_sum_unique {N L M : ℕ}
    (hL : IsMinimumSideSum N L) (hM : IsMinimumSideSum N M) : L=M := by
  have hLlo := hL.2.1
  have hLhi := hL.2.2
  have hMlo := hM.2.1
  have hMhi := hM.2.2
  apply le_antisymm
  · by_contra h
    have hl : M ≤ L-1 := by omega
    have hs := Nat.pow_le_pow_left hl 2
    omega
  · by_contra h
    have hl : L ≤ M-1 := by omega
    have hs := Nat.pow_le_pow_left hl 2
    omega

theorem square_remainder_data {N : ℕ} (hN : 0<N) :
    0<Nat.sqrt N ∧ N=(Nat.sqrt N)^2+(N-(Nat.sqrt N)^2) ∧
      N-(Nat.sqrt N)^2 ≤ 2*Nat.sqrt N := by
  have hsq := Nat.sqrt_le' N
  have hup := Nat.sqrt_le_add N
  have heq := Nat.add_sub_of_le hsq
  refine ⟨Nat.sqrt_pos.mpr hN,by omega,?_⟩
  nlinarith

theorem minimum_side_sum_square_remainder {n q : ℕ} (hn : 0<n) (hq : q≤2*n) :
    IsMinimumSideSum (n^2+q) (2*n+(if q=0 then 0 else if q≤n then 1 else 2)) := by
  by_cases hq0 : q=0
  · subst q
    simp only [↓reduceIte,Nat.add_zero]
    have hpred : 2*n-1+1=2*n := by omega
    refine ⟨by omega,?_,?_⟩ <;> nlinarith
  have hqpos : 0<q := Nat.pos_of_ne_zero hq0
  by_cases hqn : q≤n
  · simp only [hq0,hqn,↓reduceIte]
    refine ⟨by omega,?_,?_⟩
    · rw [Nat.add_sub_cancel]
      nlinarith
    · nlinarith
  · simp only [hq0,hqn,↓reduceIte]
    have hnq : n<q := by omega
    have hpred : 2*n+2-1=2*n+1 := by omega
    refine ⟨by omega,?_,?_⟩
    · rw [hpred]
      nlinarith
    · nlinarith

theorem ceil_sqrt_square_remainder {n q : ℕ} (hn : 0<n) (hq : q≤2*n) :
    ⌈2*Real.sqrt ((n^2+q : ℕ) : ℝ)⌉₊ =
      2*n+(if q=0 then 0 else if q≤n then 1 else 2) :=
  minimum_side_sum_unique (ceil_sqrt_is_minimum_side_sum (by positivity))
    (minimum_side_sum_square_remainder hn hq)

end SpanningTreeIsoperimetry
