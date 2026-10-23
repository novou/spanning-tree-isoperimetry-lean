module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Arithmetic of rectangular hulls

These are the integer and scalar steps in Sections 3, 5, and 9 of the
manuscript. They do not assert any spanning-tree comparison or geometric
decomposition: those statements require separate proofs.
-/

namespace SpanningTreeIsoperimetry

/-- An integer characterization of the least side sum compatible with area `N`.
The strict lower inequality excludes every smaller side sum. -/
def IsMinimumSideSum (N L : ℕ) : Prop :=
  0 < L ∧ (L - 1) ^ 2 < 4 * N ∧ 4 * N ≤ L ^ 2

/-- The manuscript's `ceil (2 sqrt N)` satisfies the integer side-sum test. -/
theorem ceil_sqrt_is_minimum_side_sum {N : ℕ} (hN : 0 < N) :
    IsMinimumSideSum N ⌈2 * Real.sqrt (N : ℝ)⌉₊ := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNreal
  have hpos : 0 < ⌈2 * Real.sqrt (N : ℝ)⌉₊ :=
    Nat.ceil_pos.mpr (by positivity)
  refine ⟨hpos, ?_, ?_⟩
  · have hpred : ⌈2 * Real.sqrt (N : ℝ)⌉₊ - 1 <
        ⌈2 * Real.sqrt (N : ℝ)⌉₊ := by omega
    have hlt := Nat.lt_ceil.mp hpred
    have hsq := (sq_lt_sq₀ (show (0 : ℝ) ≤
        (⌈2 * Real.sqrt (N : ℝ)⌉₊ - 1 : ℕ) by positivity)
        (show (0 : ℝ) ≤ 2 * Real.sqrt (N : ℝ) by positivity)).mpr hlt
    have hreal : ((⌈2 * Real.sqrt (N : ℝ)⌉₊ - 1 : ℕ) : ℝ) ^ 2 < 4 * N := by
      nlinarith [Real.sq_sqrt (le_of_lt hNreal)]
    exact_mod_cast hreal
  · have hle := Nat.le_ceil (2 * Real.sqrt (N : ℝ))
    have hsq := (sq_le_sq₀ (show (0 : ℝ) ≤ 2 * Real.sqrt (N : ℝ) by positivity)
        (show (0 : ℝ) ≤ (⌈2 * Real.sqrt (N : ℝ)⌉₊ : ℝ) by positivity)).mpr hle
    have hreal : 4 * (N : ℝ) ≤ (⌈2 * Real.sqrt (N : ℝ)⌉₊ : ℝ) ^ 2 := by
      nlinarith [Real.sq_sqrt (le_of_lt hNreal)]
    exact_mod_cast hreal

/-- The area of a rectangle bounds the square of its side sum. -/
theorem four_mul_area_le_side_sum_sq (r s : ℕ) :
    4 * (r * s) ≤ (r + s) ^ 2 := by
  nlinarith [sq_nonneg ((r : ℤ) - s)]

/-- No rectangle containing `N` points has side sum below the minimum. -/
theorem minimum_side_sum_le {N L r s : ℕ}
    (hL : IsMinimumSideSum N L) (harea : N ≤ r * s) : L ≤ r + s := by
  by_contra h
  have hsum : r + s ≤ L - 1 := by omega
  have hsq : (r + s) ^ 2 ≤ (L - 1) ^ 2 := Nat.pow_le_pow_left hsum 2
  have hrect := four_mul_area_le_side_sum_sq r s
  have hstrict := hL.2.1
  omega

/-- The short-side deficit bound, in an entirely integer formulation.
This proves the arithmetic part of manuscript Lemma `lem:four-corner`;
the Ferrers decomposition is not asserted here. -/
theorem deficit_lt_min_side {N L r s : ℕ}
    (hL : IsMinimumSideSum N L) (hr : 0 < r) (hs : 0 < s)
    (harea : N ≤ r * s) (hsum : r + s = L) :
    r * s - N < min r s := by
  have hfirst : r * s - N < r := by
    by_contra h
    have harea' : N ≤ r * (s - 1) := by
      have hsub : s - 1 + 1 = s := by omega
      have hdeficit : r * s - N + N = r * s := Nat.sub_add_cancel harea
      nlinarith
    have hmin := minimum_side_sum_le hL harea'
    omega
  have hsecond : r * s - N < s := by
    by_contra h
    have harea' : N ≤ (r - 1) * s := by
      have hsub : r - 1 + 1 = r := by omega
      have hdeficit : r * s - N + N = r * s := Nat.sub_add_cancel harea
      nlinarith
    have hmin := minimum_side_sum_le hL harea'
    omega
  exact lt_min hfirst hsecond

/-- The short-side deficit statement exactly with the paper's real-square-root
notation. Only the cardinality and hull-side assumptions are needed. -/
theorem deficit_lt_min_side_of_ceil_sqrt {N r s : ℕ}
    (hN : 0 < N) (hr : 0 < r) (hs : 0 < s) (harea : N ≤ r * s)
    (hsum : r + s = ⌈2 * Real.sqrt (N : ℝ)⌉₊) :
    r * s - N < min r s :=
  deficit_lt_min_side (ceil_sqrt_is_minimum_side_sum hN) hr hs harea hsum

/-- At square cardinality, zero hull excess forces a square hull. -/
theorem square_hull_of_zero_excess {n r s : ℕ}
    (harea : n ^ 2 ≤ r * s) (hsum : r + s = 2 * n) :
    r = n ∧ s = n := by
  have hsq : (r : ℤ) = n := by
    have harea' : (n : ℤ) ^ 2 ≤ (r : ℤ) * s := by exact_mod_cast harea
    have hsum' : (r : ℤ) + s = 2 * n := by exact_mod_cast hsum
    nlinarith [sq_nonneg ((r : ℤ) - n)]
  have hr : r = n := by exact_mod_cast hsq
  constructor
  · exact hr
  · omega

/-- Any nonzero collection of integer defects incurs at least `δ`. -/
theorem positive_integer_defect_charge {α δ : ℝ} {β g c : ℕ}
    (hδ : 0 ≤ δ) (hα : δ ≤ α) (hcount : 0 < β + g + c) :
    δ ≤ α * ((β : ℝ) + g) + δ * c := by
  have hcount' : (1 : ℝ) ≤ (β : ℝ) + g + c := by exact_mod_cast hcount
  have hbg : 0 ≤ (β : ℝ) + g := by positivity
  have hextra := mul_nonneg (sub_nonneg.mpr hα) hbg
  have hbase := mul_nonneg hδ (sub_nonneg.mpr hcount')
  nlinarith

/-- The numerical budget with at most two leaf seeds is strictly below `δ`.
No positivity assumption on the bulk-minus-boundary gap is needed. -/
theorem leaf_seed_budget_lt {δ gap : ℝ} {j : ℕ}
    (hδ : 0 < δ) (hgap : 2 * gap < δ) (hj : j ≤ 2) :
    (j : ℝ) * gap < δ := by
  have hj' : (j : ℝ) ≤ 2 := by exact_mod_cast hj
  by_cases hnonneg : 0 ≤ gap
  · have hmul := mul_le_mul_of_nonneg_right hj' hnonneg
    linarith
  · have hmul : (j : ℝ) * gap ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith

/-- The integer elimination step in `prop:integer-rigidity`.
The graph-theoretic comparison yielding `hbudget` is a separate dependency. -/
theorem integer_defects_vanish {α δ gap : ℝ} {β g c j : ℕ}
    (hδ : 0 < δ) (hα : δ ≤ α) (hgap : 2 * gap < δ) (hj : j ≤ 2)
    (hbudget : α * ((β : ℝ) + g) + δ * c ≤ (j : ℝ) * gap) :
    β = 0 ∧ g = 0 ∧ c = 0 := by
  have hsmall := leaf_seed_budget_lt hδ hgap hj
  have hzero : β + g + c = 0 := by
    by_contra h
    have hcount : 0 < β + g + c := Nat.pos_of_ne_zero h
    have hlarge := positive_integer_defect_charge (le_of_lt hδ) hα hcount
    linarith
  omega

/-- The area identity underlying the explicit hull selector. -/
theorem selector_area_identity (m e t : ℤ) :
    (m - t) * (m + e + t) = m * (m + e) - t * (t + e) := by
  ring

/-- The deficit changes by precisely the difference between adjacent hull sides. -/
theorem selector_deficit_step (m e d t : ℤ) :
    d - (t + 1) * (t + 1 + e) =
      (d - t * (t + e)) - ((m + e + t) - (m - t) + 1) := by
  ring

/-- The quadratic index test specifies the last admissible selector index. -/
theorem selector_index_maximal {d e T t : ℕ}
    (hnext : d < (T + 1) * (T + 1 + e))
    (ht : t * (t + e) ≤ d) : t ≤ T := by
  by_contra h
  have hT : T + 1 ≤ t := by omega
  have hprod : (T + 1) * (T + 1 + e) ≤ t * (t + e) :=
    Nat.mul_le_mul hT (by omega)
  omega

/-- Every index up to a feasible endpoint is feasible. -/
theorem selector_index_feasible {d e T t : ℕ}
    (hT : T * (T + e) ≤ d) (ht : t ≤ T) : t * (t + e) ≤ d := by
  exact le_trans (Nat.mul_le_mul ht (by omega)) hT

/-- The remaining strip deficit is smaller than the next area decrement. -/
theorem selector_remainder_lt_step {d e T : ℕ}
    (hT : T * (T + e) ≤ d) (hnext : d < (T + 1) * (T + 1 + e)) :
    d - T * (T + e) < 2 * T + e + 1 := by
  have hidentity : (T + 1) * (T + 1 + e) =
      T * (T + e) + (2 * T + e + 1) := by ring
  omega

/-- Positive cardinality ensures that the selected short side remains positive. -/
theorem selector_index_lt_half_sum {N m e d T : ℕ}
    (hN : 0 < N) (harea : m * (m + e) = N + d)
    (hT : T * (T + e) ≤ d) : T < m := by
  by_contra h
  have hm : m ≤ T := by omega
  have hprod := Nat.mul_le_mul hm (show m + e ≤ T + e by omega)
  omega

/-- The explicit selector index, evaluated using only an integer square root. -/
def selectorIndex (d e : ℕ) : ℕ := (Nat.sqrt (e ^ 2 + 4 * d) - e) / 2

/-- The integer-square-root implementation lies at the exact quadratic cutoff. -/
theorem selectorIndex_bounds (d e : ℕ) :
    selectorIndex d e * (selectorIndex d e + e) ≤ d ∧
      d < (selectorIndex d e + 1) * (selectorIndex d e + 1 + e) := by
  let q := Nat.sqrt (e ^ 2 + 4 * d)
  have he : e ≤ q := Nat.le_sqrt'.mpr (by omega)
  have hqlo : q ^ 2 ≤ e ^ 2 + 4 * d := Nat.sqrt_le' _
  have hqhi : e ^ 2 + 4 * d < (q + 1) ^ 2 := Nat.lt_succ_sqrt' _
  have hsub : q - e + e = q := Nat.sub_add_cancel he
  have hdivlo : 2 * ((q - e) / 2) ≤ q - e := by omega
  have hdivhi : q - e < 2 * (((q - e) / 2) + 1) := by omega
  have hlower : 2 * ((q - e) / 2) + e ≤ q := by omega
  have hupper : q + 1 ≤ 2 * (((q - e) / 2) + 1) + e := by omega
  have hsquarelo := Nat.pow_le_pow_left hlower 2
  have hsquarehi := Nat.pow_le_pow_left hupper 2
  change ((q - e) / 2) * (((q - e) / 2) + e) ≤ d ∧
    d < (((q - e) / 2) + 1) * (((q - e) / 2) + 1 + e)
  constructor <;> nlinarith

/-- The admissible indices are exactly `0,...,selectorIndex d e`. -/
theorem selectorIndex_feasible_iff (d e t : ℕ) :
    t * (t + e) ≤ d ↔ t ≤ selectorIndex d e := by
  constructor
  · exact selector_index_maximal (selectorIndex_bounds d e).2
  · exact selector_index_feasible (selectorIndex_bounds d e).1

/-- The integer-square-root implementation equals the real floor formula in
`eq:selector-dT`. -/
theorem selectorIndex_eq_floor (d e : ℕ) :
    selectorIndex d e =
      ⌊(Real.sqrt ((e : ℝ) ^ 2 + 4 * d) - e) / 2⌋₊ := by
  have hroot : (e : ℝ) ≤ Real.sqrt ((e : ℝ) ^ 2 + 4 * d) :=
    Real.le_sqrt_of_sq_le (by nlinarith [Nat.cast_nonneg (α := ℝ) d])
  have harg : (0 : ℝ) ≤ (Real.sqrt ((e : ℝ) ^ 2 + 4 * d) - e) / 2 := by
    linarith
  have hlow : (selectorIndex d e : ℝ) * (selectorIndex d e + e) ≤ d := by
    exact_mod_cast (selectorIndex_bounds d e).1
  have hhigh : (d : ℝ) <
      (selectorIndex d e + 1) * (selectorIndex d e + 1 + e) := by
    exact_mod_cast (selectorIndex_bounds d e).2
  have hlower : 2 * (selectorIndex d e : ℝ) + e ≤
      Real.sqrt ((e : ℝ) ^ 2 + 4 * d) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hupper : Real.sqrt ((e : ℝ) ^ 2 + 4 * d) <
      2 * ((selectorIndex d e : ℝ) + 1) + e := by
    apply (Real.sqrt_lt (by positivity) (by positivity)).mpr
    nlinarith
  symm
  exact (Nat.floor_eq_iff harg).mpr ⟨by linarith, by linarith⟩

/-- The balanced rectangle of the prescribed side sum has enough area. The
parity restriction is what converts `4N ≤ L²` into the integer area bound. -/
theorem balanced_area_ge {N L m e : ℕ} (hL : IsMinimumSideSum N L)
    (hsum : L = 2 * m + e) (he : e ≤ 1) : N ≤ m * (m + e) := by
  have hsquare := hL.2.2
  have he2 : e ^ 2 ≤ 1 := by simpa using Nat.pow_le_pow_left he 2
  nlinarith

/-- The selector constructs positive sides, the required side sum, and a
deficit strictly smaller than the short side. This includes the full arithmetic
admissibility of the strip in `eq:selector-rsk`, but no tree-count optimality. -/
theorem selected_hull_properties {N L m e : ℕ} (hN : 0 < N)
    (hL : IsMinimumSideSum N L) (hsum : L = 2 * m + e) (he : e ≤ 1) :
    let d := m * (m + e) - N
    let T := selectorIndex d e
    let r := m - T
    let s := m + e + T
    let k := d - T * (T + e)
    0 < r ∧ r ≤ s ∧ r + s = L ∧ r * s = N + k ∧ k < r := by
  dsimp only
  let d := m * (m + e) - N
  let T := selectorIndex d e
  change 0 < m - T ∧ m - T ≤ m + e + T ∧
    (m - T) + (m + e + T) = L ∧
    (m - T) * (m + e + T) = N + (d - T * (T + e)) ∧
    d - T * (T + e) < m - T
  have hbal := balanced_area_ge hL hsum he
  have harea : m * (m + e) = N + d := by dsimp [d]; omega
  have hfeasible : T * (T + e) ≤ d := (selectorIndex_bounds d e).1
  have hTm : T < m := selector_index_lt_half_sum hN harea hfeasible
  have hsub : m - T + T = m := Nat.sub_add_cancel (le_of_lt hTm)
  have hdeficit : d - T * (T + e) + T * (T + e) = d :=
    Nat.sub_add_cancel hfeasible
  have hr : 0 < m - T := by omega
  have hrs : m - T ≤ m + e + T := by omega
  have hsum' : (m - T) + (m + e + T) = L := by omega
  have hproduct : (m - T) * (m + e + T) = N + (d - T * (T + e)) := by
    nlinarith
  refine ⟨hr, hrs, hsum', hproduct, ?_⟩
  have hbound := deficit_lt_min_side hL hr
    (show 0 < m + e + T by omega)
    (show N ≤ (m - T) * (m + e + T) by omega) hsum'
  rw [min_eq_left hrs] at hbound
  omega

/-- Specialization to the actual side-sum ceiling and quotient/remainder used
by the manuscript's selector. -/
theorem selected_hull_properties_of_ceil {N : ℕ} (hN : 0 < N) :
    let L := ⌈2 * Real.sqrt (N : ℝ)⌉₊
    let m := L / 2
    let e := L % 2
    let d := m * (m + e) - N
    let T := selectorIndex d e
    let r := m - T
    let s := m + e + T
    let k := d - T * (T + e)
    0 < r ∧ r ≤ s ∧ r + s = L ∧ r * s = N + k ∧ k < r := by
  apply selected_hull_properties hN (ceil_sqrt_is_minimum_side_sum hN)
  · omega
  · omega

/-- A scalar bound for the mixed short-side/long-side stability case. -/
theorem unit_interval_stability_bound {y z : ℝ}
    (hy : 0 ≤ y) (hyz : y ≤ z) (hz : z ≤ 1) :
    (1 - y) * (z ^ 2 + y) ≤ z := by
  have hz0 : 0 ≤ z := le_trans hy hyz
  by_cases hsum : y + z ≤ 1
  · have hproduct := mul_nonneg (sub_nonneg.mpr hyz)
      (show 0 ≤ 1 - z - y by linarith)
    have hlast := mul_nonneg hy (sq_nonneg z)
    nlinarith
  · have hu : 0 ≤ z - (1 - y) := by linarith
    have hfactor : 0 ≤ 1 + z ^ 2 - z - (1 - y) := by
      nlinarith [sq_nonneg (1 - z)]
    have hproduct := mul_nonneg hu hfactor
    have hlast := mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz)
    nlinarith

/-- The short-side scalar inequality in `lem:geometric-asymmetry`. This proof
uses only `y ≤ sqrt x`, a consequence of the area constraint; it avoids a
separate convexity argument with a divided square-root endpoint. -/
theorem stability_mixed_side_bound {x y : ℝ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y)
    (harea : y ^ 2 ≤ x * (1 - y)) :
    (1 - y) * (x + y) ≤ Real.sqrt x := by
  have hsqrt := Real.sqrt_nonneg x
  have hsquare := Real.sq_sqrt hx
  have hyroot : y ≤ Real.sqrt x := by
    nlinarith [mul_nonneg hx hy]
  have hroot : Real.sqrt x ≤ 1 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by nlinarith⟩
  simpa only [hsquare] using unit_interval_stability_bound hy hyroot hroot

/-- The scalar estimate used when both hull sides exceed the square side in
`lem:geometric-asymmetry`. The geometric covering estimates are separate. -/
theorem stability_min_bound {x : ℝ} (hx : 0 ≤ x) :
    min (x + x ^ 2 / 4) (3 / 4) ≤ Real.sqrt x := by
  have hsqrt := Real.sqrt_nonneg x
  have hsquare := Real.sq_sqrt hx
  by_cases hsmall : x ≤ 9 / 16
  · apply le_trans (min_le_left _ _)
    have hroot : Real.sqrt x ≤ 3 / 4 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by nlinarith⟩
    have hquad : x ^ 2 ≤ (9 / 16) * x := by
      nlinarith [mul_nonneg hx (sub_nonneg.mpr hsmall)]
    have hlinear : x ≤ (3 / 4) * Real.sqrt x := by
      nlinarith [mul_nonneg hsqrt (sub_nonneg.mpr hroot)]
    nlinarith
  · apply le_trans (min_le_right _ _)
    nlinarith

/-- Exhaustive arithmetic equality cases for neighboring hulls, as listed in
`eq:adjacent-equality-list`. The equality criterion for tree counts itself is
not assumed proved by this lemma. -/
theorem adjacent_hull_equality_iff {r s k : ℤ}
    (hr : 1 ≤ r) (hrs : r ≤ s) (hk : 0 ≤ k) (hkr : k < r)
    (hnext : 0 ≤ k - (s - r + 1)) :
    (s - 1 - k ≤ 1 ∧ k - (s - r + 1) ≤ 1) ↔
      (r = 2 ∧ s = 2 ∧ k = 1) ∨
      (r = 3 ∧ s = 3 ∧ k = 2) ∨
      (r = 3 ∧ s = 3 ∧ k = 1) ∨
      (r = 3 ∧ s = 4 ∧ k = 2) ∨
      (r = 4 ∧ s = 4 ∧ k = 2) ∨
      (r = 4 ∧ s = 5 ∧ k = 3) := by
  omega

/-- All neighboring-hull equality cases have cardinality at most 17. -/
theorem adjacent_hull_equality_card_le_seventeen {r s k : ℤ}
    (hr : 1 ≤ r) (hrs : r ≤ s) (hk : 0 ≤ k) (hkr : k < r)
    (hnext : 0 ≤ k - (s - r + 1))
    (heq : s - 1 - k ≤ 1 ∧ k - (s - r + 1) ≤ 1) :
    r * s - k ≤ 17 := by
  rcases (adjacent_hull_equality_iff hr hrs hk hkr hnext).mp heq with
    h | h | h | h | h | h <;> rcases h with ⟨rfl, rfl, rfl⟩ <;> norm_num

end SpanningTreeIsoperimetry
