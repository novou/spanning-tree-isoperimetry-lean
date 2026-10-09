import SpanningTreeIsoperimetry.Grid
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-!
# Nonnegative sign expansion for discrete polarization

The finite sign-sum inequality is the algebraic ingredient in the manuscript's
polarization proof. Spin monomials allow repeated orbit indices and arbitrary
interaction patterns. Concrete lattice trace and determinant applications are
separate from this generic inequality.
-/

namespace SpanningTreeIsoperimetry.Polarization

open scoped BigOperators

def spin (b : Bool) : ℝ := if b then 1 else -1

def spinMonomial {I : Type*} [Fintype I] [DecidableEq I] (e : I → ℕ) (s : I → Bool) : ℝ :=
  ∏ i, spin (s i) ^ e i

def spinMoment {I : Type*} [Fintype I] [DecidableEq I] (e : I → ℕ) : ℝ :=
  ∑ s : I → Bool, spinMonomial e s

theorem spinMoment_eq {I : Type*} [Fintype I] [DecidableEq I] (e : I → ℕ) :
    spinMoment e = ∏ i, (1 + (-1 : ℝ) ^ e i) := by
  classical
  unfold spinMoment spinMonomial
  rw [← Fintype.prod_sum (fun i (b : Bool) => spin b ^ e i)]
  simp [spin]

theorem spinMoment_nonneg {I : Type*} [Fintype I] [DecidableEq I] (e : I → ℕ) :
    0 ≤ spinMoment e := by
  rw [spinMoment_eq]
  apply Finset.prod_nonneg
  intro i _
  rcases neg_one_pow_eq_or ℝ (e i) with h | h <;> simp [h]

theorem prod_spinMonomial {I J : Type*} [Fintype I] [DecidableEq I] (T : Finset J)
    (e : J → I → ℕ) (s : I → Bool) :
    (∏ j ∈ T, spinMonomial (e j) s) = spinMonomial (fun i => ∑ j ∈ T, e j i) s := by
  unfold spinMonomial
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  exact Finset.prod_pow_eq_pow_sum T (fun j => e j i) (spin (s i))

/-- A finite interaction system, allowing both occupancy and edge factors. -/
def signSum {I J : Type*} [Fintype I] [DecidableEq I] (T : Finset J)
    (a d : J → ℝ) (e : J → I → ℕ) : ℝ :=
  ∑ s : I → Bool, ∏ j ∈ T, (a j + d j * spinMonomial (e j) s)

theorem signSum_expansion {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (T : Finset J) (a d : J → ℝ) (e : J → I → ℕ) :
    signSum T a d e = ∑ S ∈ T.powerset,
      ((∏ j ∈ S, a j) * ∏ j ∈ T \ S, d j) *
        spinMoment (fun i => ∑ j ∈ T \ S, e j i) := by
  classical
  unfold signSum
  simp_rw [Finset.prod_add, Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  simp_rw [← mul_assoc, prod_spinMonomial]
  rw [← Finset.mul_sum]
  rfl

/-- Taking absolute values of all signed coefficients can only increase the
complete sum over signs. The constant coefficients need only be nonnegative. -/
theorem signSum_le_abs {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (T : Finset J) (a d : J → ℝ) (e : J → I → ℕ)
    (ha : ∀ j ∈ T, 0 ≤ a j) :
    signSum T a d e ≤ signSum T a (fun j => |d j|) e := by
  rw [signSum_expansion, signSum_expansion]
  apply Finset.sum_le_sum
  intro S hS
  have hsub := Finset.mem_powerset.mp hS
  have hconst : 0 ≤ ∏ j ∈ S, a j := Finset.prod_nonneg (fun j hj => ha j (hsub hj))
  have hd : (∏ j ∈ T \ S, d j) ≤ ∏ j ∈ T \ S, |d j| := by
    simpa only [Finset.abs_prod] using le_abs_self (∏ j ∈ T \ S, d j)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hconst) (spinMoment_nonneg _)

theorem spinMoment_of_even {I : Type*} [Fintype I] [DecidableEq I]
    (e : I → ℕ) (he : ∀ i, Even (e i)) : spinMoment e = 2 ^ Fintype.card I := by
  rw [spinMoment_eq]
  simp only [(he _).neg_one_pow, one_add_one_eq_two, Finset.prod_const, Finset.card_univ]

theorem signSum_lt_abs {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    (T : Finset J) (a d : J → ℝ) (e : J → I → ℕ)
    (ha : ∀ j ∈ T, 0 ≤ a j) (S : Finset J) (hS : S ⊆ T)
    (hconst : 0 < ∏ j ∈ S, a j) (hneg : (∏ j ∈ T \ S, d j) < 0)
    (heven : ∀ i, Even (∑ j ∈ T \ S, e j i)) :
    signSum T a d e < signSum T a (fun j => |d j|) e := by
  rw [signSum_expansion, signSum_expansion]
  apply Finset.sum_lt_sum
  · intro R hR
    have hr := Finset.mem_powerset.mp hR
    have hc : 0 ≤ ∏ j ∈ R, a j := Finset.prod_nonneg (fun j hj => ha j (hr hj))
    have hd : (∏ j ∈ T \ R, d j) ≤ ∏ j ∈ T \ R, |d j| := by
      simpa only [Finset.abs_prod] using le_abs_self (∏ j ∈ T \ R, d j)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hc) (spinMoment_nonneg _)
  · refine ⟨S, Finset.mem_powerset.mpr hS, ?_⟩
    have hm : 0 < spinMoment (fun i => ∑ j ∈ T \ S, e j i) := by
      rw [spinMoment_of_even _ heven]
      positivity
    have hd : (∏ j ∈ T \ S, d j) < ∏ j ∈ T \ S, |d j| := by
      rw [← Finset.abs_prod, abs_of_neg hneg]
      linarith
    exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hd hconst) hm

theorem spinMonomial_add {I : Type*} [Fintype I] [DecidableEq I]
    (e f : I → ℕ) (s : I → Bool) :
    spinMonomial (fun i => e i + f i) s = spinMonomial e s * spinMonomial f s := by
  simp only [spinMonomial, pow_add, Finset.prod_mul_distrib]

theorem spinMonomial_single {I : Type*} [Fintype I] [DecidableEq I]
    (k : I) (s : I → Bool) :
    spinMonomial (fun i => if i = k then 1 else 0) s = spin (s k) := by
  unfold spinMonomial
  rw [Finset.prod_eq_single k]
  · simp
  · intro i _ hik
    simp [hik]
  · simp

theorem spinMonomial_pair {I : Type*} [Fintype I] [DecidableEq I]
    (k l : I) (s : I → Bool) :
    spinMonomial (fun i => (if i = k then 1 else 0) + (if i = l then 1 else 0)) s =
      spin (s k) * spin (s l) := by
  rw [spinMonomial_add, spinMonomial_single, spinMonomial_single]

/-- Sign sum for pair interactions and occupancy factors. Repeated endpoints
are allowed, so this also covers holding steps and one-position cycles. -/
def interactionSum {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E]
    (left right : E → I) (a b : E → ℝ) (c d : I → ℝ) : ℝ :=
  ∑ s : I → Bool,
    (∏ e, (a e + b e * (spin (s (left e)) * spin (s (right e))))) *
      ∏ i, (c i + d i * spin (s i))

theorem interactionSum_eq_signSum {I E : Type*} [Fintype I] [DecidableEq I]
    [Fintype E] [DecidableEq E] (left right : E → I)
    (a b : E → ℝ) (c d : I → ℝ) :
    interactionSum left right a b c d =
      signSum (Finset.univ : Finset (E ⊕ I)) (Sum.elim a c) (Sum.elim b d)
        (Sum.elim (fun e i => (if i = left e then 1 else 0) + (if i = right e then 1 else 0))
          (fun j i => if i = j then 1 else 0)) := by
  unfold interactionSum signSum
  apply Finset.sum_congr rfl
  intro s _
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    spinMonomial_pair, spinMonomial_single]

/-- The complete finite ferromagnetic sign-sum inequality used by polarization. -/
theorem interactionSum_polarization {I E : Type*} [Fintype I] [DecidableEq I]
    [Fintype E] [DecidableEq E] (left right : E → I)
    (a b : E → ℝ) (c d : I → ℝ)
    (ha : ∀ e, 0 ≤ a e) (hb : ∀ e, 0 ≤ b e) (hc : ∀ i, 0 ≤ c i) :
    interactionSum left right a b c d ≤ interactionSum left right a b c (fun i => |d i|) := by
  rw [interactionSum_eq_signSum, interactionSum_eq_signSum]
  have hd : (fun j : E ⊕ I => |Sum.elim b d j|) = Sum.elim b (fun i => |d i|) := by
    funext j
    cases j <;> simp [abs_of_nonneg (hb _)]
  rw [← hd]
  apply signSum_le_abs
  intro j _
  cases j with
  | inl e => exact ha e
  | inr i => exact hc i

theorem pair_factor (s t : Bool) (u v : ℝ) :
    (if s = t then u else v) = (u + v) / 2 + (u - v) / 2 * (spin s * spin t) := by
  cases s <;> cases t <;> norm_num [spin] <;> ring

theorem occupancy_factor (s : Bool) (u v : ℝ) :
    (if s then u else v) = (u + v) / 2 + (u - v) / 2 * spin s := by
  cases s <;> norm_num [spin] <;> ring

/-- A finite two-point system, written in same-side/cross-side kernel values
and the occupancies of the two points in each orbit. -/
def twoPointSum {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E]
    (left right : E → I) (same cross : E → ℝ) (plus minus : I → ℝ) : ℝ :=
  ∑ s : I → Bool,
    (∏ e, if s (left e) = s (right e) then same e else cross e) *
      ∏ i, if s i then plus i else minus i

theorem twoPointSum_eq_interaction {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E]
    (left right : E → I) (same cross : E → ℝ) (plus minus : I → ℝ) :
    twoPointSum left right same cross plus minus =
      interactionSum left right (fun e => (same e + cross e) / 2)
        (fun e => (same e - cross e) / 2)
        (fun i => (plus i + minus i) / 2) (fun i => (plus i - minus i) / 2) := by
  unfold twoPointSum interactionSum
  simp only [pair_factor, show spin true = 1 from rfl, mul_one]

theorem max_min_difference (u v : ℝ) :
    (max u v - min u v) / 2 = |(u - v) / 2| := by
  by_cases huv : u ≤ v
  · rw [max_eq_right huv, min_eq_left huv, abs_of_nonpos (by linarith)]
    ring
  · have hvu := le_of_not_ge huv
    rw [max_eq_left hvu, min_eq_right hvu, abs_of_nonneg (by linarith)]

/-- Complete finite two-point polarization: align the larger occupancy with
the preferred sign whenever the same-side kernel dominates the cross-side kernel. -/
theorem twoPointSum_polarization {I E : Type*} [Fintype I] [DecidableEq I]
    [Fintype E] [DecidableEq E] (left right : E → I)
    (same cross : E → ℝ) (plus minus : I → ℝ)
    (hcross : ∀ e, 0 ≤ cross e) (hdom : ∀ e, cross e ≤ same e)
    (hplus : ∀ i, 0 ≤ plus i) (hminus : ∀ i, 0 ≤ minus i) :
    twoPointSum left right same cross plus minus ≤
      twoPointSum left right same cross (fun i => max (plus i) (minus i))
        (fun i => min (plus i) (minus i)) := by
  rw [twoPointSum_eq_interaction, twoPointSum_eq_interaction]
  simp only [max_add_min, max_min_difference]
  apply interactionSum_polarization
  · intro e
    exact div_nonneg (add_nonneg ((hcross e).trans (hdom e)) (hcross e)) (by norm_num)
  · intro e
    exact div_nonneg (sub_nonneg.mpr (hdom e)) (by norm_num)
  · intro i
    exact div_nonneg (add_nonneg (hplus i) (hminus i)) (by norm_num)

noncomputable def adjacencyKernel (x y : Vertex) : ℝ := by
  classical
  exact if lattice.Adj x y then 1 else 0

noncomputable def holdingKernel (x y : Vertex) : ℝ :=
  (if x = y then 1 else 0) + adjacencyKernel x y

theorem adjacencyKernel_nonneg (x y : Vertex) : 0 ≤ adjacencyKernel x y := by
  unfold adjacencyKernel
  split_ifs <;> norm_num

theorem holdingKernel_nonneg (x y : Vertex) : 0 ≤ holdingKernel x y := by
  unfold holdingKernel
  exact add_nonneg (by split_ifs <;> norm_num) (adjacencyKernel_nonneg x y)

/-- Reflection about the horizontal line `y=c/2`, including axes between rows. -/
def axialReflection (c : ℤ) (x : Vertex) : Vertex := (x.1, c - x.2)

@[simp] theorem axialReflection_involutive (c : ℤ) (x : Vertex) :
    axialReflection c (axialReflection c x) = x := by
  ext <;> simp [axialReflection]

theorem axial_cross_adj_eq (c : ℤ) (x y : Vertex)
    (hx : c < 2 * x.2) (hy : c < 2 * y.2)
    (hadj : lattice.Adj x (axialReflection c y)) : x = y := by
  change (x.1 = y.1 ∧ |x.2 - (c - y.2)| = 1) ∨
    (x.2 = c - y.2 ∧ |x.1 - y.1| = 1) at hadj
  rcases hadj with ⟨hfst, hsnd⟩ | ⟨hsnd, _⟩
  · rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at hsnd
    exact Prod.ext hfst (by omega)
  · omega

theorem axial_holdingKernel_domination (c : ℤ) (x y : Vertex)
    (hx : c < 2 * x.2) (hy : c < 2 * y.2) :
    holdingKernel x (axialReflection c y) ≤ holdingKernel x y := by
  have hne : x ≠ axialReflection c y := by
    intro heq
    have he := congrArg Prod.snd heq
    dsimp [axialReflection] at he
    omega
  by_cases ha : lattice.Adj x (axialReflection c y)
  · have heq := axial_cross_adj_eq c x y hx hy ha
    subst y
    simp [holdingKernel, adjacencyKernel, hne, ha]
  · simp only [holdingKernel, adjacencyKernel, ite_eq_right hne, ite_eq_right ha, zero_add]
    split_ifs <;> norm_num

theorem diagonal_no_cross_edge (x y : Vertex) (hx : x.1 < x.2) (hy : y.1 < y.2) :
    ¬lattice.Adj x y.swap := by
  change ¬((x.1 = y.2 ∧ |x.2 - y.1| = 1) ∨
    (x.2 = y.1 ∧ |x.1 - y.2| = 1))
  intro h
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
    rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at h₂ <;> omega

theorem diagonal_adjacencyKernel_domination (x y : Vertex)
    (hx : x.1 < x.2) (hy : y.1 < y.2) :
    adjacencyKernel x y.swap ≤ adjacencyKernel x y := by
  rw [adjacencyKernel, ite_eq_right (diagonal_no_cross_edge x y hx hy)]
  exact adjacencyKernel_nonneg x y

/-- Polarization of a finite set under an involution, toward the chosen side.
At a fixed point the two membership conditions coincide. -/
def polarized (U : Domain) (reflect : Vertex → Vertex) (preferred : Vertex → Prop)
    [DecidablePred preferred] : Domain :=
  (U ∪ U.image reflect).filter fun x =>
    if preferred x then x ∈ U ∨ reflect x ∈ U else x ∈ U ∧ reflect x ∈ U

theorem mem_polarized {U : Domain} {reflect : Vertex → Vertex}
    (hr : Function.Involutive reflect) {preferred : Vertex → Prop} [DecidablePred preferred]
    (x : Vertex) :
    x ∈ polarized U reflect preferred ↔
      if preferred x then x ∈ U ∨ reflect x ∈ U else x ∈ U ∧ reflect x ∈ U := by
  rw [polarized, Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    have hor : x ∈ U ∨ reflect x ∈ U := by
      split_ifs at h
      · exact h
      · exact Or.inl h.1
    rcases hor with hx | hx
    · exact Finset.mem_union_left _ hx
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨reflect x, hx, hr x⟩)

def occupancy (U : Domain) (x : Vertex) : ℝ := if x ∈ U then 1 else 0

theorem occupancy_nonneg (U : Domain) (x : Vertex) : 0 ≤ occupancy U x := by
  unfold occupancy
  split_ifs <;> norm_num

theorem polarized_occupancy_plus {U : Domain} {reflect : Vertex → Vertex}
    (hr : Function.Involutive reflect) {preferred : Vertex → Prop} [DecidablePred preferred]
    {x : Vertex} (hx : preferred x) :
    occupancy (polarized U reflect preferred) x = max (occupancy U x) (occupancy U (reflect x)) := by
  unfold occupancy
  simp only [mem_polarized hr, hx, ite_true]
  by_cases h₁ : x ∈ U <;> by_cases h₂ : reflect x ∈ U <;> simp [h₁, h₂]

theorem polarized_occupancy_minus {U : Domain} {reflect : Vertex → Vertex}
    (hr : Function.Involutive reflect) {preferred : Vertex → Prop} [DecidablePred preferred]
    {x : Vertex} (hx : ¬preferred (reflect x)) :
    occupancy (polarized U reflect preferred) (reflect x) =
      min (occupancy U x) (occupancy U (reflect x)) := by
  unfold occupancy
  simp only [mem_polarized hr, hx, ite_false, hr x]
  by_cases h₁ : x ∈ U <;> by_cases h₂ : reflect x ∈ U <;> simp [h₁, h₂]

/-- The actual axial lattice-kernel sign sum improves after polarizing the set.
Indices are occurrence positions, so repeated reflection orbits cause no restriction. -/
theorem axial_orbit_sum_polarization {I E : Type*} [Fintype I] [DecidableEq I]
    [Fintype E] [DecidableEq E] (left right : E → I) (v : I → Vertex)
    (c : ℤ) (U : Domain) (hv : ∀ i, c < 2 * (v i).2) :
    twoPointSum left right
      (fun e => holdingKernel (v (left e)) (v (right e)))
      (fun e => holdingKernel (v (left e)) (axialReflection c (v (right e))))
      (fun i => occupancy U (v i)) (fun i => occupancy U (axialReflection c (v i))) ≤
    twoPointSum left right
      (fun e => holdingKernel (v (left e)) (v (right e)))
      (fun e => holdingKernel (v (left e)) (axialReflection c (v (right e))))
      (fun i => occupancy (polarized U (axialReflection c) (fun x => c < 2 * x.2)) (v i))
      (fun i => occupancy (polarized U (axialReflection c) (fun x => c < 2 * x.2))
        (axialReflection c (v i))) := by
  have hp (i : I) := polarized_occupancy_plus (U := U)
    (preferred := fun x => c < 2 * x.2) (axialReflection_involutive c) (hv i)
  have hn (i : I) := polarized_occupancy_minus (U := U)
    (preferred := fun x => c < 2 * x.2) (axialReflection_involutive c)
    (x := v i) (by dsimp [axialReflection]; have := hv i; omega)
  simp_rw [hp, hn]
  exact twoPointSum_polarization left right _ _ _ _
    (fun _ => holdingKernel_nonneg _ _)
    (fun e => axial_holdingKernel_domination c _ _ (hv (left e)) (hv (right e)))
    (fun _ => occupancy_nonneg _ _) (fun _ => occupancy_nonneg _ _)

/-- The corresponding concrete ordinary-kernel inequality for diagonal folds. -/
theorem diagonal_orbit_sum_polarization {I E : Type*} [Fintype I] [DecidableEq I]
    [Fintype E] [DecidableEq E] (left right : E → I) (v : I → Vertex)
    (U : Domain) (hv : ∀ i, (v i).1 < (v i).2) :
    twoPointSum left right
      (fun e => adjacencyKernel (v (left e)) (v (right e)))
      (fun e => adjacencyKernel (v (left e)) (v (right e)).swap)
      (fun i => occupancy U (v i)) (fun i => occupancy U (v i).swap) ≤
    twoPointSum left right
      (fun e => adjacencyKernel (v (left e)) (v (right e)))
      (fun e => adjacencyKernel (v (left e)) (v (right e)).swap)
      (fun i => occupancy (polarized U Prod.swap (fun x => x.1 < x.2)) (v i))
      (fun i => occupancy (polarized U Prod.swap (fun x => x.1 < x.2)) (v i).swap) := by
  have hp (i : I) := polarized_occupancy_plus (U := U)
    (preferred := fun x : Vertex => x.1 < x.2) Prod.swap_swap (hv i)
  have hn (i : I) := polarized_occupancy_minus (U := U)
    (preferred := fun x : Vertex => x.1 < x.2) Prod.swap_swap
    (x := v i) (by dsimp; have := hv i; omega)
  simp_rw [hp, hn]
  exact twoPointSum_polarization left right _ _ _ _
    (fun _ => adjacencyKernel_nonneg _ _)
    (fun e => diagonal_adjacencyKernel_domination _ _ (hv (left e)) (hv (right e)))
    (fun _ => occupancy_nonneg _ _) (fun _ => occupancy_nonneg _ _)

theorem axial_adjacency_invariant (c : ℤ) (x y : Vertex) :
    lattice.Adj (axialReflection c x) (axialReflection c y) ↔ lattice.Adj x y := by
  change (x.1 = y.1 ∧ |(c - x.2) - (c - y.2)| = 1) ∨
    (c - x.2 = c - y.2 ∧ |x.1 - y.1| = 1) ↔
      (x.1 = y.1 ∧ |x.2 - y.2| = 1) ∨ (x.2 = y.2 ∧ |x.1 - y.1| = 1)
  rw [show (c - x.2) - (c - y.2) = -(x.2 - y.2) by ring, abs_neg]
  have heq : c - x.2 = c - y.2 ↔ x.2 = y.2 := by omega
  rw [heq]

theorem axial_holdingKernel_invariant (c : ℤ) (x y : Vertex) :
    holdingKernel (axialReflection c x) (axialReflection c y) = holdingKernel x y := by
  have heq : axialReflection c x = axialReflection c y ↔ x = y :=
    (Function.Involutive.injective (axialReflection_involutive c)).eq_iff
  have ha := axial_adjacency_invariant c x y
  by_cases h : lattice.Adj x y
  · simp [holdingKernel, adjacencyKernel, heq, h, ha.mpr h]
  · have hn : ¬lattice.Adj (axialReflection c x) (axialReflection c y) := fun h' => h (ha.mp h')
    simp [holdingKernel, adjacencyKernel, heq, h, hn]

theorem diagonal_adjacency_invariant (x y : Vertex) :
    lattice.Adj x.swap y.swap ↔ lattice.Adj x y := by
  change (x.2 = y.2 ∧ |x.1 - y.1| = 1) ∨ (x.1 = y.1 ∧ |x.2 - y.2| = 1) ↔ _
  exact or_comm

theorem diagonal_adjacencyKernel_invariant (x y : Vertex) :
    adjacencyKernel x.swap y.swap = adjacencyKernel x y := by
  have ha := diagonal_adjacency_invariant x y
  by_cases h : lattice.Adj x y
  · simp [adjacencyKernel, h, ha.mpr h]
  · have hn : ¬lattice.Adj x.swap y.swap := fun h' => h (ha.mp h')
    simp [adjacencyKernel, h, hn]

end SpanningTreeIsoperimetry.Polarization




