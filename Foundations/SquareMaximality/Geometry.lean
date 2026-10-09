import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card

set_option autoImplicit false

namespace SquareMaximality

/-- A vertex of the integer square lattice. -/
abbrev Point := ℤ × ℤ

/-- The half-open integer rectangle
`[a, a + r) × [b, b + s)`.

The natural numbers `r` and `s` are its numbers of lattice columns and
rows, respectively. -/
noncomputable def rectangle (a b : ℤ) (r s : ℕ) : Finset Point :=
  (Finset.Ico a (a + r)).product (Finset.Ico b (b + s))

@[simp]
theorem rectangle_card (a b : ℤ) (r s : ℕ) :
    (rectangle a b r s).card = r * s := by
  simp [rectangle]

/-- The number of points missing from a rectangle is its area minus the
number of points in the contained set. -/
theorem rectangle_sdiff_card_of_subset
    {S : Finset Point} {a b : ℤ} {r s : ℕ}
    (hS : S ⊆ rectangle a b r s) :
    (rectangle a b r s \ S).card = r * s - S.card := by
  rw [Finset.card_sdiff_of_subset hS, rectangle_card]

/-- Missing-point count when the contained set has square cardinality. -/
theorem rectangle_sdiff_card_of_card_sq
    {S : Finset Point} {a b : ℤ} {r s n : ℕ}
    (hS : S ⊆ rectangle a b r s)
    (hcard : S.card = n ^ 2) :
    (rectangle a b r s \ S).card = r * s - n ^ 2 := by
  rw [rectangle_sdiff_card_of_subset hS, hcard]

/-- `IsRectHull S a b r s` says that the positive-size rectangle based at
`(a,b)` contains `S` and that `S` meets every one of its four sides.

The side witnesses make the rectangle the minimal axis-parallel lattice
rectangle containing `S`. -/
def IsRectHull (S : Finset Point) (a b : ℤ) (r s : ℕ) : Prop :=
  0 < r ∧
  0 < s ∧
  S ⊆ rectangle a b r s ∧
  (∃ p ∈ S, p.1 = a) ∧
  (∃ p ∈ S, p.1 = a + r - 1) ∧
  (∃ p ∈ S, p.2 = b) ∧
  (∃ p ∈ S, p.2 = b + s - 1)

/-- A finite set of lattice points is an `n × n` lattice square when it
is a translate of the standard half-open `n × n` rectangle. -/
def IsLatticeSquare (S : Finset Point) (n : ℕ) : Prop :=
  ∃ a b : ℤ, S = rectangle a b n n

/-- A set filling as many points as its rectangular hull has must equal the
hull.  In the square case this identifies it as a lattice square. -/
theorem IsRectHull.isLatticeSquare_of_card
    {S : Finset Point} {a b : ℤ} {n : ℕ}
    (hHull : IsRectHull S a b n n)
    (hcard : S.card = n ^ 2) :
    IsLatticeSquare S n := by
  refine ⟨a, b, ?_⟩
  apply Finset.eq_of_subset_of_card_le hHull.2.2.1
  rw [rectangle_card, hcard, pow_two]

/-- Version of `IsRectHull.isLatticeSquare_of_card` with separately named
hull dimensions. -/
theorem IsRectHull.isLatticeSquare_of_eq
    {S : Finset Point} {a b : ℤ} {r s n : ℕ}
    (hHull : IsRectHull S a b r s)
    (hr : r = n) (hs : s = n)
    (hcard : S.card = n ^ 2) :
    IsLatticeSquare S n := by
  subst r
  subst s
  exact hHull.isLatticeSquare_of_card hcard

end SquareMaximality
