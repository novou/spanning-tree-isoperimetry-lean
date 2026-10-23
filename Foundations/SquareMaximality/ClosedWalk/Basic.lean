module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Int.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Finite square-lattice step words

This file gives the finite objects used in the closed-walk charging argument of
`general.tex`: the four-step alphabet, words, partial sums, coordinate spans,
and the finite set of closed words.  It also records a two-sign encoding of a
step.  Under this encoding a word is closed exactly when each sign word is
balanced; that observation is the finite combinatorial core of the formula
`w_(2a) = choose (2a) a ^ 2`.
-/

namespace SquareMaximality
namespace ClosedWalk

/-- The four nearest-neighbour steps of the square lattice. -/
inductive Step
  | east
  | west
  | north
  | south
  deriving DecidableEq, Repr

instance : Fintype Step where
  elems := {.east, .west, .north, .south}
  complete x := by cases x <;> simp

/-- The displacement vector of a square-lattice step. -/
def Step.vector : Step → ℤ × ℤ
  | .east => (1, 0)
  | .west => (-1, 0)
  | .north => (0, 1)
  | .south => (0, -1)

@[simp] theorem Step.vector_east : Step.east.vector = (1, 0) := rfl
@[simp] theorem Step.vector_west : Step.west.vector = (-1, 0) := rfl
@[simp] theorem Step.vector_north : Step.north.vector = (0, 1) := rfl
@[simp] theorem Step.vector_south : Step.south.vector = (0, -1) := rfl

/-- A step word of length `n`. -/
abbrev Word (n : ℕ) := Fin n → Step

/-- Total displacement of a word. -/
def total {n : ℕ} (ω : Word n) : ℤ × ℤ :=
  ∑ i, (ω i).vector

/-- A word is closed when its total displacement is zero. -/
def IsClosed {n : ℕ} (ω : Word n) : Prop := total ω = (0, 0)

instance {n : ℕ} (ω : Word n) : Decidable (IsClosed ω) :=
  inferInstanceAs (Decidable (total ω = (0, 0)))

/-- A step at a natural index, extended by zero beyond the word length. -/
def stepAt {n : ℕ} (ω : Word n) (j : ℕ) : ℤ × ℤ :=
  if h : j < n then (ω ⟨j, h⟩).vector else (0, 0)

/-- Partial displacement after the positions whose indices are less than `t`. -/
def position {n : ℕ} (ω : Word n) (t : ℕ) : ℤ × ℤ :=
  ∑ j ∈ Finset.range t, stepAt ω j

/-- The finite partial-sum set `{0,d₁,d₁+d₂,…,d₁+⋯+dₙ}`. -/
def partialSums {n : ℕ} (ω : Word n) : Finset (ℤ × ℤ) :=
  (Finset.range (n + 1)).image (position ω)

@[simp] theorem position_zero {n : ℕ} (ω : Word n) : position ω 0 = (0, 0) := by
  apply Prod.ext <;> simp [position]

@[simp] theorem position_length {n : ℕ} (ω : Word n) : position ω n = total ω := by
  rw [position, total]
  calc
    (∑ j ∈ Finset.range n, stepAt ω j) =
        ∑ i : Fin n, if h : i.1 < n then (ω ⟨i.1, h⟩).vector else (0, 0) :=
      (Fin.sum_univ_eq_sum_range
        (fun j => if h : j < n then (ω ⟨j, h⟩).vector else (0, 0)) n).symm
    _ = ∑ i, (ω i).vector := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [i.2, dite_true]

theorem partialSums_nonempty {n : ℕ} (ω : Word n) : (partialSums ω).Nonempty := by
  refine ⟨position ω 0, Finset.mem_image.mpr ⟨0, ?_, rfl⟩⟩
  simp

@[simp] theorem zero_mem_partialSums {n : ℕ} (ω : Word n) :
    (0, 0) ∈ partialSums ω := by
  rw [← position_zero ω]
  exact Finset.mem_image.mpr ⟨0, by simp, rfl⟩

/-- All horizontal coordinates visited by a word. -/
def visitedX {n : ℕ} (ω : Word n) : Finset ℤ :=
  (partialSums ω).image Prod.fst

/-- All vertical coordinates visited by a word. -/
def visitedY {n : ℕ} (ω : Word n) : Finset ℤ :=
  (partialSums ω).image Prod.snd

theorem visitedX_nonempty {n : ℕ} (ω : Word n) : (visitedX ω).Nonempty :=
  (partialSums_nonempty ω).image _

theorem visitedY_nonempty {n : ℕ} (ω : Word n) : (visitedY ω).Nonempty :=
  (partialSums_nonempty ω).image _

@[simp] theorem zero_mem_visitedX {n : ℕ} (ω : Word n) : 0 ∈ visitedX ω := by
  exact Finset.mem_image.mpr ⟨(0, 0), zero_mem_partialSums ω, rfl⟩

@[simp] theorem zero_mem_visitedY {n : ℕ} (ω : Word n) : 0 ∈ visitedY ω := by
  exact Finset.mem_image.mpr ⟨(0, 0), zero_mem_partialSums ω, rfl⟩

/-- Horizontal span, as a nonnegative integer. -/
def spanX {n : ℕ} (ω : Word n) : ℕ :=
  Int.toNat ((visitedX ω).max' (visitedX_nonempty ω) -
    (visitedX ω).min' (visitedX_nonempty ω))

/-- Vertical span, as a nonnegative integer. -/
def spanY {n : ℕ} (ω : Word n) : ℕ :=
  Int.toNat ((visitedY ω).max' (visitedY_nonempty ω) -
    (visitedY ω).min' (visitedY_nonempty ω))

/-- The finite set of closed words of a fixed length. -/
def closedWords (n : ℕ) : Finset (Word n) :=
  Finset.univ.filter IsClosed

/-- The number `w_n` of closed words of length `n`. -/
def closedWordCount (n : ℕ) : ℕ := (closedWords n).card

@[simp] theorem mem_closedWords {n : ℕ} {ω : Word n} :
    ω ∈ closedWords n ↔ IsClosed ω := by
  simp [closedWords]

/-- Encoding of a step by two signs.  It is a rotated coordinate system. -/
def stepSignEquiv : Step ≃ Bool × Bool where
  toFun
    | .east => (true, true)
    | .west => (false, false)
    | .north => (true, false)
    | .south => (false, true)
  invFun
    | (true, true) => .east
    | (false, false) => .west
    | (true, false) => .north
    | (false, true) => .south
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with ⟨a, b⟩; cases a <;> cases b <;> rfl

/-- Positions carrying a positive first transformed sign. -/
def firstSignSet {n : ℕ} (ω : Word n) : Finset (Fin n) :=
  Finset.univ.filter fun i => (stepSignEquiv (ω i)).1

/-- Positions carrying a positive second transformed sign. -/
def secondSignSet {n : ℕ} (ω : Word n) : Finset (Fin n) :=
  Finset.univ.filter fun i => (stepSignEquiv (ω i)).2

@[simp] theorem mem_firstSignSet {n : ℕ} {ω : Word n} {i : Fin n} :
    i ∈ firstSignSet ω ↔ (stepSignEquiv (ω i)).1 := by
  simp [firstSignSet]

@[simp] theorem mem_secondSignSet {n : ℕ} {ω : Word n} {i : Fin n} :
    i ∈ secondSignSet ω ↔ (stepSignEquiv (ω i)).2 := by
  simp [secondSignSet]

/-- Recover a word from the sets of positive positions of its two signs. -/
def wordOfSignSets {n : ℕ} (s : Finset (Fin n) × Finset (Fin n)) : Word n :=
  fun i => stepSignEquiv.symm (i ∈ s.1, i ∈ s.2)

/-- Step words are equivalent to pairs of subsets of their positions. -/
def wordEquivSignSets (n : ℕ) : Word n ≃ Finset (Fin n) × Finset (Fin n) where
  toFun ω := (firstSignSet ω, secondSignSet ω)
  invFun := wordOfSignSets
  left_inv ω := by
    funext i
    apply stepSignEquiv.injective
    simp [wordOfSignSets]
  right_inv s := by
    ext i <;> simp [wordOfSignSets]

@[simp] theorem wordEquivSignSets_apply (n : ℕ) (ω : Word n) :
    wordEquivSignSets n ω = (firstSignSet ω, secondSignSet ω) := rfl

end ClosedWalk
end SquareMaximality
