module

public import SquareMaximality.ClosedWalk.PlaneMarked

@[expose] public section

set_option backward.privateInPublic true

/-!
# Coordinate symmetry of closed square-lattice words

Swapping the two coordinates is an involution on step words.  This supplies
the vertical counterpart of the horizontal span identities without repeating
the reflection argument.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace ClosedWalk

/-- Interchange the horizontal and vertical directions. -/
def swapStep : Step → Step
  | .east => .north
  | .west => .south
  | .north => .east
  | .south => .west

@[simp] theorem swapStep_swapStep (d : Step) : swapStep (swapStep d) = d := by
  cases d <;> rfl

@[simp] theorem swapStep_vector (d : Step) :
    (swapStep d).vector = (d.vector.2, d.vector.1) := by
  cases d <;> rfl

/-- Swap every step in a word. -/
def swapWord {n : ℕ} (ω : Word n) : Word n :=
  fun i => swapStep (ω i)

@[simp] theorem swapWord_swapWord {n : ℕ} (ω : Word n) :
    swapWord (swapWord ω) = ω := by
  funext i
  simp [swapWord]

private def swapPoint (p : ℤ × ℤ) : ℤ × ℤ := (p.2, p.1)

private theorem stepAt_swapWord {n : ℕ} (ω : Word n) (j : ℕ) :
    stepAt (swapWord ω) j = swapPoint (stepAt ω j) := by
  by_cases hj : j < n
  · simp [stepAt, swapWord, swapPoint, hj]
  · simp [stepAt, swapPoint, hj]

theorem position_swapWord {n : ℕ} (ω : Word n) (t : ℕ) :
    position (swapWord ω) t = swapPoint (position ω t) := by
  apply Prod.ext
  · simp only [position, swapPoint, Prod.fst_sum, Prod.snd_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg Prod.fst (stepAt_swapWord ω j)
  · simp only [position, swapPoint, Prod.fst_sum, Prod.snd_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg Prod.snd (stepAt_swapWord ω j)

theorem total_swapWord {n : ℕ} (ω : Word n) :
    total (swapWord ω) = swapPoint (total ω) := by
  rw [← position_length, ← position_length, position_swapWord]

theorem isClosed_swapWord_iff {n : ℕ} (ω : Word n) :
    IsClosed (swapWord ω) ↔ IsClosed ω := by
  rw [IsClosed, IsClosed, total_swapWord]
  constructor
  · intro h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  · intro h
    rw [h]
    rfl

theorem partialSums_swapWord {n : ℕ} (ω : Word n) :
    partialSums (swapWord ω) = (partialSums ω).image swapPoint := by
  classical
  ext p
  simp only [partialSums, Finset.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨position ω t, ⟨t, ht, rfl⟩, (position_swapWord ω t).symm⟩
  · rintro ⟨q, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, position_swapWord ω t⟩

theorem visitedX_swapWord {n : ℕ} (ω : Word n) :
    visitedX (swapWord ω) = visitedY ω := by
  classical
  ext z
  simp [visitedX, visitedY, partialSums_swapWord, swapPoint]

theorem visitedY_swapWord {n : ℕ} (ω : Word n) :
    visitedY (swapWord ω) = visitedX ω := by
  rw [← visitedX_swapWord (swapWord ω), swapWord_swapWord]

@[simp] theorem spanX_swapWord {n : ℕ} (ω : Word n) :
    spanX (swapWord ω) = spanY ω := by
  simp only [spanX, spanY, visitedX_swapWord]

@[simp] theorem spanY_swapWord {n : ℕ} (ω : Word n) :
    spanY (swapWord ω) = spanX ω := by
  simp only [spanX, spanY, visitedY_swapWord]

/-- Coordinate swap as an equivalence of closed words represented by
membership in `closedWords`. -/
def swapClosedWordEquiv (n : ℕ) :
    {ω : Word n // ω ∈ closedWords n} ≃
      {ω : Word n // ω ∈ closedWords n} where
  toFun ω := ⟨swapWord ω.1, by
    rw [mem_closedWords, isClosed_swapWord_iff]
    exact mem_closedWords.mp ω.2⟩
  invFun ω := ⟨swapWord ω.1, by
    rw [mem_closedWords, isClosed_swapWord_iff]
    exact mem_closedWords.mp ω.2⟩
  left_inv ω := Subtype.ext (swapWord_swapWord ω.1)
  right_inv ω := Subtype.ext (swapWord_swapWord ω.1)

/-- Horizontal and vertical span masses agree at every length. -/
theorem closedWords_spanY_add_one_sum_eq_spanX (n : ℕ) :
    (∑ ω ∈ closedWords n, (spanY ω + 1)) =
      ∑ ω ∈ closedWords n, (spanX ω + 1) := by
  calc
    (∑ ω ∈ closedWords n, (spanY ω + 1)) =
        ∑ ω : {ω : Word n // ω ∈ closedWords n}, (spanY ω.1 + 1) :=
      (Finset.sum_coe_sort _ _).symm
    _ = ∑ ω : {ω : Word n // ω ∈ closedWords n}, (spanX ω.1 + 1) := by
      apply Fintype.sum_equiv (swapClosedWordEquiv n)
      intro ω
      change spanY ω.1 + 1 = spanX (swapWord ω.1) + 1
      rw [spanX_swapWord]
    _ = ∑ ω ∈ closedWords n, (spanX ω + 1) :=
      Finset.sum_coe_sort (closedWords n) (fun ω => spanX ω + 1)

theorem closedWords_spanY_add_one_sum_even (a : ℕ) :
    ∑ ω ∈ closedWords (2 * a), (spanY ω + 1) =
      Nat.choose (2 * (2 * a)) (2 * a) := by
  rw [closedWords_spanY_add_one_sum_eq_spanX,
    closedWords_spanX_add_one_sum_even]

theorem closedWords_spanY_add_one_sum_odd (a : ℕ) :
    ∑ ω ∈ closedWords (2 * a + 1), (spanY ω + 1) = 0 := by
  rw [closedWords_spanY_add_one_sum_eq_spanX,
    closedWords_spanX_add_one_sum_odd]

end ClosedWalk
end SquareMaximality
