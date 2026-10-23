module

public import SquareMaximality.Boundary.Faces
public import SquareMaximality.Boundary.KingRuns
public import SquareMaximality.ClosedWalk.All

@[expose] public section

/-!
# Finite closed-walk charging

This module formalizes the finite placement estimate preceding the determinant
series in `general.tex`.  A word is normalized by translating the minima of
its partial sums to the origin.  Each placement meeting a marked face injects
into a primal vacancy window one unit wider in each coordinate.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Boundary

open Windows
open ClosedWalk

def walkMinX {n : ℕ} (ω : Word n) : ℤ :=
  (visitedX ω).min' (visitedX_nonempty ω)

def walkMaxX {n : ℕ} (ω : Word n) : ℤ :=
  (visitedX ω).max' (visitedX_nonempty ω)

def walkMinY {n : ℕ} (ω : Word n) : ℤ :=
  (visitedY ω).min' (visitedY_nonempty ω)

def walkMaxY {n : ℕ} (ω : Word n) : ℤ :=
  (visitedY ω).max' (visitedY_nonempty ω)

theorem walkMinX_le_walkMaxX {n : ℕ} (ω : Word n) : walkMinX ω ≤ walkMaxX ω :=
  Finset.min'_le_max' _ _

theorem walkMinY_le_walkMaxY {n : ℕ} (ω : Word n) : walkMinY ω ≤ walkMaxY ω :=
  Finset.min'_le_max' _ _

/-- Translate one visited point by the coordinatewise minima and convert the
now nonnegative coordinates to naturals. -/
def normalizedWalkPoint {n : ℕ} (ω : Word n) (p : Point) : LatticePoint :=
  ((p.1 - walkMinX ω).toNat, (p.2 - walkMinY ω).toNat)

/-- Partial-sum set translated into its minimal natural-coordinate box. -/
def normalizedPartialSums {n : ℕ} (ω : Word n) : Finset LatticePoint :=
  (partialSums ω).image (normalizedWalkPoint ω)

theorem normalizedWalkPoint_fst_le_spanX
    {n : ℕ} (ω : Word n) {p : Point} (hp : p ∈ partialSums ω) :
    (normalizedWalkPoint ω p).1 ≤ spanX ω := by
  have hpX : p.1 ∈ visitedX ω := Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hmin : walkMinX ω ≤ p.1 := Finset.min'_le _ _ hpX
  have hmax : p.1 ≤ walkMaxX ω := Finset.le_max' _ _ hpX
  change (p.1 - walkMinX ω).toNat ≤
    (walkMaxX ω - walkMinX ω).toNat
  exact Int.toNat_le_toNat (sub_le_sub_right hmax (walkMinX ω))

theorem normalizedWalkPoint_snd_le_spanY
    {n : ℕ} (ω : Word n) {p : Point} (hp : p ∈ partialSums ω) :
    (normalizedWalkPoint ω p).2 ≤ spanY ω := by
  have hpY : p.2 ∈ visitedY ω := Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hmin : walkMinY ω ≤ p.2 := Finset.min'_le _ _ hpY
  have hmax : p.2 ≤ walkMaxY ω := Finset.le_max' _ _ hpY
  change (p.2 - walkMinY ω).toNat ≤
    (walkMaxY ω - walkMinY ω).toNat
  exact Int.toNat_le_toNat (sub_le_sub_right hmax (walkMinY ω))

theorem normalizedPartialSums_subset_box {n : ℕ} (ω : Word n) :
    normalizedPartialSums ω ⊆ rectangleWindow 0 0 (spanX ω) (spanY ω) := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
  exact mem_rectangleWindow.mpr ⟨Nat.zero_le _,
    by simpa using normalizedWalkPoint_fst_le_spanX ω hp,
    Nat.zero_le _, by simpa using normalizedWalkPoint_snd_le_spanY ω hp⟩

/-- Normalized partial sums placed with lower-left corner `(x,y)`. -/
def placedPartialSums {n : ℕ} (ω : Word n) (x y : ℕ) : Finset LatticePoint :=
  (normalizedPartialSums ω).image fun z => (x + z.1, y + z.2)

theorem placedPartialSums_subset_box
    {n : ℕ} (ω : Word n) (x y : ℕ) :
    placedPartialSums ω x y ⊆ rectangleWindow x y (spanX ω) (spanY ω) := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
  have hbox := mem_rectangleWindow.mp (normalizedPartialSums_subset_box ω hw)
  exact mem_rectangleWindow.mpr ⟨by omega, by omega, by omega, by omega⟩

/-- Lower-left starts of normalized word placements which meet a marked face.
The outer valid-start bounds are those of the corresponding primal window. -/
def walkMeetingStarts {n : ℕ} (R S : ℕ) (V : Finset LatticePoint)
    (ω : Word n) : Finset (Σ _x : ℕ, ℕ) :=
  ((validWindowStarts R (spanX ω + 1)).sigma fun _ =>
      validWindowStarts S (spanY ω + 1)).filter fun z =>
    (placedPartialSums ω z.1 z.2 ∩ markedFaces R S V).Nonempty

@[simp] theorem mem_walkMeetingStarts
    {n R S : ℕ} {V : Finset LatticePoint} {ω : Word n}
    {z : Σ _x : ℕ, ℕ} :
    z ∈ walkMeetingStarts R S V ω ↔
      z.1 + (spanX ω + 1) ≤ R ∧
      z.2 + (spanY ω + 1) ≤ S ∧
      (placedPartialSums ω z.1 z.2 ∩ markedFaces R S V).Nonempty := by
  simp [walkMeetingStarts, and_assoc]

/-- A placed walk meeting a marked face determines a primal vacancy window. -/
theorem walkMeetingStarts_subset_rectangleWindows
    {n : ℕ} (R S : ℕ) (V : Finset LatticePoint) (ω : Word n) :
    walkMeetingStarts R S V ω ⊆
      meetingRectangleWindowStarts R S (spanX ω + 1) (spanY ω + 1) V := by
  intro z hz
  rcases mem_walkMeetingStarts.mp hz with ⟨hx, hy, q, hq⟩
  have hqParts := Finset.mem_inter.mp hq
  have hqBox := placedPartialSums_subset_box ω z.1 z.2 hqParts.1
  have hqBounds := mem_rectangleWindow.mp hqBox
  rcases mem_markedFaces.mp hqParts.2 with
    ⟨_, _, v, hvV, hqx, hxq, hqy, hyq⟩
  apply mem_meetingRectangleWindowStarts.mpr
  refine ⟨hx, hy, v, hvV, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Equation `walk-charging`, in the normalized-placement formulation. -/
theorem walk_charging
    {n : ℕ} (R S : ℕ) (V : Finset LatticePoint) (ω : Word n)
    (hV : V ⊆ grid R S)
    (hinj : SlidingWindowInjection R S (spanX ω + 1) V) :
    (walkMeetingStarts R S V ω).card ≤
      V.card + (spanX ω + 1) * horizontalInternalRunCount R S V +
        (spanY ω + 1) * verticalInternalRunCount R S V := by
  by_cases hx : spanX ω + 1 ≤ R
  · by_cases hy : spanY ω + 1 ≤ S
    · exact (Finset.card_le_card
        (walkMeetingStarts_subset_rectangleWindows R S V ω)).trans
          (anisotropic_window_inequality R S (spanX ω + 1) (spanY ω + 1)
            V hV hx hy hinj)
    · have hempty : walkMeetingStarts R S V ω = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨z, hz⟩
        have hz' := mem_walkMeetingStarts.mp hz
        exact hy (by omega)
      rw [hempty]
      simp
  · have hempty : walkMeetingStarts R S V ω = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨z, hz⟩
      have hz' := mem_walkMeetingStarts.mp hz
      exact hx (by omega)
    rw [hempty]
    simp

/-- The walk charging bound is unconditional for the canonical encoded
boundary-vacancy set, because its sliding injection has been constructed. -/
theorem walk_charging_encodedBoundaryVacancies
    {n : ℕ} (R S : ℕ) (A : Finset Point) (ω : Word n) :
    (walkMeetingStarts R S
      (boundaryVacancies R S (encodedVacancies R S A)) ω).card ≤
      (boundaryVacancies R S (encodedVacancies R S A)).card +
        (spanX ω + 1) * horizontalInternalRunCount R S
          (boundaryVacancies R S (encodedVacancies R S A)) +
        (spanY ω + 1) * verticalInternalRunCount R S
          (boundaryVacancies R S (encodedVacancies R S A)) := by
  apply walk_charging
  · exact (boundaryVacancies_subset R S _).trans
      (encodedVacancies_subset_grid R S A)
  · exact slidingWindowInjection_encodedBoundaryVacancies
      R S (spanX ω + 1) A

end Boundary
end SquareMaximality
