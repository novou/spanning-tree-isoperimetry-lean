import SquareMaximality.Normalization
import SquareMaximality.Constants

set_option autoImplicit false

/-!
# Interfaces for the two substantive estimates in `general.tex`

The manuscript's proof has a short logical assembly step and two long inputs:

* the rectangular area penalty; and
* the normalized rectangular-hull penalty.

This file states those inputs as predicates.  They are parameters to the
modular theorem in `Main.lean`, not global axioms.  The final public theorem
later constructs both predicates explicitly.
-/

namespace SquareMaximality

/-- The rectangular area penalty in the ordered-side form stated in the manuscript. -/
def RectangularAreaPenalty (κ : ℝ) : Prop :=
  ∀ ⦃n r s : ℕ⦄,
    0 < n → 0 < r → 0 < s → r ≤ s → n ^ 2 ≤ r * s →
      Real.log (tauRect r s : ℝ) - Real.log (tauRect n n : ℝ)
        ≤ κ * ((r * s - n ^ 2 : ℕ) : ℝ)

/-- The strict part of the rectangular estimate: equality is possible only at the original
`n × n` square. -/
def StrictRectangularAreaPenalty (κ : ℝ) : Prop :=
  ∀ ⦃n r s : ℕ⦄,
    0 < n → 0 < r → 0 < s → r ≤ s → n ^ 2 ≤ r * s →
      (r, s) ≠ (n, n) →
        Real.log (tauRect r s : ℝ) - Real.log (tauRect n n : ℝ)
          < κ * ((r * s - n ^ 2 : ℕ) : ℝ)

/-- The ordered-side rectangular estimate implies the same bound for side lengths in either
order, by interchanging the two lattice coordinates when necessary. -/
theorem RectangularAreaPenalty.bound
    {κ : ℝ} (h : RectangularAreaPenalty κ)
    ⦃n r s : ℕ⦄ (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (harea : n ^ 2 ≤ r * s) :
    Real.log (tauRect r s : ℝ) - Real.log (tauRect n n : ℝ)
      ≤ κ * ((r * s - n ^ 2 : ℕ) : ℝ) := by
  rcases le_total r s with hrs | hsr
  · exact h hn hr hs hrs harea
  · have hswapped := h hn hs hr hsr (by simpa [Nat.mul_comm] using harea)
    simpa [tauRect_comm, Nat.mul_comm] using hswapped

/-- The ordered-side strict estimate likewise applies in either orientation.  Swapping the
sides preserves the condition that the rectangle is not the original square. -/
theorem StrictRectangularAreaPenalty.bound
    {κ : ℝ} (h : StrictRectangularAreaPenalty κ)
    ⦃n r s : ℕ⦄ (hn : 0 < n) (hr : 0 < r) (hs : 0 < s)
    (harea : n ^ 2 ≤ r * s) (hne : (r, s) ≠ (n, n)) :
    Real.log (tauRect r s : ℝ) - Real.log (tauRect n n : ℝ)
      < κ * ((r * s - n ^ 2 : ℕ) : ℝ) := by
  rcases le_total r s with hrs | hsr
  · exact h hn hr hs hrs harea hne
  · have hneSwapped : (s, r) ≠ (n, n) := by
      intro heq
      apply hne
      exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
    have hswapped := h hn hs hr hsr (by simpa [Nat.mul_comm] using harea) hneSwapped
    simpa [tauRect_comm, Nat.mul_comm] using hswapped

/-- The normalized rectangular-hull inequality, stated after translating the
minimal hull to the standard rectangle based at the origin. -/
def NormalizedHullPenalty (κ : ℝ) : Prop :=
  ∀ ⦃S : Finset Point⦄ ⦃r s : ℕ⦄,
    (inducedGrid S).Connected → IsRectHull S 0 0 r s →
      Real.log (tau S : ℝ) - Real.log (tauRect r s : ℝ)
        ≤ -κ * ((rectangle 0 0 r s \ S).card : ℝ)

/-- The origin-normalized hull estimate applies at an arbitrary base point
by translating the entire finite set to the origin. -/
theorem NormalizedHullPenalty.bound
    {κ : ℝ} (h : NormalizedHullPenalty κ)
    ⦃S : Finset Point⦄ ⦃a b : ℤ⦄ ⦃r s : ℕ⦄
    (hconn : (inducedGrid S).Connected) (hHull : IsRectHull S a b r s) :
    Real.log (tau S : ℝ) - Real.log (tauRect r s : ℝ)
      ≤ -κ * ((rectangle a b r s \ S).card : ℝ) := by
  have hconn0 := hHull.connected_iff_translate_to_origin.mp hconn
  have h0 := h hconn0 hHull.translate_to_origin
  rw [hHull.tau_translate_to_origin,
    hHull.vacancy_card_translate_to_origin] at h0
  exact h0

/-- The two deep inputs needed for the non-strict square-maximality conclusion. -/
structure MaximalityInputs (κ : ℝ) : Prop where
  rectangularPenalty : RectangularAreaPenalty κ
  hullPenalty : NormalizedHullPenalty κ

/-- The additional strict rectangular estimate used to characterize equality. -/
structure EqualityInputs (κ : ℝ) : Prop extends MaximalityInputs κ where
  strictRectangularPenalty : StrictRectangularAreaPenalty κ

end SquareMaximality
