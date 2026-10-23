module

public import SquareMaximality.Penalties
public import SquareMaximality.Logic

@[expose] public section

set_option autoImplicit false

/-!
# Checked assembly of the square-maximality argument

This file formalizes the final argument of `general.tex`: the missing-vertex count in the hull
is exactly the rectangular excess area, so the two estimates have equal and opposite penalty
terms.  The theorem is parameterized by `MaximalityInputs`/`EqualityInputs`; in particular, the
long analytic and planar-graph estimates are visible hypotheses rather than hidden axioms.
-/

namespace SquareMaximality

/-- The square-maximality conclusion follows from matching rectangular and hull penalties.

The constant `κ` is arbitrary: its actual evaluation as `4 * Catalan / π` is irrelevant to this
assembly because it cancels exactly. -/
theorem squareMaximality_of_inputs
    {κ : ℝ} (inputs : MaximalityInputs κ)
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2) :
    tau S ≤ tauRect n n := by
  classical
  by_cases hconn : (inducedGrid S).Connected
  · have hScard : 0 < S.card := by
      rw [hcard]
      exact pow_pos hn 2
    obtain ⟨a, b, r, s, hHull⟩ := exists_isRectHull_of_card_pos S hScard
    have hr : 0 < r := hHull.1
    have hs : 0 < s := hHull.2.1
    have harea : n ^ 2 ≤ r * s := by
      rw [← hcard]
      calc
        S.card ≤ (rectangle a b r s).card := Finset.card_le_card hHull.2.2.1
        _ = r * s := rectangle_card a b r s
    have hgap : (rectangle a b r s \ S).card = r * s - n ^ 2 :=
      rectangle_sdiff_card_of_card_sq hHull.2.2.1 hcard
    have hhull := inputs.hullPenalty.bound hconn hHull
    rw [hgap] at hhull
    have hrect := inputs.rectangularPenalty.bound hn hr hs harea
    have hlog : Real.log (tau S : ℝ) ≤ Real.log (tauRect n n : ℝ) :=
      le_of_matching_penalties hhull hrect
    exact nat_le_of_log_le ((tau_pos_iff_connected S).2 hconn)
      (tauRect_pos hn hn) hlog
  · have hnotpos : ¬0 < tau S := by
      intro hpos
      exact hconn ((tau_pos_iff_connected S).1 hpos)
    have htau : tau S = 0 := Nat.eq_zero_of_not_pos hnotpos
    simp [htau]

/-- Under the strict rectangular estimate, equality occurs exactly for translated `n × n`
lattice squares.  Translation invariance itself is proved in `Infrastructure.lean`. -/
theorem equality_iff_latticeSquare_of_inputs
    {κ : ℝ} (inputs : EqualityInputs κ)
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2) :
    tau S = tauRect n n ↔ IsLatticeSquare S n := by
  classical
  constructor
  · intro heq
    have hsquarePos : 0 < tauRect n n := tauRect_pos hn hn
    have hsetPos : 0 < tau S := by simpa [heq] using hsquarePos
    have hconn : (inducedGrid S).Connected := (tau_pos_iff_connected S).1 hsetPos
    have hScard : 0 < S.card := by
      rw [hcard]
      exact pow_pos hn 2
    obtain ⟨a, b, r, s, hHull⟩ := exists_isRectHull_of_card_pos S hScard
    have hrPos : 0 < r := hHull.1
    have hsPos : 0 < s := hHull.2.1
    have harea : n ^ 2 ≤ r * s := by
      rw [← hcard]
      calc
        S.card ≤ (rectangle a b r s).card := Finset.card_le_card hHull.2.2.1
        _ = r * s := rectangle_card a b r s
    by_cases hrs : (r, s) = (n, n)
    · have hr : r = n := congrArg Prod.fst hrs
      have hs : s = n := congrArg Prod.snd hrs
      exact hHull.isLatticeSquare_of_eq hr hs hcard
    · have hgap : (rectangle a b r s \ S).card = r * s - n ^ 2 :=
        rectangle_sdiff_card_of_card_sq hHull.2.2.1 hcard
      have hhull := inputs.hullPenalty.bound hconn hHull
      rw [hgap] at hhull
      have hrect := inputs.strictRectangularPenalty.bound hn hrPos hsPos harea hrs
      have hlog : Real.log (tau S : ℝ) < Real.log (tauRect n n : ℝ) :=
        lt_of_matching_penalties hhull hrect
      exact (nat_ne_of_log_lt hsetPos hsquarePos hlog heq).elim
  · rintro ⟨a, b, rfl⟩
    exact tau_rectangle_eq_tauRect a b n n

/-- The manuscript's non-strict theorem, conditional on its named inputs. -/
theorem paper_squareMaximality_of_penalties
    (inputs : MaximalityInputs squareLatticeEntropy)
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2) :
    tau S ≤ tauRect n n :=
  squareMaximality_of_inputs inputs hn S hcard

/-- The manuscript's equality characterization, conditional on its named inputs. -/
theorem paper_equality_iff_latticeSquare_of_penalties
    (inputs : EqualityInputs squareLatticeEntropy)
    {n : ℕ} (hn : 0 < n) (S : Finset Point) (hcard : S.card = n ^ 2) :
    tau S = tauRect n n ↔ IsLatticeSquare S n :=
  equality_iff_latticeSquare_of_inputs inputs hn S hcard

end SquareMaximality
