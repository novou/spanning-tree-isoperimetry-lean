module

public import SquareMaximality.Normalization
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Degenerate rectangular hulls

The normalized-hull proof in `general.tex` first removes the cases in
which one side of the hull has length one.  This file formalizes the
discrete intermediate-value fact for lattice walks that underlies that
branch.
-/

namespace SquareMaximality

open SimpleGraph

/-- A lattice walk whose endpoints lie on opposite sides of a horizontal
level visits that level. -/
theorem walk_exists_second_eq_of_le
    {S : Finset Point} {u v : {p : Point // p ∈ S}}
    (w : (inducedGrid S).Walk u v) (y : ℤ)
    (hu : u.1.2 ≤ y) (hv : y ≤ v.1.2) :
    ∃ z ∈ w.support, z.1.2 = y := by
  induction w generalizing y with
  | @nil u =>
      exact ⟨u, by simp, le_antisymm hu hv⟩
  | @cons u v z huv w ih =>
      by_cases huy : u.1.2 = y
      · exact ⟨u, by simp, huy⟩
      have huy_lt : u.1.2 < y := lt_of_le_of_ne hu huy
      have hstep :
          (((u.1.1 + 1 = v.1.1) ∨ (v.1.1 + 1 = u.1.1)) ∧ u.1.2 = v.1.2) ∨
          (((u.1.2 + 1 = v.1.2) ∨ (v.1.2 + 1 = u.1.2)) ∧ u.1.1 = v.1.1) :=
        (manhattanDist_eq_one_iff u.1 v.1).mp huv
      by_cases hvy : v.1.2 = y
      · exact ⟨v, by simp, hvy⟩
      have hv_le : v.1.2 ≤ y := by
        rcases hstep with hstep | hstep <;> rcases hstep with ⟨hstep, hother⟩
        · omega
        · rcases hstep with hstep | hstep <;> omega
      obtain ⟨q, hq, hqy⟩ := ih y hv_le hv
      exact ⟨q, by simp [hq], hqy⟩

/-- The coordinate-swapped discrete intermediate-value theorem. -/
theorem walk_exists_first_eq_of_le
    {S : Finset Point} {u v : {p : Point // p ∈ S}}
    (w : (inducedGrid S).Walk u v) (x : ℤ)
    (hu : u.1.1 ≤ x) (hv : x ≤ v.1.1) :
    ∃ z ∈ w.support, z.1.1 = x := by
  induction w generalizing x with
  | @nil u =>
      exact ⟨u, by simp, le_antisymm hu hv⟩
  | @cons u v z huv w ih =>
      by_cases hux : u.1.1 = x
      · exact ⟨u, by simp, hux⟩
      have hux_lt : u.1.1 < x := lt_of_le_of_ne hu hux
      have hstep :
          (((u.1.1 + 1 = v.1.1) ∨ (v.1.1 + 1 = u.1.1)) ∧ u.1.2 = v.1.2) ∨
          (((u.1.2 + 1 = v.1.2) ∨ (v.1.2 + 1 = u.1.2)) ∧ u.1.1 = v.1.1) :=
        (manhattanDist_eq_one_iff u.1 v.1).mp huv
      by_cases hvx : v.1.1 = x
      · exact ⟨v, by simp, hvx⟩
      have hv_le : v.1.1 ≤ x := by
        rcases hstep with hstep | hstep <;> rcases hstep with ⟨hstep, hother⟩
        · rcases hstep with hstep | hstep <;> omega
        · omega
      obtain ⟨q, hq, hqx⟩ := ih x hv_le hv
      exact ⟨q, by simp [hq], hqx⟩

/-- Every column of a connected set occurs between the two extreme columns of
its minimal rectangular hull. -/
theorem IsRectHull.exists_point_with_first_eq
    {S : Finset Point} {r s : ℕ}
    (hHull : IsRectHull S 0 0 r s)
    (hconn : (inducedGrid S).Connected)
    {x : ℤ} (hx0 : 0 ≤ x) (hxr : x < r) :
    ∃ p ∈ S, p.1 = x := by
  obtain ⟨left, hleftS, hleftX⟩ := hHull.2.2.2.1
  obtain ⟨right, hrightS, hrightX⟩ := hHull.2.2.2.2.1
  let u : {q : Point // q ∈ S} := ⟨left, hleftS⟩
  let v : {q : Point // q ∈ S} := ⟨right, hrightS⟩
  obtain ⟨w⟩ := hconn u v
  have hu : u.1.1 ≤ x := by simpa [u, hleftX] using hx0
  have hv : x ≤ v.1.1 := by
    simp only [v, hrightX]
    omega
  obtain ⟨p, _hpSupport, hpX⟩ := walk_exists_first_eq_of_le w x hu hv
  exact ⟨p.1, p.2, hpX⟩

/-- Every row of a connected set occurs between the two extreme rows of its
minimal rectangular hull. -/
theorem IsRectHull.exists_point_with_second_eq
    {S : Finset Point} {r s : ℕ}
    (hHull : IsRectHull S 0 0 r s)
    (hconn : (inducedGrid S).Connected)
    {y : ℤ} (hy0 : 0 ≤ y) (hys : y < s) :
    ∃ p ∈ S, p.2 = y := by
  obtain ⟨bottom, hbottomS, hbottomY⟩ := hHull.2.2.2.2.2.1
  obtain ⟨top, htopS, htopY⟩ := hHull.2.2.2.2.2.2
  let u : {q : Point // q ∈ S} := ⟨bottom, hbottomS⟩
  let v : {q : Point // q ∈ S} := ⟨top, htopS⟩
  obtain ⟨w⟩ := hconn u v
  have hu : u.1.2 ≤ y := by simpa [u, hbottomY] using hy0
  have hv : y ≤ v.1.2 := by
    simp only [v, htopY]
    omega
  obtain ⟨p, _hpSupport, hpY⟩ := walk_exists_second_eq_of_le w y hu hv
  exact ⟨p.1, p.2, hpY⟩

/-- A connected set with a minimal one-column hull fills that entire
column.  This is the `r = 1` branch preceding the dual argument in the
normalized-hull proof. -/
theorem IsRectHull.eq_rectangle_of_width_one
    {S : Finset Point} {s : ℕ}
    (hHull : IsRectHull S 0 0 1 s)
    (hconn : (inducedGrid S).Connected) :
    S = rectangle 0 0 1 s := by
  apply Finset.Subset.antisymm hHull.2.2.1
  intro p hpRect
  obtain ⟨bottom, hbottomS, hbottomY⟩ := hHull.2.2.2.2.2.1
  obtain ⟨top, htopS, htopY⟩ := hHull.2.2.2.2.2.2
  let u : {q : Point // q ∈ S} := ⟨bottom, hbottomS⟩
  let v : {q : Point // q ∈ S} := ⟨top, htopS⟩
  obtain ⟨w⟩ := hconn u v
  have hu : u.1.2 ≤ p.2 := by
    have hp := hpRect
    simp [rectangle] at hp
    simp [u, hbottomY]
    omega
  have hv : p.2 ≤ v.1.2 := by
    have hp := hpRect
    simp [rectangle] at hp
    simp [v, htopY]
    omega
  obtain ⟨q, _hqSupport, hqY⟩ := walk_exists_second_eq_of_le w p.2 hu hv
  have hqRect := hHull.2.2.1 q.2
  have hqp : q.1 = p := by
    apply Prod.ext
    · simp [rectangle] at hpRect hqRect
      omega
    · exact hqY
  rw [← hqp]
  exact q.2

/-- A connected set with a minimal one-row hull fills that entire row. -/
theorem IsRectHull.eq_rectangle_of_height_one
    {S : Finset Point} {r : ℕ}
    (hHull : IsRectHull S 0 0 r 1)
    (hconn : (inducedGrid S).Connected) :
    S = rectangle 0 0 r 1 := by
  apply Finset.Subset.antisymm hHull.2.2.1
  intro p hpRect
  obtain ⟨left, hleftS, hleftX⟩ := hHull.2.2.2.1
  obtain ⟨right, hrightS, hrightX⟩ := hHull.2.2.2.2.1
  let u : {q : Point // q ∈ S} := ⟨left, hleftS⟩
  let v : {q : Point // q ∈ S} := ⟨right, hrightS⟩
  obtain ⟨w⟩ := hconn u v
  have hu : u.1.1 ≤ p.1 := by
    have hp := hpRect
    simp [rectangle] at hp
    simp [u, hleftX]
    omega
  have hv : p.1 ≤ v.1.1 := by
    have hp := hpRect
    simp [rectangle] at hp
    simp [v, hrightX]
    omega
  obtain ⟨q, _hqSupport, hqX⟩ := walk_exists_first_eq_of_le w p.1 hu hv
  have hqRect := hHull.2.2.1 q.2
  have hqp : q.1 = p := by
    apply Prod.ext
    · exact hqX
    · simp [rectangle] at hpRect hqRect
      omega
  rw [← hqp]
  exact q.2

/-- The normalized hull inequality is an equality in the one-column case. -/
theorem normalizedHull_bound_of_width_one
    (κ : ℝ) {S : Finset Point} {s : ℕ}
    (hHull : IsRectHull S 0 0 1 s)
    (hconn : (inducedGrid S).Connected) :
    Real.log (tau S : ℝ) - Real.log (tauRect 1 s : ℝ)
      ≤ -κ * ((rectangle 0 0 1 s \ S).card : ℝ) := by
  rw [hHull.eq_rectangle_of_width_one hconn]
  simp [tauRect_eq]

/-- The normalized hull inequality is an equality in the one-row case. -/
theorem normalizedHull_bound_of_height_one
    (κ : ℝ) {S : Finset Point} {r : ℕ}
    (hHull : IsRectHull S 0 0 r 1)
    (hconn : (inducedGrid S).Connected) :
    Real.log (tau S : ℝ) - Real.log (tauRect r 1 : ℝ)
      ≤ -κ * ((rectangle 0 0 r 1 \ S).card : ℝ) := by
  rw [hHull.eq_rectangle_of_height_one hconn]
  simp [tauRect_eq]

end SquareMaximality
