import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

set_option autoImplicit false

/-!
# One-dimensional windows

This file formalizes Lemma 4.1 of `general.tex`.  A subset of the discrete
line `{0, ..., L}` is represented by a `Finset Nat`.  An internal run is
represented canonically by its left endpoint; `intervalComponent` recovers
the actual maximal consecutive interval belonging to that endpoint.
-/

namespace SquareMaximality

namespace Windows

/-- The discrete line `{0, ..., L}`. -/
def line (L : ℕ) : Finset ℕ := Finset.range (L + 1)

/-- The (closed) integer interval `[t, t+p]`. -/
def window (t p : ℕ) : Finset ℕ := Finset.Icc t (t + p)

/-- All starts whose length-`p` window is contained in `line L`. -/
def validWindowStarts (L p : ℕ) : Finset ℕ :=
  (line L).filter fun t => t + p ≤ L

/-- Valid windows which meet `B`, recorded by their start. -/
def meetingWindowStarts (L p : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (validWindowStarts L p).filter fun t => (window t p ∩ B).Nonempty

/-- The final consecutive run of `B` which touches `L` (empty if `L ∉ B`). -/
def rightBoundaryRun (L : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (line L).filter fun x => Finset.Icc x L ⊆ B

/--
Canonical representatives of the internal interval components of `B`.

The representative `a` says that `a` is in `B`, its predecessor is not,
and the run starting at `a` does not continue all the way to `L`.
-/
def internalRunStarts (L : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (line L).filter fun a =>
    0 < a ∧ a ∈ B ∧ a - 1 ∉ B ∧ a ∉ rightBoundaryRun L B

/-- The maximal consecutive interval of `B` beginning at `a`. -/
def intervalComponent (L : ℕ) (B : Finset ℕ) (a : ℕ) : Finset ℕ :=
  (Finset.Icc a L).filter fun x => Finset.Icc a x ⊆ B

/-- The finite family of actual internal interval components of `B`. -/
def internalRuns (L : ℕ) (B : Finset ℕ) : Finset (Finset ℕ) :=
  (internalRunStarts L B).image (intervalComponent L B)

/-- Starts of valid windows which approach the run beginning at `a` from the left. -/
private def approachStarts (L p a : ℕ) : Finset ℕ :=
  (validWindowStarts L p).filter fun t => t < a ∧ a ≤ t + p

@[simp] theorem mem_line {L x : ℕ} : x ∈ line L ↔ x ≤ L := by
  simp [line, Nat.lt_succ_iff]

@[simp] theorem mem_window {t p x : ℕ} : x ∈ window t p ↔ t ≤ x ∧ x ≤ t + p := by
  simp [window]

@[simp] theorem mem_validWindowStarts {L p t : ℕ} :
    t ∈ validWindowStarts L p ↔ t + p ≤ L := by
  simp only [validWindowStarts, Finset.mem_filter, mem_line]
  omega

@[simp] theorem mem_meetingWindowStarts {L p t : ℕ} {B : Finset ℕ} :
    t ∈ meetingWindowStarts L p B ↔
      t + p ≤ L ∧ ∃ x ∈ B, t ≤ x ∧ x ≤ t + p := by
  simp only [meetingWindowStarts, Finset.mem_filter, mem_validWindowStarts]
  constructor
  · rintro ⟨ht, hne⟩
    rcases hne with ⟨x, hx⟩
    have hx' := Finset.mem_inter.mp hx
    exact ⟨ht, x, hx'.2, (mem_window.mp hx'.1).1, (mem_window.mp hx'.1).2⟩
  · rintro ⟨ht, x, hxB, htx, hxp⟩
    refine ⟨ht, ⟨x, Finset.mem_inter.mpr ⟨?_, hxB⟩⟩⟩
    exact mem_window.mpr ⟨htx, hxp⟩

@[simp] theorem mem_rightBoundaryRun {L x : ℕ} {B : Finset ℕ} :
    x ∈ rightBoundaryRun L B ↔ x ≤ L ∧ Finset.Icc x L ⊆ B := by
  simp [rightBoundaryRun]

@[simp] theorem mem_internalRunStarts {L a : ℕ} {B : Finset ℕ} :
    a ∈ internalRunStarts L B ↔
      a ≤ L ∧ 0 < a ∧ a ∈ B ∧ a - 1 ∉ B ∧ a ∉ rightBoundaryRun L B := by
  simp [internalRunStarts]

@[simp] theorem mem_intervalComponent {L a x : ℕ} {B : Finset ℕ} :
    x ∈ intervalComponent L B a ↔
      a ≤ x ∧ x ≤ L ∧ Finset.Icc a x ⊆ B := by
  simp only [intervalComponent, Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem rightBoundaryRun_subset (L : ℕ) (B : Finset ℕ) :
    rightBoundaryRun L B ⊆ B := by
  intro x hx
  rw [mem_rightBoundaryRun] at hx
  exact hx.2 (by simp [hx.1])

theorem intervalComponent_contains_start {L a : ℕ} {B : Finset ℕ}
    (haL : a ≤ L) (haB : a ∈ B) : a ∈ intervalComponent L B a := by
  rw [mem_intervalComponent]
  refine ⟨le_rfl, haL, ?_⟩
  simpa using haB

theorem intervalComponent_subset_B {L a : ℕ} {B : Finset ℕ} :
    intervalComponent L B a ⊆ B := by
  intro x hx
  rw [mem_intervalComponent] at hx
  exact hx.2.2 (by simp [hx.1])

theorem intervalComponent_interval {L a x z : ℕ} {B : Finset ℕ}
    (hz : z ∈ intervalComponent L B a) (hax : a ≤ x) (hxz : x ≤ z) :
    x ∈ intervalComponent L B a := by
  rw [mem_intervalComponent] at hz ⊢
  refine ⟨hax, hxz.trans hz.2.1, ?_⟩
  intro y hy
  exact hz.2.2 (by simp only [Finset.mem_Icc] at hy ⊢; omega)

theorem internal_component_avoids_endpoints {L a : ℕ} {B : Finset ℕ}
    (ha : a ∈ internalRunStarts L B) :
    0 ∉ intervalComponent L B a ∧ L ∉ intervalComponent L B a := by
  rw [mem_internalRunStarts] at ha
  constructor
  · intro h0
    rw [mem_intervalComponent] at h0
    omega
  · intro hL
    rw [mem_intervalComponent] at hL
    exact ha.2.2.2.2 (mem_rightBoundaryRun.mpr ⟨ha.1, hL.2.2⟩)

theorem intervalComponent_injective_on_internal_starts (L : ℕ) (B : Finset ℕ) :
    Set.InjOn (intervalComponent L B) (internalRunStarts L B) := by
  intro a ha b hb hab
  change a ∈ internalRunStarts L B at ha
  change b ∈ internalRunStarts L B at hb
  rw [mem_internalRunStarts] at ha hb
  have haa : a ∈ intervalComponent L B a :=
    intervalComponent_contains_start ha.1 ha.2.2.1
  have hbb : b ∈ intervalComponent L B b :=
    intervalComponent_contains_start hb.1 hb.2.2.1
  have hba : b ≤ a := (mem_intervalComponent.mp (hab ▸ haa)).1
  have hab' : a ≤ b := (mem_intervalComponent.mp (hab.symm ▸ hbb)).1
  omega

theorem card_internalRuns (L : ℕ) (B : Finset ℕ) :
    (internalRuns L B).card = (internalRunStarts L B).card := by
  exact Finset.card_image_of_injOn (intervalComponent_injective_on_internal_starts L B)

private theorem card_approachStarts_le (L p a : ℕ) :
    (approachStarts L p a).card ≤ p := by
  have hsub : approachStarts L p a ⊆ Finset.Ico (a - p) a := by
    intro t ht
    simp only [approachStarts, Finset.mem_filter, mem_validWindowStarts] at ht
    simp only [Finset.mem_Ico]
    omega
  calc
    (approachStarts L p a).card ≤ (Finset.Ico (a - p) a).card :=
      Finset.card_le_card hsub
    _ ≤ p := by simp; omega

private def ordinaryChargedStarts (L p : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (validWindowStarts L p).filter fun t => t ∈ B ∧ t ∉ rightBoundaryRun L B

private def rightChargedStarts (L p : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (validWindowStarts L p).filter fun t => t + p ∈ rightBoundaryRun L B

private def internalChargedStarts (L p : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (internalRunStarts L B).biUnion (approachStarts L p)

private theorem rightBoundaryRun_upward {L x y : ℕ} {B : Finset ℕ}
    (hx : x ∈ rightBoundaryRun L B) (hxy : x ≤ y) (hyL : y ≤ L) :
    y ∈ rightBoundaryRun L B := by
  rw [mem_rightBoundaryRun] at hx ⊢
  refine ⟨hyL, ?_⟩
  intro z hz
  apply hx.2
  simp only [Finset.mem_Icc] at hz ⊢
  omega

private theorem card_ordinaryChargedStarts_le (L p : ℕ) (B : Finset ℕ) :
    (ordinaryChargedStarts L p B).card ≤
      (B \ rightBoundaryRun L B).card := by
  apply Finset.card_le_card
  intro t ht
  simp only [ordinaryChargedStarts, Finset.mem_filter] at ht
  exact Finset.mem_sdiff.mpr ht.2

private theorem card_rightChargedStarts_le (L p : ℕ) (B : Finset ℕ) :
    (rightChargedStarts L p B).card ≤ (rightBoundaryRun L B).card := by
  refine Finset.card_le_card_of_injOn (fun t => t + p) ?_ ?_
  · intro t ht
    change t ∈ rightChargedStarts L p B at ht
    simp only [rightChargedStarts, Finset.mem_filter] at ht
    exact ht.2
  · intro t₁ ht₁ t₂ ht₂ h
    exact Nat.add_right_cancel h

private theorem card_internalChargedStarts_le (L p : ℕ) (B : Finset ℕ) :
    (internalChargedStarts L p B).card ≤
      (internalRunStarts L B).card * p := by
  exact Finset.card_biUnion_le_card_mul _ _ _ fun a _ => card_approachStarts_le L p a

private theorem meetingWindowStarts_subset_charges (L p : ℕ) (B : Finset ℕ) :
    meetingWindowStarts L p B ⊆
      ordinaryChargedStarts L p B ∪
        (rightChargedStarts L p B ∪ internalChargedStarts L p B) := by
  intro t ht
  rw [mem_meetingWindowStarts] at ht
  rcases ht with ⟨htvalid, b, hbB, htb, hbupper⟩
  by_cases hmeetsRight :
      ∃ x ∈ rightBoundaryRun L B, t ≤ x ∧ x ≤ t + p
  · rcases hmeetsRight with ⟨x, hxright, htx, hxupper⟩
    have hendRight : t + p ∈ rightBoundaryRun L B :=
      rightBoundaryRun_upward hxright hxupper htvalid
    apply Finset.mem_union.mpr
    exact Or.inr (Finset.mem_union.mpr (Or.inl (by
      simp only [rightChargedStarts, Finset.mem_filter, mem_validWindowStarts]
      exact ⟨htvalid, hendRight⟩)))
  · by_cases htB : t ∈ B
    · have htNotRight : t ∉ rightBoundaryRun L B := by
        intro htRight
        exact hmeetsRight ⟨t, htRight, le_rfl, by omega⟩
      apply Finset.mem_union.mpr
      exact Or.inl (by
        simp only [ordinaryChargedStarts, Finset.mem_filter, mem_validWindowStarts]
        exact ⟨htvalid, htB, htNotRight⟩)
    · let S : Finset ℕ := window t p ∩ B
      have hS : S.Nonempty := by
        refine ⟨b, Finset.mem_inter.mpr ⟨?_, hbB⟩⟩
        exact mem_window.mpr ⟨htb, hbupper⟩
      let a : ℕ := S.min' hS
      have haS : a ∈ S := S.min'_mem hS
      have haWin : a ∈ window t p := (Finset.mem_inter.mp haS).1
      have haB : a ∈ B := (Finset.mem_inter.mp haS).2
      have hta : t ≤ a := (mem_window.mp haWin).1
      have haupper : a ≤ t + p := (mem_window.mp haWin).2
      have htaStrict : t < a := by
        have hat : a ≠ t := by
          intro h
          exact htB (h ▸ haB)
        omega
      have haPred : a - 1 ∉ B := by
        intro haPredB
        have haPredWin : a - 1 ∈ window t p := by
          rw [mem_window]
          omega
        have haPredS : a - 1 ∈ S :=
          Finset.mem_inter.mpr ⟨haPredWin, haPredB⟩
        have hmin : a ≤ a - 1 := S.min'_le (a - 1) haPredS
        omega
      have haNotRight : a ∉ rightBoundaryRun L B := by
        intro haRight
        exact hmeetsRight ⟨a, haRight, hta, haupper⟩
      have haInternal : a ∈ internalRunStarts L B := by
        rw [mem_internalRunStarts]
        exact ⟨haupper.trans htvalid, by omega, haB, haPred, haNotRight⟩
      have htApproach : t ∈ approachStarts L p a := by
        simp only [approachStarts, Finset.mem_filter, mem_validWindowStarts]
        exact ⟨htvalid, htaStrict, haupper⟩
      apply Finset.mem_union.mpr
      apply Or.inr
      apply Finset.mem_union.mpr
      apply Or.inr
      exact Finset.mem_biUnion.mpr ⟨a, haInternal, htApproach⟩

/--
**One-dimensional window lemma (Lemma 4.1).**

If `B ⊆ {0, ..., L}` and `0 ≤ p ≤ L`, then the number of length-`p`
integer windows in the line which meet `B` is at most `|B| + p i(B)`,
where `i(B)` is the number of internal interval components.
-/
theorem one_dimensional_window (L p : ℕ) (B : Finset ℕ)
    (_hB : B ⊆ line L) (_hp : p ≤ L) :
    (meetingWindowStarts L p B).card ≤
      B.card + p * (internalRunStarts L B).card := by
  let A := ordinaryChargedStarts L p B
  let R := rightChargedStarts L p B
  let E := internalChargedStarts L p B
  have hcover : meetingWindowStarts L p B ⊆ A ∪ (R ∪ E) := by
    simpa [A, R, E] using meetingWindowStarts_subset_charges L p B
  have hmeeting : (meetingWindowStarts L p B).card ≤ (A ∪ (R ∪ E)).card :=
    Finset.card_le_card hcover
  have hunion : (A ∪ (R ∪ E)).card ≤ A.card + R.card + E.card := by
    calc
      (A ∪ (R ∪ E)).card ≤ A.card + (R ∪ E).card :=
        Finset.card_union_le A (R ∪ E)
      _ ≤ A.card + (R.card + E.card) :=
        Nat.add_le_add_left (Finset.card_union_le R E) A.card
      _ = A.card + R.card + E.card := by omega
  have hA : A.card ≤ (B \ rightBoundaryRun L B).card := by
    simpa [A] using card_ordinaryChargedStarts_le L p B
  have hR : R.card ≤ (rightBoundaryRun L B).card := by
    simpa [R] using card_rightChargedStarts_le L p B
  have hE : E.card ≤ (internalRunStarts L B).card * p := by
    simpa [E] using card_internalChargedStarts_le L p B
  have hpartition :
      (B \ rightBoundaryRun L B).card + (rightBoundaryRun L B).card = B.card :=
    Finset.card_sdiff_add_card_eq_card (rightBoundaryRun_subset L B)
  calc
    (meetingWindowStarts L p B).card ≤ A.card + R.card + E.card :=
      hmeeting.trans hunion
    _ ≤ B.card + (internalRunStarts L B).card * p := by omega
    _ = B.card + p * (internalRunStarts L B).card := by
      rw [Nat.mul_comm]

/-- The same theorem stated using the finite family of interval components itself. -/
theorem one_dimensional_window_runs (L p : ℕ) (B : Finset ℕ)
    (hB : B ⊆ line L) (hp : p ≤ L) :
    (meetingWindowStarts L p B).card ≤ B.card + p * (internalRuns L B).card := by
  rw [card_internalRuns]
  exact one_dimensional_window L p B hB hp

end Windows

end SquareMaximality
