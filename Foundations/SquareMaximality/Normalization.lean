module

public import SquareMaximality.Infrastructure
public import SquareMaximality.Hull

@[expose] public section

set_option autoImplicit false

/-!
# Normalizing rectangular hulls

Translation moves an arbitrary rectangular hull to one based at the origin
without changing its dimensions, induced-grid connectivity, spanning-tree
count, or number of vacant sites.
-/

namespace SquareMaximality

/-- Translating a finite lattice rectangle translates its base point and
leaves its side lengths unchanged. -/
theorem translateFinset_rectangle (a b c d : ℤ) (r s : ℕ) :
    translateFinset c d (rectangle a b r s) =
      rectangle (a + c) (b + d) r s := by
  ext p
  constructor
  · intro hp
    rw [translateFinset, Finset.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    simp [rectangle, pointTranslation] at hq ⊢
    omega
  · intro hp
    let q : Point := pointTranslation (-c) (-d) p
    have hq : q ∈ rectangle a b r s := by
      simp [q, rectangle] at hp ⊢
      omega
    have hpq : pointTranslation c d q = p := by
      rcases p with ⟨x, y⟩
      simp [q, pointTranslation]
    rw [← hpq]
    exact (mem_translateFinset c d (rectangle a b r s) q).2 hq

/-- Translating a rectangle by the negative of its base point places it at
the origin. -/
@[simp]
theorem translateFinset_rectangle_to_origin (a b : ℤ) (r s : ℕ) :
    translateFinset (-a) (-b) (rectangle a b r s) =
      rectangle 0 0 r s := by
  rw [translateFinset_rectangle]
  congr <;> omega

/-- Normalizing a rectangular hull by translating its base point to the
origin preserves the hull dimensions and all four side witnesses. -/
theorem IsRectHull.translate_to_origin
    {S : Finset Point} {a b : ℤ} {r s : ℕ}
    (hHull : IsRectHull S a b r s) :
    IsRectHull (translateFinset (-a) (-b) S) 0 0 r s := by
  rcases hHull with
    ⟨hr, hs, hsub, hleft, hright, hbottom, htop⟩
  refine ⟨hr, hs, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [translateFinset, Finset.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hqRect := hsub hq
    simp [rectangle, pointTranslation] at hqRect ⊢
    omega
  · obtain ⟨p, hp, hpa⟩ := hleft
    refine ⟨pointTranslation (-a) (-b) p,
      (mem_translateFinset (-a) (-b) S p).2 hp, ?_⟩
    simp [pointTranslation, hpa]
  · obtain ⟨p, hp, hpa⟩ := hright
    refine ⟨pointTranslation (-a) (-b) p,
      (mem_translateFinset (-a) (-b) S p).2 hp, ?_⟩
    simp [pointTranslation]
    omega
  · obtain ⟨p, hp, hpb⟩ := hbottom
    refine ⟨pointTranslation (-a) (-b) p,
      (mem_translateFinset (-a) (-b) S p).2 hp, ?_⟩
    simp [pointTranslation, hpb]
  · obtain ⟨p, hp, hpb⟩ := htop
    refine ⟨pointTranslation (-a) (-b) p,
      (mem_translateFinset (-a) (-b) S p).2 hp, ?_⟩
    simp [pointTranslation]
    omega

/-- A hull and its normalization have connected induced grids
simultaneously. -/
theorem IsRectHull.connected_iff_translate_to_origin
    {S : Finset Point} {a b : ℤ} {r s : ℕ}
    (_hHull : IsRectHull S a b r s) :
    (inducedGrid S).Connected ↔
      (inducedGrid (translateFinset (-a) (-b) S)).Connected :=
  (inducedGridTranslationIso (-a) (-b) S).connected_iff

/-- Normalizing a hull leaves its spanning-tree count unchanged. -/
theorem IsRectHull.tau_translate_to_origin
    {S : Finset Point} {a b : ℤ} {r s : ℕ}
    (_hHull : IsRectHull S a b r s) :
    tau (translateFinset (-a) (-b) S) = tau S := by
  simp

/-- Normalizing a hull preserves the number of lattice sites of the hull
that are absent from the set. -/
theorem IsRectHull.vacancy_card_translate_to_origin
    {S : Finset Point} {a b : ℤ} {r s : ℕ}
    (hHull : IsRectHull S a b r s) :
    (rectangle 0 0 r s \ translateFinset (-a) (-b) S).card =
      (rectangle a b r s \ S).card := by
  rw [rectangle_sdiff_card_of_subset hHull.translate_to_origin.2.2.1,
    rectangle_sdiff_card_of_subset hHull.2.2.1]
  simp [translateFinset]

end SquareMaximality
