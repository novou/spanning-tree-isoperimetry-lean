import SquareMaximality.Geometry
import Mathlib.Data.Finset.Max

set_option autoImplicit false

/-!
# Rectangular hulls of finite lattice sets

Every nonempty finite set of lattice points has a smallest axis-parallel
lattice rectangle.  Its four sides are attained by coordinate extrema of the
set.
-/

namespace SquareMaximality

/-- A set admitting a rectangular hull is nonempty. -/
theorem IsRectHull.nonempty
    {S : Finset Point} {a b : ℤ} {r s : ℕ}
    (hHull : IsRectHull S a b r s) :
    S.Nonempty := by
  obtain ⟨p, hp, _⟩ := hHull.2.2.2.1
  exact ⟨p, hp⟩

/-- A set admitting a rectangular hull has positive cardinality. -/
theorem IsRectHull.card_pos
    {S : Finset Point} {a b : ℤ} {r s : ℕ}
    (hHull : IsRectHull S a b r s) :
    0 < S.card := by
  exact Finset.card_pos.mpr hHull.nonempty

/-- Every nonempty finite set of lattice points has a rectangular hull. -/
theorem exists_isRectHull_of_nonempty
    (S : Finset Point) (hS : S.Nonempty) :
    ∃ a b : ℤ, ∃ r s : ℕ, IsRectHull S a b r s := by
  let xs : Finset ℤ := S.image Prod.fst
  let ys : Finset ℤ := S.image Prod.snd

  obtain ⟨p₀, hp₀⟩ := hS
  have hxs : xs.Nonempty := by
    exact ⟨p₀.1, Finset.mem_image_of_mem Prod.fst hp₀⟩
  have hys : ys.Nonempty := by
    exact ⟨p₀.2, Finset.mem_image_of_mem Prod.snd hp₀⟩

  let a : ℤ := xs.min' hxs
  let c : ℤ := xs.max' hxs
  let b : ℤ := ys.min' hys
  let d : ℤ := ys.max' hys
  let r : ℕ := (c - a).toNat + 1
  let s : ℕ := (d - b).toNat + 1

  have hac : a ≤ c := by
    exact Finset.min'_le xs c (Finset.max'_mem xs hxs)
  have hbd : b ≤ d := by
    exact Finset.min'_le ys d (Finset.max'_mem ys hys)
  have hr_cast : ((c - a).toNat : ℤ) = c - a := by
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hac)
  have hs_cast : ((d - b).toNat : ℤ) = d - b := by
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hbd)

  have hleft : ∃ p ∈ S, p.1 = a := by
    obtain ⟨p, hp, hpa⟩ := Finset.mem_image.mp (Finset.min'_mem xs hxs)
    exact ⟨p, hp, hpa⟩
  have hright : ∃ p ∈ S, p.1 = a + r - 1 := by
    obtain ⟨p, hp, hpc⟩ := Finset.mem_image.mp (Finset.max'_mem xs hxs)
    refine ⟨p, hp, ?_⟩
    change p.1 = c at hpc
    dsimp [r]
    rw [hr_cast]
    omega
  have hbottom : ∃ p ∈ S, p.2 = b := by
    obtain ⟨p, hp, hpb⟩ := Finset.mem_image.mp (Finset.min'_mem ys hys)
    exact ⟨p, hp, hpb⟩
  have htop : ∃ p ∈ S, p.2 = b + s - 1 := by
    obtain ⟨p, hp, hpd⟩ := Finset.mem_image.mp (Finset.max'_mem ys hys)
    refine ⟨p, hp, ?_⟩
    change p.2 = d at hpd
    dsimp [s]
    rw [hs_cast]
    omega

  refine ⟨a, b, r, s, ?_⟩
  refine ⟨by simp [r], by simp [s], ?_, hleft, hright, hbottom, htop⟩
  intro p hp
  have hpx : p.1 ∈ xs := Finset.mem_image_of_mem Prod.fst hp
  have hpy : p.2 ∈ ys := Finset.mem_image_of_mem Prod.snd hp
  have hax : a ≤ p.1 := Finset.min'_le xs p.1 hpx
  have hxc : p.1 ≤ c := Finset.le_max' xs p.1 hpx
  have hby : b ≤ p.2 := Finset.min'_le ys p.2 hpy
  have hyd : p.2 ≤ d := Finset.le_max' ys p.2 hpy
  rcases p with ⟨x, y⟩
  rw [rectangle]
  refine Finset.mem_product.mpr ⟨?_, ?_⟩
  · rw [Finset.mem_Ico]
    constructor
    · exact hax
    · change x < a + (r : ℤ)
      dsimp [r]
      rw [hr_cast]
      omega
  · rw [Finset.mem_Ico]
    constructor
    · exact hby
    · change y < b + (s : ℤ)
      dsimp [s]
      rw [hs_cast]
      omega

/-- Cardinality-positive form of `exists_isRectHull_of_nonempty`. -/
theorem exists_isRectHull_of_card_pos
    (S : Finset Point) (hS : 0 < S.card) :
    ∃ a b : ℤ, ∃ r s : ℕ, IsRectHull S a b r s := by
  exact exists_isRectHull_of_nonempty S (Finset.card_pos.mp hS)

end SquareMaximality
