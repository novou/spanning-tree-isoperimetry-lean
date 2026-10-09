import SpanningTreeIsoperimetry.FerrersFoldStrict

/-! The small maximal blocks and full Ferrers-fold strictness alternative. -/
namespace SpanningTreeIsoperimetry.CornerFolds

open Polarization StripPolarization Ferrers DomainIsometries
open scoped Classical

/-- A Ferrers diagram supported on its two coordinate axes. -/
def IsFerrersHook (M : Diagram) : Prop := ∀ a ∈ M, a.1 = 0 ∨ a.2 = 0

def hookStrictPath (u p q i : ℕ) : Vertex :=
  if i ≤ p - 1 then ((u : ℤ) - p - 1 + i, 1)
  else if i ≤ u - 1 then ((u : ℤ) - 2, 1 + (i : ℤ) - (p - 1 : ℕ))
  else ((u : ℤ) - 1, q)

@[simp] theorem hookStrictPath_start (u p q : ℕ) :
    hookStrictPath u p q 0 = ((u : ℤ) - p - 1, 1) := by simp [hookStrictPath]

theorem hookStrictPath_end {u p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hsum : u + 1 = p + q) :
    hookStrictPath u p q u = ((u : ℤ) - 1, (q : ℤ)) := by
  have hp' : ¬u ≤ p - 1 := by omega
  have hu' : ¬u ≤ u - 1 := by omega
  simp [hookStrictPath, hp', hu']

theorem hookStrictPath_adj {u p q i : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hsum : u + 1 = p + q) (hi : i < u) :
    lattice.Adj (hookStrictPath u p q i) (hookStrictPath u p q (i + 1)) := by
  simp only [hookStrictPath, lattice]
  split_ifs <;> simp only [abs_eq (by norm_num : (0 : ℤ) ≤ 1), Nat.cast_add, Nat.cast_one, true_and] <;> omega

theorem hookStrictPath_bounds {u v p q i : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hsum : u + 1 = p + q) (hv : v = u + 1) (hi : i ≤ u) :
    let x := hookStrictPath u p q i
    x ∈ rectangle u v ∧ ((x.1 < (u : ℤ) - 1 ∧ 0 < x.2) ∨ (q : ℤ) ≤ x.2) ∧
      x.2 < x.1 + (v - u + 1 : ℕ) := by
  simp only [hookStrictPath, mem_rectangle]
  split_ifs <;> omega

theorem bottomRight_absent_of_hook {u p q : ℕ} {M : Diagram} (hHook : IsFerrersHook M)
    (hbox : ∀ a ∈ M, a.1 < p ∧ a.2 < q) (x : Vertex)
    (hescape : (x.1 < (u : ℤ) - 1 ∧ 0 < x.2) ∨ (q : ℤ) ≤ x.2) : x ∉ bottomRightDefect u M := by
  intro hx
  obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
  have hb := hbox a ha
  have hh := hHook a ha
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  dsimp [verticalReflection, SquareMaximality.Boundary.ofNatPoint] at he1 he2
  omega

/-- The exceptional `(t,c)=(1,2)` hook still has an explicit strict path. -/
theorem ferrers_hook_fold_strict {u v : ℕ} {M : Diagram} (hM : IsFerrers M)
    (hHook : IsFerrersHook M) (hp : 2 ≤ ferrersWidth M) (hq : 2 ≤ ferrersHeight M)
    (hsum : u + 1 = ferrersWidth M + ferrersHeight M) (hv : v = u + 1)
    (hheight : (0, v - u) ∈ M) (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (rectangle u v \ bottomRightDefect u M) z <
      faceDeterminant (ferrersFoldCandidate u v 1 M) z := by
  have hcorner : (1 - 1, v - u + 1 - 1) ∈ M := by simpa using hheight
  have hsplit : ∀ a ∈ M, a.1 < 1 ∨ a.2 < v - u + 1 := by
    intro a ha
    have hh := hHook a ha
    omega
  have hpol := polarize_ferrersFoldCandidate hM (show u ≤ v by omega) (by decide : 0 < 1)
    (show 1 ≤ u by omega) hcorner hsplit
  let P := preferredDomain (ferrersFoldCandidate u v 1 M) (shiftedDiagonalReflection (v - u + 1 : ℕ))
    (fun x => x.2 < x.1 + (v - u + 1 : ℕ))
  have hmem : ∀ i, i ≤ u → hookStrictPath u (ferrersWidth M) (ferrersHeight M) i ∈ P := by
    intro i hi
    change _ ∈ preferredDomain _ _ _
    rw [preferredDomain, Finset.mem_filter, hpol]
    have hb := hookStrictPath_bounds hp hq hsum hv hi
    exact ⟨Finset.mem_sdiff.mpr ⟨hb.1, bottomRight_absent_of_hook hHook
      (fun a ha => ferrers_extent_bounds ha) _ hb.2.1⟩, hb.2.2⟩
  obtain ⟨w⟩ := reachable_along P (hookStrictPath u (ferrersWidth M) (ferrersHeight M)) u hmem
    (fun i hi => hookStrictPath_adj hp hq hsum hi)
  have hop : OppositeSingletons (ferrersFoldCandidate u v 1 M) (shiftedDiagonalReflection (v - u + 1 : ℕ))
      (hookStrictPath u (ferrersWidth M) (ferrersHeight M) 0)
      (hookStrictPath u (ferrersWidth M) (ferrersHeight M) u) := by
    rw [hookStrictPath_start, hookStrictPath_end hp hq hsum]
    have he : ((v - u + 1 : ℕ) : ℤ) - 1 = 1 := by omega
    have hh := ferrersStrictPath_opposite (M := M) (u := u) (v := v) (t := 1)
      (p := ferrersWidth M) (q := ferrersHeight M) (by omega) (by decide) (by omega) (by omega)
      (fun a ha => ferrers_extent_bounds ha) (by omega)
    simpa only [he, Nat.cast_one] using hh
  have h := shiftedDiagonal_lower_determinant_strict (ferrersFoldCandidate u v 1 M) (v - u + 1 : ℕ) z hz w hop
  rw [hpol] at h
  exact h

theorem ferrers_hook_tailX {M : Diagram} (hM : IsFerrers M) (hHook : IsFerrersHook M)
    (hne : M.Nonempty) : ferrersTailX M 1 = horizontalStrip (ferrersWidth M - 1) := by
  ext x
  rw [mem_ferrersTailX, mem_horizontalStrip]
  constructor
  · intro hx
    have hh := hHook _ hx
    have hb := ferrers_extent_bounds hx
    exact ⟨by omega, by omega⟩
  · intro hx
    exact hM _ (ferrers_width_corner hM hne) _ (by omega) (by omega)

theorem ferrers_hook_tailY {M : Diagram} (hM : IsFerrers M) (hHook : IsFerrersHook M)
    (hne : M.Nonempty) : transpose (ferrersTailY M 1) = horizontalStrip (ferrersHeight M - 1) := by
  ext x
  rw [mem_transpose, mem_ferrersTailY, mem_horizontalStrip]
  simp only [Prod.fst_swap, Prod.snd_swap]
  constructor
  · intro hx
    have hh := hHook _ hx
    have hb := ferrers_extent_bounds hx
    exact ⟨by omega, by omega⟩
  · intro hx
    exact hM _ (ferrers_height_corner hM hne) _ (by omega) (by omega)

/-- Full strictness alternative for the actual maximal-block Ferrers fold:
the only non-strict alternative is a square hook, whose tails are strips. -/
theorem exists_ferrers_fold_strict_alternative {u v : ℕ} {M : Diagram} (hM : IsFerrers M)
    (huv : u ≤ v) (hcard : M.card ≤ u) (hheight : (0, v - u) ∈ M)
    (hp : 2 ≤ ferrersWidth M) (hq : 2 ≤ ferrersHeight M) :
    ∃ t : ℕ, 0 < t ∧ t < u ∧ (t - 1, v - u + t - 1) ∈ M ∧
      (∀ a ∈ M, a.1 < t ∨ a.2 < v - u + t) ∧
      ((u = v ∧ IsFerrersHook M ∧ t = 1 ∧
        ferrersTailX M t = horizontalStrip (ferrersWidth M - 1) ∧
        transpose (ferrersTailY M (v - u + t)) = horizontalStrip (ferrersHeight M - 1)) ∨
        ∀ z : ℝ, 4 ≤ z → faceDeterminant (rectangle u v \ bottomRightDefect u M) z <
          faceDeterminant (ferrersFoldCandidate u v t M) z) := by
  obtain ⟨t, ht0, hcorner, hblock, hsplit, hblockCard⟩ := exists_maximal_ferrers_block hM (v - u) hheight
  have hne : M.Nonempty := ⟨_, hheight⟩
  have hwidth := ferrers_width_corner hM hne
  have hheight' := ferrers_height_corner hM hne
  have hu : 2 ≤ u := by
    have hh := (ferrers_coordinate_lt_card hM hwidth).1
    omega
  have htu : t ≤ u := by
    have h := (ferrers_coordinate_lt_card hM hcorner).1
    omega
  have hc : 0 < v - u + t := by omega
  have hmul : t * t ≤ t * (v - u + t) := Nat.mul_le_mul_left t (by omega)
  have htlt : t < u := by nlinarith
  refine ⟨t, ht0, htlt, hcorner, hsplit, ?_⟩
  by_cases hlarge : 2 ≤ t * (v - u + t - 1)
  · exact Or.inr (fun z hz => ferrers_fold_strict_of_large_block hM huv hcard ht0 hcorner hsplit hlarge z hz)
  · have hc2 : v - u + t ≤ 2 := by
      by_contra h
      have hh := Nat.mul_le_mul (show 1 ≤ t by omega) (show 2 ≤ v - u + t - 1 by omega)
      omega
    have ht1 : t = 1 := by
      by_contra h
      have hh := Nat.mul_le_mul (show 2 ≤ t by omega) (show 1 ≤ v - u + t - 1 by omega)
      omega
    subst t
    by_cases hc1 : v - u + 1 = 1
    · have heq : u = v := by omega
      have hHook : IsFerrersHook M := by
        intro a ha
        have hh := hsplit a ha
        omega
      left
      exact ⟨heq, hHook, rfl, ferrers_hook_tailX hM hHook hne,
        by rw [hc1]; exact ferrers_hook_tailY hM hHook hne⟩
    · have hcEq : v - u + 1 = 2 := by omega
      have hv : v = u + 1 := by omega
      by_cases hgap : 2 ≤ (u : ℤ) - ferrersWidth M - ferrersHeight M + (v - u + 1 : ℕ)
      · right
        have hb := ferrers_extent_bounds hcorner
        exact fun z hz => ferrers_fold_strict_of_gap hM huv (by decide) (by omega) (by omega)
          (by omega) hcorner hsplit (fun a ha => ferrers_extent_bounds ha) hgap z hz
      · have hcount := (ferrers_axes_block_card hM (by omega : 0 < ferrersWidth M)
          (by omega : 0 < ferrersHeight M) (by decide : 0 < 1) hc hwidth hheight' hcorner).trans hcard
        have hsum : u + 1 = ferrersWidth M + ferrersHeight M := by omega
        have hHook : IsFerrersHook M := by
          intro a ha
          by_contra hn
          have h11 : (2 - 1, 2 - 1) ∈ M := hM a ha _ (by omega) (by omega)
          have hcount' := (ferrers_axes_block_card hM (by omega : 0 < ferrersWidth M)
            (by omega : 0 < ferrersHeight M) (by decide : 0 < 2) (by decide : 0 < 2)
            hwidth hheight' h11).trans hcard
          norm_num only at hcount'
          omega
        exact Or.inr (fun z hz => ferrers_hook_fold_strict hM hHook hp hq hsum hv hheight z hz)

/-- The paper's height condition is equivalent to a literal cell of the diagram. -/
theorem ferrers_height_cell_iff {M : Diagram} (hM : IsFerrers M) (d : ℕ) :
    (0, d) ∈ M ↔ d < ferrersHeight M := by
  constructor
  · intro hd
    exact (ferrers_extent_bounds hd).2
  · intro hd
    have hne : M.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
      intro he
      simp [he, ferrersHeight] at hd)
    exact hM _ (ferrers_height_corner hM hne) _ (by omega) (by omega)

theorem ferrers_horizontal_of_height_le_one {M : Diagram} (hM : IsFerrers M)
    (hh : ferrersHeight M ≤ 1) : M = horizontalStrip (ferrersWidth M) := by
  ext p
  rw [mem_horizontalStrip]
  constructor
  · intro hp
    have hb := ferrers_extent_bounds hp
    exact ⟨hb.1, by omega⟩
  · intro hp
    have hne : M.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
      intro he
      simp [he, ferrersWidth] at hp)
    exact hM _ (ferrers_width_corner hM hne) p (by omega) (by omega)

theorem ferrers_vertical_of_width_le_one {M : Diagram} (hM : IsFerrers M)
    (hw : ferrersWidth M ≤ 1) : M = transpose (horizontalStrip (ferrersHeight M)) := by
  ext p
  rw [mem_transpose, mem_horizontalStrip]
  simp only [Prod.fst_swap, Prod.snd_swap]
  constructor
  · intro hp
    have hb := ferrers_extent_bounds hp
    exact ⟨hb.2, by omega⟩
  · intro hp
    have hne : M.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
      intro he
      simp [he, ferrersHeight] at hp)
    exact hM _ (ferrers_height_corner hM hne) p (by omega) (by omega)

/-- Concrete nonstrip hypotheses supply the two extent bounds used above. -/
theorem ferrers_nonstrip_extents {M : Diagram} (hM : IsFerrers M)
    (hnotX : M ≠ horizontalStrip M.card) (hnotY : M ≠ transpose (horizontalStrip M.card)) :
    2 ≤ ferrersWidth M ∧ 2 ≤ ferrersHeight M := by
  constructor
  · by_contra h
    have heq := ferrers_vertical_of_width_le_one hM (by omega)
    have hc := congrArg Finset.card heq
    simp only [card_transpose, card_horizontalStrip] at hc
    exact hnotY (by simpa only [← hc] using heq)
  · by_contra h
    have heq := ferrers_horizontal_of_height_le_one hM (by omega)
    have hc := congrArg Finset.card heq
    simp only [card_horizontalStrip] at hc
    exact hnotX (by simpa only [← hc] using heq)

end SpanningTreeIsoperimetry.CornerFolds
