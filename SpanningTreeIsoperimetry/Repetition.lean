import SpanningTreeIsoperimetry.Ferrers

/-!
# Row and column repetition for Ferrers defects

Duplicating row `j` increases by one the height of precisely the columns
meeting that row.  Moving each excluded start upward in those columns gives
a direct injection between the excluded starts before and after duplication.
The proof works for every finite visited set.
-/

namespace SpanningTreeIsoperimetry.Ferrers

/-- Duplicating row `j`, expressed by the columns which meet it. -/
def duplicateRow (M : Diagram) (j : ℕ) : Diagram :=
  M ∪ (M.filter (fun p => (p.1, j) ∈ M)).image (fun p => (p.1, p.2 + 1))

theorem mem_duplicateRow {M : Diagram} {j : ℕ} {t : Point} :
    t ∈ duplicateRow M j ↔ t ∈ M ∨
      ∃ p ∈ M, (p.1, j) ∈ M ∧ (p.1, p.2 + 1) = t := by
  simp only [duplicateRow, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro (ht | ⟨p, ⟨hp, hpj⟩, heq⟩)
    · exact Or.inl ht
    · exact Or.inr ⟨p, hp, hpj, heq⟩
  · rintro (ht | ⟨p, hp, hpj, heq⟩)
    · exact Or.inl ht
    · exact Or.inr ⟨p, ⟨hp, hpj⟩, heq⟩

/-- This proves that the column-based definition is exactly row repetition:
rows through `j` stay put and all subsequent rows are copies of their
predecessors. In particular row `j+1` repeats row `j`. -/
theorem mem_duplicateRow_iff {M : Diagram} (hM : IsFerrers M) (j : ℕ) (t : Point) :
    t ∈ duplicateRow M j ↔ if t.2 ≤ j then t ∈ M else (t.1, t.2 - 1) ∈ M := by
  rw [mem_duplicateRow]
  by_cases htj : t.2 ≤ j
  · rw [ite_eq_left htj]
    constructor
    · rintro (ht | ⟨p, _, hpj, heq⟩)
      · exact ht
      · have hx := congrArg Prod.fst heq
        exact hM (p.1, j) hpj t (by dsimp at hx; omega) htj
    · exact Or.inl
  · rw [ite_eq_right htj]
    constructor
    · rintro (ht | ⟨p, hp, _, heq⟩)
      · exact hM t ht (t.1, t.2 - 1) le_rfl (Nat.sub_le _ _)
      · have hx := congrArg Prod.fst heq
        have hy := congrArg Prod.snd heq
        have hpeq : p = (t.1, t.2 - 1) := by
          apply Prod.ext
          · simpa using hx
          · dsimp at hy
            omega
        exact hpeq ▸ hp
    · intro ht
      refine Or.inr ⟨(t.1, t.2 - 1), ht, ?_, ?_⟩
      · exact hM (t.1, t.2 - 1) ht (t.1, j) le_rfl (by omega)
      · apply Prod.ext
        · rfl
        · dsimp
          omega

theorem duplicateRow_isFerrers {M : Diagram} (hM : IsFerrers M) (j : ℕ) :
    IsFerrers (duplicateRow M j) := by
  intro p hp q hqx hqy
  rw [mem_duplicateRow_iff hM j] at hp ⊢
  by_cases hpj : p.2 ≤ j
  · rw [ite_eq_left hpj] at hp
    have hqj : q.2 ≤ j := le_trans hqy hpj
    rw [ite_eq_left hqj]
    exact hM p hp q hqx hqy
  · rw [ite_eq_right hpj] at hp
    by_cases hqj : q.2 ≤ j
    · rw [ite_eq_left hqj]
      exact hM (p.1, p.2 - 1) hp q hqx (by omega)
    · rw [ite_eq_right hqj]
      exact hM (p.1, p.2 - 1) hp (q.1, q.2 - 1) hqx (by omega)

/-- Move an excluded start upward if its column is lengthened. -/
def liftRowStart (M : Diagram) (j : ℕ) (t : Point) : Point :=
  if (t.1, j) ∈ M then (t.1, t.2 + 1) else t

@[simp] theorem liftRowStart_fst (M : Diagram) (j : ℕ) (t : Point) :
    (liftRowStart M j t).1 = t.1 := by
  unfold liftRowStart
  split_ifs <;> rfl

theorem liftRowStart_injective (M : Diagram) (j : ℕ) :
    Function.Injective (liftRowStart M j) := by
  intro t u heq
  have hx : t.1 = u.1 := by simpa using congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  apply Prod.ext hx
  by_cases ht : (t.1, j) ∈ M
  · have hu : (u.1, j) ∈ M := hx ▸ ht
    simpa [liftRowStart, ht, hu] using hy
  · have hu : (u.1, j) ∉ M := by simpa [← hx] using ht
    simpa [liftRowStart, ht, hu] using hy

theorem liftRowStart_mem {M : Diagram} {j : ℕ} {t : Point} (ht : t ∈ M) :
    liftRowStart M j t ∈ duplicateRow M j := by
  by_cases htj : (t.1, j) ∈ M
  · rw [liftRowStart, ite_eq_left htj]
    exact mem_duplicateRow.mpr (Or.inr ⟨t, ht, htj, rfl⟩)
  · rw [liftRowStart, ite_eq_right htj]
    exact mem_duplicateRow.mpr (Or.inl ht)

/-- Every hit after lifting pulls back to a hit before duplication. -/
theorem shift_lift_mem_imp_shift_mem {M : Diagram} (hM : IsFerrers M)
    (j : ℕ) (t p : Point)
    (hmem : shift (liftRowStart M j t) p ∈ duplicateRow M j) : shift t p ∈ M := by
  rw [mem_duplicateRow] at hmem
  by_cases htj : (t.1, j) ∈ M
  · rw [liftRowStart, ite_eq_left htj] at hmem
    rcases hmem with hmem | ⟨q, hq, _, heq⟩
    · exact hM _ hmem (shift t p) le_rfl (by dsimp [shift]; omega)
    · have hx := congrArg Prod.fst heq
      have hy := congrArg Prod.snd heq
      have hqeq : q = shift t p := by
        apply Prod.ext
        · simpa [shift] using hx
        · dsimp [shift] at hy ⊢
          omega
      exact hqeq ▸ hq
  · rw [liftRowStart, ite_eq_right htj] at hmem
    rcases hmem with hmem | ⟨q, _, hqj, heq⟩
    · exact hmem
    · have hx := congrArg Prod.fst heq
      have htmem : (t.1, j) ∈ M := hM (q.1, j) hqj (t.1, j)
        (by dsimp [shift] at hx; omega) le_rfl
      exact (htj htmem).elim

theorem lift_excluded_start {M P : Diagram} (hM : IsFerrers M) (j : ℕ)
    {t : Point} (ht : t ∈ M \ hitStarts M P) :
    liftRowStart M j t ∈ duplicateRow M j \ hitStarts (duplicateRow M j) P := by
  obtain ⟨htM, htnot⟩ := Finset.mem_sdiff.mp ht
  refine Finset.mem_sdiff.mpr ⟨liftRowStart_mem htM, ?_⟩
  intro hhit
  obtain ⟨p, hp, htp⟩ := (mem_hitStarts.mp hhit).2
  exact htnot (mem_hitStarts.mpr ⟨htM, p, hp, shift_lift_mem_imp_shift_mem hM j t p htp⟩)

/-- The row assertion of manuscript `lem:repetition`, proved by an injection
of excluded starts. No normalization or closed-walk assumption is needed. -/
theorem defectCount_duplicateRow {M P : Diagram} (hM : IsFerrers M) (j : ℕ) :
    defectCount M P ≤ defectCount (duplicateRow M j) P := by
  rw [defectCount_eq_card_sdiff, defectCount_eq_card_sdiff]
  have hsub : (M \ hitStarts M P).image (liftRowStart M j) ⊆
      duplicateRow M j \ hitStarts (duplicateRow M j) P := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    exact lift_excluded_start hM j ht
  have hc := Finset.card_image_of_injective (M \ hitStarts M P) (liftRowStart_injective M j)
  exact hc ▸ Finset.card_le_card hsub

def transpose (M : Diagram) : Diagram := M.image Prod.swap

@[simp] theorem mem_transpose {M : Diagram} {p : Point} :
    p ∈ transpose M ↔ p.swap ∈ M := by
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    simpa using hq
  · intro hp
    exact Finset.mem_image.mpr ⟨p.swap, hp, by simp⟩

@[simp] theorem transpose_transpose (M : Diagram) : transpose (transpose M) = M := by
  ext p
  simp only [mem_transpose, Prod.swap_swap]

@[simp] theorem card_transpose (M : Diagram) : (transpose M).card = M.card := by
  exact Finset.card_image_of_injective M Prod.swap_injective

theorem transpose_isFerrers {M : Diagram} (hM : IsFerrers M) : IsFerrers (transpose M) := by
  intro p hp q hqx hqy
  rw [mem_transpose] at hp ⊢
  exact hM p.swap hp q.swap hqy hqx

theorem hitStarts_transpose (M P : Diagram) :
    hitStarts (transpose M) (transpose P) = transpose (hitStarts M P) := by
  ext t
  simp only [mem_hitStarts, mem_transpose]
  constructor
  · rintro ⟨ht, p, hp, htp⟩
    exact ⟨ht, p.swap, hp, htp⟩
  · rintro ⟨ht, p, hp, htp⟩
    exact ⟨ht, p.swap, by simpa using hp, htp⟩

@[simp] theorem defectCount_transpose (M P : Diagram) :
    defectCount (transpose M) (transpose P) = defectCount M P := by
  simp only [defectCount, hitStarts_transpose, card_transpose]

/-- Column duplication is row duplication after interchanging the axes. -/
def duplicateColumn (M : Diagram) (j : ℕ) : Diagram :=
  transpose (duplicateRow (transpose M) j)

theorem duplicateColumn_isFerrers {M : Diagram} (hM : IsFerrers M) (j : ℕ) :
    IsFerrers (duplicateColumn M j) :=
  transpose_isFerrers (duplicateRow_isFerrers (transpose_isFerrers hM) j)

/-- The column assertion of manuscript `lem:repetition`. -/
theorem defectCount_duplicateColumn {M P : Diagram} (hM : IsFerrers M) (j : ℕ) :
    defectCount M P ≤ defectCount (duplicateColumn M j) P := by
  have hb := defectCount_duplicateRow (P := transpose P) (transpose_isFerrers hM) j
  rw [defectCount_transpose] at hb
  have heq : defectCount (duplicateColumn M j) P =
      defectCount (duplicateRow (transpose M) j) (transpose P) := by
    simpa [duplicateColumn] using
      defectCount_transpose (duplicateRow (transpose M) j) (transpose P)
  rw [heq]
  exact hb

end SpanningTreeIsoperimetry.Ferrers
