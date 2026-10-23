module

public import SpanningTreeIsoperimetry.Grid
public import Mathlib.Order.Preorder.Finite

@[expose] public section

/-!
# Wordwise corner-defect comparisons

The visited points of a normalized lattice word lie in `ℕ × ℕ`.  The
combinatorial comparisons below hold for arbitrary finite visited sets, so
they do not need the closed-walk or nearest-neighbor restrictions.
-/

namespace SpanningTreeIsoperimetry.Ferrers

abbrev Point := ℕ × ℕ
abbrev Diagram := Finset Point

def shift (t p : Point) : Point := (t.1 + p.1, t.2 + p.2)

/-- Translation starts whose translated visited set meets the diagram. -/
def hitStarts (M P : Diagram) : Diagram :=
  M.filter (fun t => ∃ p ∈ P, shift t p ∈ M)

@[simp] theorem mem_hitStarts {M P : Diagram} {t : Point} :
    t ∈ hitStarts M P ↔ t ∈ M ∧ ∃ p ∈ P, shift t p ∈ M :=
  Finset.mem_filter

theorem hitStarts_subset (M P : Diagram) : hitStarts M P ⊆ M :=
  Finset.filter_subset _ _

/-- The lower-ideal property makes the restriction `t ∈ M` redundant. Thus
`hitStarts` is exactly the set counted in the manuscript. -/
theorem mem_hitStarts_iff {M P : Diagram} (hM : IsFerrers M) (t : Point) :
    t ∈ hitStarts M P ↔ ∃ p ∈ P, shift t p ∈ M := by
  constructor
  · exact fun h => (mem_hitStarts.mp h).2
  · rintro ⟨p, hp, htp⟩
    refine mem_hitStarts.mpr ⟨?_, p, hp, htp⟩
    exact hM (shift t p) htp t (Nat.le_add_right _ _) (Nat.le_add_right _ _)

/-- Number of starts in the defect that fail to hit it. -/
def defectCount (M P : Diagram) : ℕ := M.card - (hitStarts M P).card

theorem defectCount_eq_card_sdiff (M P : Diagram) :
    defectCount M P = (M \ hitStarts M P).card := by
  rw [Finset.card_sdiff_of_subset (hitStarts_subset M P)]
  rfl

theorem defectCount_le_card (M P : Diagram) : defectCount M P ≤ M.card :=
  Nat.sub_le _ _

theorem hitStarts_eq_of_origin_mem {M P : Diagram} (h0 : (0, 0) ∈ P) :
    hitStarts M P = M := by
  apply Finset.Subset.antisymm (hitStarts_subset M P)
  intro t ht
  refine mem_hitStarts.mpr ⟨ht, (0, 0), h0, ?_⟩
  simpa [shift] using ht

theorem defectCount_eq_zero_of_origin_mem {M P : Diagram} (h0 : (0, 0) ∈ P) :
    defectCount M P = 0 := by
  simp [defectCount, hitStarts_eq_of_origin_mem h0]

/-- Coordinatewise maximal cells of a finite diagram. -/
def maximalCells (M : Diagram) : Diagram :=
  M.filter (fun m => ∀ q ∈ M, m.1 ≤ q.1 → m.2 ≤ q.2 → q = m)

@[simp] theorem mem_maximalCells {M : Diagram} {m : Point} :
    m ∈ maximalCells M ↔ m ∈ M ∧
      ∀ q ∈ M, m.1 ≤ q.1 → m.2 ≤ q.2 → q = m :=
  Finset.mem_filter

theorem maximal_not_hit {M P : Diagram} (h0 : (0, 0) ∉ P)
    {m : Point} (hm : m ∈ maximalCells M) : m ∉ hitStarts M P := by
  intro hhit
  obtain ⟨p, hp, hmp⟩ := (mem_hitStarts.mp hhit).2
  have heq : shift m p = m :=
    (mem_maximalCells.mp hm).2 _ hmp (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  dsimp [shift] at hx hy
  have hp0 : p = (0, 0) := Prod.ext (by omega) (by omega)
  exact h0 (hp0 ▸ hp)

theorem maximalCells_subset_sdiff {M P : Diagram} (h0 : (0, 0) ∉ P) :
    maximalCells M ⊆ M \ hitStarts M P := by
  intro m hm
  exact Finset.mem_sdiff.mpr ⟨(mem_maximalCells.mp hm).1, maximal_not_hit h0 hm⟩

/-- Manuscript `lem:maximal-cells`. This holds for every finite diagram; the
lower-ideal hypothesis is only needed for the interpretation of `hitStarts`. -/
theorem maximalCells_card_le_defectCount {M P : Diagram} (h0 : (0, 0) ∉ P) :
    (maximalCells M).card ≤ defectCount M P := by
  rw [defectCount_eq_card_sdiff]
  exact Finset.card_le_card (maximalCells_subset_sdiff h0)

/-- The horizontal corner strip `Iₖ`. -/
def horizontalStrip (k : ℕ) : Diagram := Finset.range k ×ˢ {(0 : ℕ)}

@[simp] theorem mem_horizontalStrip {k : ℕ} {p : Point} :
    p ∈ horizontalStrip k ↔ p.1 < k ∧ p.2 = 0 := by
  simp only [horizontalStrip, Finset.mem_product, Finset.mem_range, Finset.mem_singleton]

@[simp] theorem card_horizontalStrip (k : ℕ) : (horizontalStrip k).card = k := by
  simp [horizontalStrip]

theorem horizontalStrip_isFerrers (k : ℕ) : IsFerrers (horizontalStrip k) := by
  intro p hp q hqx hqy
  rw [mem_horizontalStrip] at hp ⊢
  exact ⟨lt_of_le_of_lt hqx hp.1, by omega⟩

/-- Translation starts for a strip form a shorter strip. Here `a` is exactly
the least abscissa of a visited point on the horizontal axis. -/
theorem hitStarts_horizontalStrip {P : Diagram} {a : ℕ}
    (ha : (a, 0) ∈ P)
    (ha_min : ∀ p ∈ P, p.2 = 0 → a ≤ p.1) (k : ℕ) :
    hitStarts (horizontalStrip k) P = horizontalStrip (k - a) := by
  ext t
  constructor
  · intro ht
    obtain ⟨htM, p, hp, htp⟩ := mem_hitStarts.mp ht
    rw [mem_horizontalStrip] at htM htp ⊢
    have hpy : p.2 = 0 := by
      dsimp [shift] at htp
      omega
    have hap := ha_min p hp hpy
    dsimp [shift] at htp
    exact ⟨by omega, htM.2⟩
  · intro ht
    rw [mem_horizontalStrip] at ht
    refine mem_hitStarts.mpr ⟨?_, (a, 0), ha, ?_⟩
    · exact mem_horizontalStrip.mpr ⟨by omega, ht.2⟩
    · apply mem_horizontalStrip.mpr
      dsimp [shift]
      exact ⟨by omega, by simpa using ht.2⟩

/-- The wordwise strip formula in Section 4.3. -/
theorem defectCount_horizontalStrip {P : Diagram} {a : ℕ}
    (ha : (a, 0) ∈ P)
    (ha_min : ∀ p ∈ P, p.2 = 0 → a ≤ p.1) (k : ℕ) :
    defectCount (horizontalStrip k) P = min k a := by
  rw [defectCount, hitStarts_horizontalStrip ha ha_min, card_horizontalStrip,
    card_horizontalStrip]
  omega

/-- Coordinatewise normalization means that each coordinate attains zero;
the origin itself need not be visited. -/
def IsNormalized (P : Diagram) : Prop :=
  (∃ p ∈ P, p.1 = 0) ∧ (∃ p ∈ P, p.2 = 0)

def axisAbscissae (P : Diagram) : Finset ℕ :=
  (P.filter (fun p => p.2 = 0)).image Prod.fst

theorem axisAbscissae_nonempty {P : Diagram} (hP : IsNormalized P) :
    (axisAbscissae P).Nonempty := by
  obtain ⟨p, hp, hp0⟩ := hP.2
  exact ⟨p.1, Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hp0⟩, rfl⟩⟩

def firstAxisX (P : Diagram) (hP : IsNormalized P) : ℕ :=
  (axisAbscissae P).min' (axisAbscissae_nonempty hP)

theorem firstAxisX_mem {P : Diagram} (hP : IsNormalized P) :
    (firstAxisX P hP, 0) ∈ P := by
  have hmem := Finset.min'_mem (axisAbscissae P) (axisAbscissae_nonempty hP)
  obtain ⟨p, hp, hx⟩ := Finset.mem_image.mp hmem
  obtain ⟨hpP, hp0⟩ := Finset.mem_filter.mp hp
  have heq : p = (firstAxisX P hP, 0) := Prod.ext hx hp0
  exact heq ▸ hpP

theorem firstAxisX_le {P : Diagram} (hP : IsNormalized P) {p : Point}
    (hp : p ∈ P) (hp0 : p.2 = 0) : firstAxisX P hP ≤ p.1 := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hp0⟩, rfl⟩

theorem normalized_defectCount_horizontalStrip {P : Diagram}
    (hP : IsNormalized P) (k : ℕ) :
    defectCount (horizontalStrip k) P = min k (firstAxisX P hP) :=
  defectCount_horizontalStrip (firstAxisX_mem hP) (fun _ hp hp0 => firstAxisX_le hP hp hp0) k

theorem strip_defect_monotone {P : Diagram} (hP : IsNormalized P) :
    Monotone (fun k => defectCount (horizontalStrip k) P) := by
  intro j k hjk
  simp only [normalized_defectCount_horizontalStrip hP]
  omega

/-- The wordwise discrete concavity that precedes the energy comparison. -/
theorem strip_defect_concave {P : Diagram} (hP : IsNormalized P) (k : ℕ) :
    defectCount (horizontalStrip (k + 2)) P + defectCount (horizontalStrip k) P ≤
      2 * defectCount (horizontalStrip (k + 1)) P := by
  simp only [normalized_defectCount_horizontalStrip hP]
  omega

/-- The wordwise version of the quantitative two-strip concentration gap. -/
theorem strip_defect_concentration {P : Diagram} (hP : IsNormalized P)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    2 * defectCount (horizontalStrip 1) P + defectCount (horizontalStrip (a + b)) P ≤
      defectCount (horizontalStrip a) P + defectCount (horizontalStrip b) P +
        defectCount (horizontalStrip 2) P := by
  simp only [normalized_defectCount_horizontalStrip hP]
  omega

theorem exists_dominating_maximal {M : Diagram} {p : Point} (hp : p ∈ M) :
    ∃ m ∈ maximalCells M, p.1 ≤ m.1 ∧ p.2 ≤ m.2 := by
  obtain ⟨m, hpm, hm⟩ := M.exists_le_maximal hp
  refine ⟨m, mem_maximalCells.mpr ⟨hm.1, ?_⟩, hpm.1, hpm.2⟩
  intro q hq hx hy
  exact le_antisymm (hm.2 hq ⟨hx, hy⟩) ⟨hx, hy⟩

def IsRectangle (M : Diagram) : Prop :=
  ∃ r s : ℕ, M = Finset.range r ×ˢ Finset.range s

/-- A finite nonempty lower ideal with at most one maximal cell is a rectangle. -/
theorem isRectangle_of_maximal_card_le_one {M : Diagram}
    (hM : IsFerrers M) (hne : M.Nonempty) (hcard : (maximalCells M).card ≤ 1) :
    IsRectangle M := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨m, hm, _⟩ := exists_dominating_maximal hp
  refine ⟨m.1 + 1, m.2 + 1, ?_⟩
  ext q
  simp only [Finset.mem_product, Finset.mem_range]
  constructor
  · intro hq
    obtain ⟨n, hn, hqn⟩ := exists_dominating_maximal hq
    have heq := Finset.card_le_one.mp hcard n hn m hm
    subst n
    exact ⟨by omega, by omega⟩
  · rintro ⟨hx, hy⟩
    exact hM m (mem_maximalCells.mp hm).1 q (by omega) (by omega)

theorem two_le_maximal_card_of_nonrectangle {M : Diagram}
    (hM : IsFerrers M) (hne : M.Nonempty) (hrect : ¬IsRectangle M) :
    2 ≤ (maximalCells M).card := by
  by_contra h
  exact hrect (isRectangle_of_maximal_card_le_one hM hne (by omega))

/-- A nonmaximal cell above `t` exists whenever a translate advances by at
least two coordinate steps and still lies in the lower ideal. -/
theorem exists_nonmaximal_above {M : Diagram} (hM : IsFerrers M) {t p : Point}
    (hmem : shift t p ∈ M) (hp : 2 ≤ p.1 + p.2) :
    ∃ u ∈ M \ maximalCells M, t.1 + t.2 < u.1 + u.2 := by
  by_cases hx : 0 < p.1
  · let u : Point := (t.1 + 1, t.2)
    have hu : u ∈ M := hM (shift t p) hmem u (by dsimp [u, shift]; omega)
      (by dsimp [u, shift]; omega)
    have hnot : u ∉ maximalCells M := by
      intro hmax
      have heq := (mem_maximalCells.mp hmax).2 (shift t p) hmem
        (by dsimp [u, shift]; omega) (by dsimp [u, shift]; omega)
      have h₁ := congrArg Prod.fst heq
      have h₂ := congrArg Prod.snd heq
      dsimp [u, shift] at h₁ h₂
      omega
    exact ⟨u, Finset.mem_sdiff.mpr ⟨hu, hnot⟩, by dsimp [u]; omega⟩
  · let u : Point := (t.1, t.2 + 1)
    have hu : u ∈ M := hM (shift t p) hmem u (by dsimp [u, shift]; omega)
      (by dsimp [u, shift]; omega)
    have hnot : u ∉ maximalCells M := by
      intro hmax
      have heq := (mem_maximalCells.mp hmax).2 (shift t p) hmem
        (by dsimp [u, shift]; omega) (by dsimp [u, shift]; omega)
      have h₁ := congrArg Prod.fst heq
      have h₂ := congrArg Prod.snd heq
      dsimp [u, shift] at h₁ h₂
      omega
    exact ⟨u, Finset.mem_sdiff.mpr ⟨hu, hnot⟩, by dsimp [u]; omega⟩

theorem nonmaximal_nonempty {M : Diagram} (hM : IsFerrers M) (hne : M.Nonempty)
    (hcard : 2 ≤ (maximalCells M).card) : (M \ maximalCells M).Nonempty := by
  obtain ⟨p, hp⟩ := hne
  have hzero : (0, 0) ∈ M := hM p hp (0, 0) (Nat.zero_le _) (Nat.zero_le _)
  refine ⟨(0, 0), Finset.mem_sdiff.mpr ⟨hzero, ?_⟩⟩
  intro hmax
  have hsub : maximalCells M ⊆ {(0, 0)} := by
    intro q hq
    apply Finset.mem_singleton.mpr
    exact (mem_maximalCells.mp hmax).2 q (mem_maximalCells.mp hq).1
      (Nat.zero_le _) (Nat.zero_le _)
  have hb := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at hb
  omega

theorem maximal_card_add_one_le_defectCount {M P : Diagram}
    (hM : IsFerrers M) (hne : M.Nonempty) (hcard : 2 ≤ (maximalCells M).card)
    (h0 : (0, 0) ∉ P) (hE : (1, 0) ∉ P) (hN : (0, 1) ∉ P) :
    (maximalCells M).card + 1 ≤ defectCount M P := by
  obtain ⟨t, ht, hscore⟩ := (M \ maximalCells M).exists_max_image
    (fun u : Point => u.1 + u.2) (nonmaximal_nonempty hM hne hcard)
  have htM := (Finset.mem_sdiff.mp ht).1
  have htnotmax := (Finset.mem_sdiff.mp ht).2
  have htnothit : t ∉ hitStarts M P := by
    intro hhit
    obtain ⟨p, hp, htp⟩ := (mem_hitStarts.mp hhit).2
    have hpweight : 2 ≤ p.1 + p.2 := by
      by_contra h
      have hcases : p = (0, 0) ∨ p = (1, 0) ∨ p = (0, 1) := by
        rcases p with ⟨x, y⟩
        simp only [Prod.mk.injEq]
        dsimp at h
        omega
      rcases hcases with rfl | rfl | rfl
      · exact h0 hp
      · exact hE hp
      · exact hN hp
    obtain ⟨u, hu, htu⟩ := exists_nonmaximal_above hM htp hpweight
    exact (not_lt_of_ge (hscore u hu)) htu
  have hsub : insert t (maximalCells M) ⊆ M \ hitStarts M P := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact Finset.mem_sdiff.mpr ⟨htM, htnothit⟩
    · exact maximalCells_subset_sdiff h0 hu
  have hb := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem htnotmax, ← defectCount_eq_card_sdiff] at hb
  exact hb

def threeCell : Diagram := {(0, 0), (1, 0), (0, 1)}

@[simp] theorem card_threeCell : threeCell.card = 3 := by decide

theorem defectCount_threeCell_le_two {P : Diagram}
    (haxis : (1, 0) ∈ P ∨ (0, 1) ∈ P) : defectCount threeCell P ≤ 2 := by
  have hzero : (0, 0) ∈ hitStarts threeCell P := by
    refine mem_hitStarts.mpr ⟨by decide, ?_⟩
    rcases haxis with hE | hN
    · exact ⟨(1, 0), hE, by decide⟩
    · exact ⟨(0, 1), hN, by decide⟩
  have hpos := Finset.card_pos.mpr ⟨(0, 0), hzero⟩
  unfold defectCount
  rw [card_threeCell]
  omega

theorem defectCount_singleton_of_origin_not_mem {P : Diagram} (h0 : (0, 0) ∉ P) :
    defectCount {(0, 0)} P = 1 := by
  have hmax : (maximalCells {(0, 0)}).card = 1 := by decide
  have hlo := maximalCells_card_le_defectCount (M := {(0, 0)}) h0
  have hhi := defectCount_le_card {(0, 0)} P
  simp only [hmax, Finset.card_singleton] at hlo hhi
  omega

/-- The coefficientwise assertion of manuscript `lem:three-cell-obstruction`.
Its subsequent energy inequality requires summing the closed-word weights. -/
theorem three_cell_obstruction {M P : Diagram} (hM : IsFerrers M)
    (hne : M.Nonempty) (hrect : ¬IsRectangle M) :
    defectCount threeCell P + ((maximalCells M).card - 2) * defectCount {(0, 0)} P ≤
      defectCount M P := by
  have ha := two_le_maximal_card_of_nonrectangle hM hne hrect
  by_cases h0 : (0, 0) ∈ P
  · simp only [defectCount_eq_zero_of_origin_mem h0, mul_zero, add_zero, le_refl]
  · rw [defectCount_singleton_of_origin_not_mem h0, mul_one]
    by_cases haxis : (1, 0) ∈ P ∨ (0, 1) ∈ P
    · have hL := defectCount_threeCell_le_two haxis
      have hmax := maximalCells_card_le_defectCount (M := M) h0
      omega
    · have hE : (1, 0) ∉ P := fun h => haxis (Or.inl h)
      have hN : (0, 1) ∉ P := fun h => haxis (Or.inr h)
      have hL := defectCount_le_card threeCell P
      rw [card_threeCell] at hL
      have hmax := maximal_card_add_one_le_defectCount hM hne ha h0 hE hN
      omega

end SpanningTreeIsoperimetry.Ferrers
