module

public import SpanningTreeIsoperimetry.Repetition
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

/-!
# Closed lattice words and nonnegative corner-energy series

Words are actual sequences of the four nearest-neighbor lattice steps.
Their visited sets are translated by their coordinatewise minima before
the Ferrers defect count is evaluated. The infinite energy takes values in
`ℝ≥0∞`; finiteness is never implicit in this definition.
-/

namespace SpanningTreeIsoperimetry.CornerEnergy

open scoped BigOperators ENNReal
open Ferrers

abbrev Word (ℓ : ℕ) := Fin ℓ → Fin 4

def direction : Fin 4 → Vertex := ![(1, 0), (-1, 0), (0, 1), (0, -1)]

def position {ℓ : ℕ} (w : Word ℓ) (i : ℕ) : Vertex :=
  ∑ t : Fin ℓ, if t.val < i then direction (w t) else 0

@[simp] theorem position_zero {ℓ : ℕ} (w : Word ℓ) : position w 0 = 0 := by
  simp [position]

theorem position_succ {ℓ : ℕ} (w : Word ℓ) {i : ℕ} (hi : i < ℓ) :
    position w (i + 1) = position w i + direction (w ⟨i, hi⟩) := by
  have hsplit (t : Fin ℓ) :
      (if t.val < i + 1 then direction (w t) else 0) =
        (if t.val < i then direction (w t) else 0) +
          (if t = ⟨i, hi⟩ then direction (w t) else 0) := by
    by_cases ht : t.val < i
    · have hti : t.val < i + 1 := by omega
      have hne : t ≠ ⟨i, hi⟩ := by intro heq; subst t; exact (Nat.lt_irrefl i) ht
      simp [ht, hti, hne]
    · by_cases heq : t = ⟨i, hi⟩
      · subst t
        simp
      · have hti : ¬ t.val < i + 1 := by
          have hne : t.val ≠ i := fun h => heq (Fin.ext h)
          omega
        simp [ht, hti, heq]
  unfold position
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  simp

theorem direction_nearest (d : Fin 4) : lattice.Adj (0, 0) (direction d) := by
  fin_cases d <;> norm_num [lattice, direction]

theorem positions_adjacent {ℓ : ℕ} (w : Word ℓ) {i : ℕ} (hi : i < ℓ) :
    lattice.Adj (position w i) (position w (i + 1)) := by
  rw [position_succ w hi]
  simpa only [translate, add_zero, ← Prod.mk_add_mk, Prod.mk.eta] using
    (translate_adj (position w i) (0, 0) (direction (w ⟨i, hi⟩))).mpr
      (direction_nearest (w ⟨i, hi⟩))

def visited {ℓ : ℕ} (w : Word ℓ) : Finset Vertex :=
  (Finset.range (ℓ + 1)).image (position w)

theorem visited_nonempty {ℓ : ℕ} (w : Word ℓ) : (visited w).Nonempty := by
  refine ⟨0, Finset.mem_image.mpr ⟨0, ?_, position_zero w⟩⟩
  simp

abbrev ClosedWord (ℓ : ℕ) := {w : Word ℓ // position w ℓ = (0, 0)}

theorem closedWord_card_le (ℓ : ℕ) : Fintype.card (ClosedWord ℓ) ≤ 4 ^ ℓ := by
  calc
    Fintype.card (ClosedWord ℓ) ≤ Fintype.card (Word ℓ) := Fintype.card_subtype_le _
    _ = 4 ^ ℓ := by simp [Word]

def minimumX (V : Finset Vertex) (hV : V.Nonempty) : ℤ :=
  (V.image Prod.fst).min' (hV.image Prod.fst)

def minimumY (V : Finset Vertex) (hV : V.Nonempty) : ℤ :=
  (V.image Prod.snd).min' (hV.image Prod.snd)

def normalizePoint (V : Finset Vertex) (hV : V.Nonempty) (p : Vertex) : Point :=
  ((p.1 - minimumX V hV).toNat, (p.2 - minimumY V hV).toNat)

def normalizeVisited (V : Finset Vertex) (hV : V.Nonempty) : Diagram :=
  V.image (normalizePoint V hV)

theorem minimumX_le {V : Finset Vertex} (hV : V.Nonempty) {p : Vertex} (hp : p ∈ V) :
    minimumX V hV ≤ p.1 :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

theorem minimumY_le {V : Finset Vertex} (hV : V.Nonempty) {p : Vertex} (hp : p ∈ V) :
    minimumY V hV ≤ p.2 :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

/-- The natural coordinates are the exact translated integer coordinates;
`toNat` is not truncating any negative displacement. -/
theorem normalizePoint_cast {V : Finset Vertex} (hV : V.Nonempty) {p : Vertex}
    (hp : p ∈ V) :
    ((normalizePoint V hV p).1 : ℤ) = p.1 - minimumX V hV ∧
      ((normalizePoint V hV p).2 : ℤ) = p.2 - minimumY V hV := by
  exact ⟨Int.toNat_of_nonneg (sub_nonneg.mpr (minimumX_le hV hp)),
    Int.toNat_of_nonneg (sub_nonneg.mpr (minimumY_le hV hp))⟩

theorem normalizeVisited_isNormalized (V : Finset Vertex) (hV : V.Nonempty) :
    IsNormalized (normalizeVisited V hV) := by
  constructor
  · have hm := Finset.min'_mem (V.image Prod.fst) (hV.image Prod.fst)
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hm
    refine ⟨normalizePoint V hV p, Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
    dsimp [normalizePoint]
    change p.1 = minimumX V hV at hpx
    rw [hpx, sub_self]
    rfl
  · have hm := Finset.min'_mem (V.image Prod.snd) (hV.image Prod.snd)
    obtain ⟨p, hp, hpy⟩ := Finset.mem_image.mp hm
    refine ⟨normalizePoint V hV p, Finset.mem_image.mpr ⟨p, hp, rfl⟩, ?_⟩
    dsimp [normalizePoint]
    change p.2 = minimumY V hV at hpy
    rw [hpy, sub_self]
    rfl

def normalizedVisited {ℓ : ℕ} (w : Word ℓ) : Diagram :=
  normalizeVisited (visited w) (visited_nonempty w)

theorem normalizedVisited_isNormalized {ℓ : ℕ} (w : Word ℓ) :
    IsNormalized (normalizedVisited w) :=
  normalizeVisited_isNormalized (visited w) (visited_nonempty w)

/-- Sum over all rooted closed direction words of a fixed length. -/
def defectSum (M : Diagram) (ℓ : ℕ) : ℕ :=
  ∑ w : ClosedWord ℓ, defectCount M (normalizedVisited w.val)

@[simp] theorem defectSum_empty (ℓ : ℕ) : defectSum ∅ ℓ = 0 := by
  simp [defectSum, defectCount]

noncomputable def energyWeight (n : ℕ) : ℝ≥0∞ := (((n + 1) * 4 ^ (n + 1) : ℕ) : ℝ≥0∞)⁻¹

noncomputable def energyTerm (M : Diagram) (n : ℕ) : ℝ≥0∞ := energyWeight n * defectSum M (n + 1)

noncomputable def partialEnergy (M : Diagram) (L : ℕ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range L, energyTerm M n

noncomputable def energy (M : Diagram) : ℝ≥0∞ := ∑' n : ℕ, energyTerm M n

@[simp] theorem energy_empty : energy ∅ = 0 := by
  simp [energy, energyTerm]

@[simp] theorem energy_strip_zero : energy (horizontalStrip 0) = 0 := by
  simp [horizontalStrip]

theorem energyWeight_ne_top (n : ℕ) : energyWeight n ≠ ⊤ := by
  simp [energyWeight]

theorem energyTerm_ne_top (M : Diagram) (n : ℕ) : energyTerm M n ≠ ⊤ := by
  exact ENNReal.mul_ne_top (energyWeight_ne_top n) (by simp)

theorem partialEnergy_ne_top (M : Diagram) (L : ℕ) : partialEnergy M L ≠ ⊤ := by
  exact ENNReal.sum_ne_top.mpr (fun n _ => energyTerm_ne_top M n)

theorem partialEnergy_le_energy (M : Diagram) (L : ℕ) : partialEnergy M L ≤ energy M :=
  ENNReal.sum_le_tsum (Finset.range L)

theorem energy_eq_iSup_partial (M : Diagram) : energy M = ⨆ L : ℕ, partialEnergy M L :=
  ENNReal.tsum_eq_iSup_nat

theorem partialEnergy_monotone (M : Diagram) : Monotone (partialEnergy M) := by
  intro L K hLK
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hLK) (fun _ _ _ => zero_le)

noncomputable def partialRealEnergy (M : Diagram) (L : ℕ) : ℝ := (partialEnergy M L).toReal

theorem partialRealEnergy_eq (M : Diagram) (L : ℕ) :
    partialRealEnergy M L = ∑ n ∈ Finset.range L,
      (defectSum M (n + 1) : ℝ) / ((n + 1) * 4 ^ (n + 1)) := by
  rw [partialRealEnergy, partialEnergy, ENNReal.toReal_sum (fun n _ => energyTerm_ne_top M n)]
  apply Finset.sum_congr rfl
  intro n _
  simp [energyTerm, energyWeight, ENNReal.toReal_add, div_eq_mul_inv, mul_comm]

theorem defectSum_duplicateRow {M : Diagram} (hM : IsFerrers M) (j ℓ : ℕ) :
    defectSum M ℓ ≤ defectSum (duplicateRow M j) ℓ :=
  Finset.sum_le_sum (fun _ _ => defectCount_duplicateRow hM j)

theorem defectSum_duplicateColumn {M : Diagram} (hM : IsFerrers M) (j ℓ : ℕ) :
    defectSum M ℓ ≤ defectSum (duplicateColumn M j) ℓ :=
  Finset.sum_le_sum (fun _ _ => defectCount_duplicateColumn hM j)

theorem defectSum_maximalCells (M : Diagram) (ℓ : ℕ) :
    (maximalCells M).card * defectSum {(0, 0)} ℓ ≤ defectSum M ℓ := by
  have hword (w : ClosedWord ℓ) :
      (maximalCells M).card * defectCount {(0, 0)} (normalizedVisited w.val) ≤
        defectCount M (normalizedVisited w.val) := by
    by_cases h0 : (0, 0) ∈ normalizedVisited w.val
    · simp [defectCount_eq_zero_of_origin_mem h0]
    · rw [defectCount_singleton_of_origin_not_mem h0, mul_one]
      exact maximalCells_card_le_defectCount h0
  simpa only [defectSum, Finset.mul_sum] using Finset.sum_le_sum (fun w _ => hword w)

theorem defectSum_threeCell {M : Diagram} (hM : IsFerrers M) (hne : M.Nonempty)
    (hrect : ¬IsRectangle M) (ℓ : ℕ) :
    defectSum threeCell ℓ + ((maximalCells M).card - 2) * defectSum {(0, 0)} ℓ ≤
      defectSum M ℓ := by
  simpa only [defectSum, Finset.sum_add_distrib, Finset.mul_sum] using
    Finset.sum_le_sum (s := (Finset.univ : Finset (ClosedWord ℓ)))
      (fun _ _ => three_cell_obstruction hM hne hrect)

theorem defectSum_strip_monotone (ℓ : ℕ) :
    Monotone (fun k => defectSum (horizontalStrip k) ℓ) := by
  intro j k hjk
  exact Finset.sum_le_sum
    (fun w _ => strip_defect_monotone (normalizedVisited_isNormalized w.val) hjk)

theorem defectSum_strip_concave (k ℓ : ℕ) :
    defectSum (horizontalStrip (k + 2)) ℓ + defectSum (horizontalStrip k) ℓ ≤
      2 * defectSum (horizontalStrip (k + 1)) ℓ := by
  simpa only [defectSum, Finset.sum_add_distrib, Finset.mul_sum] using
    Finset.sum_le_sum (s := (Finset.univ : Finset (ClosedWord ℓ)))
      (fun w _ => strip_defect_concave (normalizedVisited_isNormalized w.val) k)

theorem defectSum_strip_concentration {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (ℓ : ℕ) :
    2 * defectSum (horizontalStrip 1) ℓ + defectSum (horizontalStrip (a + b)) ℓ ≤
      defectSum (horizontalStrip a) ℓ + defectSum (horizontalStrip b) ℓ +
        defectSum (horizontalStrip 2) ℓ := by
  simpa only [defectSum, Finset.sum_add_distrib, Finset.mul_sum] using
    Finset.sum_le_sum (s := (Finset.univ : Finset (ClosedWord ℓ)))
      (fun w _ => strip_defect_concentration (normalizedVisited_isNormalized w.val) ha hb)

theorem energyTerm_mono {A B : Diagram} (h : ∀ ℓ, defectSum A ℓ ≤ defectSum B ℓ) (n : ℕ) :
    energyTerm A n ≤ energyTerm B n := by
  apply mul_le_mul_right
  exact_mod_cast h (n + 1)

theorem energy_mono_of_defectSum_le {A B : Diagram}
    (h : ∀ ℓ, defectSum A ℓ ≤ defectSum B ℓ) : energy A ≤ energy B :=
  ENNReal.tsum_le_tsum (energyTerm_mono h)

theorem partialEnergy_mono_of_defectSum_le {A B : Diagram}
    (h : ∀ ℓ, defectSum A ℓ ≤ defectSum B ℓ) (L : ℕ) : partialEnergy A L ≤ partialEnergy B L :=
  Finset.sum_le_sum (fun n _ => energyTerm_mono h n)

private theorem term_linear_combination (a b : ℕ) (A B : Diagram) (n : ℕ) :
    energyWeight n * (↑(a * defectSum A (n + 1) + b * defectSum B (n + 1)) : ℝ≥0∞) =
      a * energyTerm A n + b * energyTerm B n := by
  simp only [Nat.cast_add, Nat.cast_mul, energyTerm]
  ring

theorem energyTerm_linear_le (a b c d : ℕ) (A B C D : Diagram)
    (h : ∀ ℓ, a * defectSum A ℓ + b * defectSum B ℓ ≤ c * defectSum C ℓ + d * defectSum D ℓ)
    (n : ℕ) : a * energyTerm A n + b * energyTerm B n ≤
      c * energyTerm C n + d * energyTerm D n := by
  rw [← term_linear_combination, ← term_linear_combination]
  apply mul_le_mul_right
  exact_mod_cast h (n + 1)

/-- Nonnegative sums preserve the coefficient comparisons even before
finiteness of the full corner energy has been established. -/
theorem energy_linear_le (a b c d : ℕ) (A B C D : Diagram)
    (h : ∀ ℓ, a * defectSum A ℓ + b * defectSum B ℓ ≤ c * defectSum C ℓ + d * defectSum D ℓ) :
    a * energy A + b * energy B ≤ c * energy C + d * energy D := by
  have hb := ENNReal.tsum_le_tsum (energyTerm_linear_le a b c d A B C D h)
  simpa only [ENNReal.tsum_add, ENNReal.tsum_mul_left, energy] using hb

theorem partialEnergy_linear_le (a b c d : ℕ) (A B C D : Diagram)
    (h : ∀ ℓ, a * defectSum A ℓ + b * defectSum B ℓ ≤ c * defectSum C ℓ + d * defectSum D ℓ)
    (L : ℕ) : a * partialEnergy A L + b * partialEnergy B L ≤
      c * partialEnergy C L + d * partialEnergy D L := by
  have hb := Finset.sum_le_sum (s := Finset.range L)
    (fun n _ => energyTerm_linear_le a b c d A B C D h n)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, partialEnergy] using hb

theorem energy_duplicateRow {M : Diagram} (hM : IsFerrers M) (j : ℕ) :
    energy M ≤ energy (duplicateRow M j) :=
  energy_mono_of_defectSum_le (defectSum_duplicateRow hM j)

theorem energy_duplicateColumn {M : Diagram} (hM : IsFerrers M) (j : ℕ) :
    energy M ≤ energy (duplicateColumn M j) :=
  energy_mono_of_defectSum_le (defectSum_duplicateColumn hM j)

theorem energy_maximalCells (M : Diagram) :
    (maximalCells M).card * energy {(0, 0)} ≤ energy M := by
  simpa using energy_linear_le (maximalCells M).card 0 1 0 {(0, 0)} M M M
    (by intro ℓ; simpa using defectSum_maximalCells M ℓ)

theorem energy_threeCell {M : Diagram} (hM : IsFerrers M) (hne : M.Nonempty)
    (hrect : ¬IsRectangle M) :
    energy threeCell + ((maximalCells M).card - 2 : ℕ) * energy {(0, 0)} ≤ energy M := by
  simpa using energy_linear_le 1 ((maximalCells M).card - 2) 1 0
    threeCell {(0, 0)} M M (by intro ℓ; simpa using defectSum_threeCell hM hne hrect ℓ)

theorem energy_strip_monotone : Monotone (fun k => energy (horizontalStrip k)) := by
  intro j k hjk
  exact energy_mono_of_defectSum_le (fun ℓ => defectSum_strip_monotone ℓ hjk)

theorem energy_strip_concave (k : ℕ) :
    energy (horizontalStrip (k + 2)) + energy (horizontalStrip k) ≤
      2 * energy (horizontalStrip (k + 1)) := by
  simpa using energy_linear_le 1 1 2 0 (horizontalStrip (k + 2)) (horizontalStrip k)
    (horizontalStrip (k + 1)) ∅ (by intro ℓ; simpa using defectSum_strip_concave k ℓ)

theorem partialEnergy_duplicateRow {M : Diagram} (hM : IsFerrers M) (j L : ℕ) :
    partialEnergy M L ≤ partialEnergy (duplicateRow M j) L :=
  partialEnergy_mono_of_defectSum_le (defectSum_duplicateRow hM j) L

theorem partialEnergy_duplicateColumn {M : Diagram} (hM : IsFerrers M) (j L : ℕ) :
    partialEnergy M L ≤ partialEnergy (duplicateColumn M j) L :=
  partialEnergy_mono_of_defectSum_le (defectSum_duplicateColumn hM j) L

theorem partialEnergy_threeCell {M : Diagram} (hM : IsFerrers M) (hne : M.Nonempty)
    (hrect : ¬IsRectangle M) (L : ℕ) :
    partialEnergy threeCell L + ((maximalCells M).card - 2 : ℕ) * partialEnergy {(0, 0)} L ≤
      partialEnergy M L := by
  simpa using partialEnergy_linear_le 1 ((maximalCells M).card - 2) 1 0
    threeCell {(0, 0)} M M (by intro ℓ; simpa using defectSum_threeCell hM hne hrect ℓ) L

theorem partialEnergy_strip_concave (k L : ℕ) :
    partialEnergy (horizontalStrip (k + 2)) L + partialEnergy (horizontalStrip k) L ≤
      2 * partialEnergy (horizontalStrip (k + 1)) L := by
  simpa using partialEnergy_linear_le 1 1 2 0 (horizontalStrip (k + 2)) (horizontalStrip k)
    (horizontalStrip (k + 1)) ∅ (by intro ℓ; simpa using defectSum_strip_concave k ℓ) L

theorem partialRealEnergy_duplicateRow {M : Diagram} (hM : IsFerrers M) (j L : ℕ) :
    partialRealEnergy M L ≤ partialRealEnergy (duplicateRow M j) L :=
  (ENNReal.toReal_le_toReal (partialEnergy_ne_top M L)
    (partialEnergy_ne_top (duplicateRow M j) L)).mpr (partialEnergy_duplicateRow hM j L)

theorem partialRealEnergy_strip_concave (k L : ℕ) :
    partialRealEnergy (horizontalStrip (k + 2)) L + partialRealEnergy (horizontalStrip k) L ≤
      2 * partialRealEnergy (horizontalStrip (k + 1)) L := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by norm_num) (partialEnergy_ne_top (horizontalStrip (k + 1)) L))
    (partialEnergy_strip_concave k L)
  simpa only [ENNReal.toReal_add (partialEnergy_ne_top _ _) (partialEnergy_ne_top _ _),
    ENNReal.toReal_mul, ENNReal.toReal_ofNat, partialRealEnergy] using h

theorem partialRealEnergy_threeCell {M : Diagram} (hM : IsFerrers M) (hne : M.Nonempty)
    (hrect : ¬IsRectangle M) (L : ℕ) :
    partialRealEnergy threeCell L + ((maximalCells M).card - 2 : ℕ) *
      partialRealEnergy {(0, 0)} L ≤ partialRealEnergy M L := by
  have h := ENNReal.toReal_mono (partialEnergy_ne_top M L) (partialEnergy_threeCell hM hne hrect L)
  have hprod : (↑((maximalCells M).card - 2) : ℝ≥0∞) * partialEnergy {(0, 0)} L ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (partialEnergy_ne_top {(0, 0)} L)
  rw [ENNReal.toReal_add (partialEnergy_ne_top threeCell L) hprod] at h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, partialRealEnergy] using h

theorem energyTerm_strip_concentration {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (n : ℕ) :
    2 * energyTerm (horizontalStrip 1) n + energyTerm (horizontalStrip (a + b)) n ≤
      energyTerm (horizontalStrip a) n + energyTerm (horizontalStrip b) n +
        energyTerm (horizontalStrip 2) n := by
  have hc : (↑(2 * defectSum (horizontalStrip 1) (n + 1) +
      defectSum (horizontalStrip (a + b)) (n + 1)) : ℝ≥0∞) ≤
      ↑(defectSum (horizontalStrip a) (n + 1) + defectSum (horizontalStrip b) (n + 1) +
        defectSum (horizontalStrip 2) (n + 1)) := by
    exact_mod_cast defectSum_strip_concentration ha hb (n + 1)
  have ht := mul_le_mul_right hc (energyWeight n)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, mul_add] at ht
  convert ht using 1
  all_goals simp only [energyTerm]
  all_goals ring

/-- The non-subtractive form remains meaningful even when finiteness of
the critical corner-energy series is not yet known. -/
theorem energy_strip_concentration {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    2 * energy (horizontalStrip 1) + energy (horizontalStrip (a + b)) ≤
      energy (horizontalStrip a) + energy (horizontalStrip b) + energy (horizontalStrip 2) := by
  have h := ENNReal.tsum_le_tsum (energyTerm_strip_concentration ha hb)
  simpa only [ENNReal.tsum_add, ENNReal.tsum_mul_left, energy] using h

theorem partialEnergy_strip_concentration {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (L : ℕ) :
    2 * partialEnergy (horizontalStrip 1) L + partialEnergy (horizontalStrip (a + b)) L ≤
      partialEnergy (horizontalStrip a) L + partialEnergy (horizontalStrip b) L +
        partialEnergy (horizontalStrip 2) L := by
  have h := Finset.sum_le_sum (s := Finset.range L)
    (fun n _ => energyTerm_strip_concentration ha hb n)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, partialEnergy] using h

end SpanningTreeIsoperimetry.CornerEnergy
