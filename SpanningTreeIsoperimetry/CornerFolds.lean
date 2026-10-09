import SpanningTreeIsoperimetry.StripPolarization
import SpanningTreeIsoperimetry.DomainIsometries
import SpanningTreeIsoperimetry.Repetition

/-! Concrete corner separation and diagonal folds on integer face domains. -/
namespace SpanningTreeIsoperimetry.CornerFolds

open Polarization StripPolarization Ferrers DomainIsometries
open scoped Classical

/-- Integer-coordinate lower closure in a fixed vertical column. -/
def ColumnLower (M : Domain) : Prop :=
  ∀ x y z : ℤ, (x, y) ∈ M → 0 ≤ z → z ≤ y → (x, z) ∈ M

/-- No column contains cells from both defects. -/
def ColumnDisjoint (L R : Domain) : Prop :=
  ∀ x y z : ℤ, (x, y) ∈ L → (x, z) ∉ R

def adjacentColumnFaces (u v : ℕ) (L R : Domain) : Domain := rectangle u v \ (L ∪ R)

def oppositeColumnFaces (u v : ℕ) (L R : Domain) : Domain :=
  rectangle u v \ (L ∪ R.image (axialReflection ((v : ℤ) - 1)))

theorem mem_image_involution {M : Domain} {f : Vertex → Vertex}
    (hf : Function.Involutive f) (x : Vertex) : x ∈ M.image f ↔ f x ∈ M := by
  constructor
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa only [hf y] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨f x, hx, hf x⟩

theorem axial_mem_rectangle (u v : ℕ) (x : Vertex) :
    axialReflection ((v : ℤ) - 1) x ∈ rectangle u v ↔ x ∈ rectangle u v := by
  simp only [mem_rectangle, axialReflection]
  omega

private theorem upper_column_logic (A B C D : Prop) (hAC : A → C) (hBD : B → D)
    (hCD : C → ¬D) : (¬(A ∨ D) ∨ ¬(C ∨ B)) ↔ ¬(A ∨ B) := by
  tauto

private theorem lower_column_logic (A B C D : Prop) (hCA : C → A) (hDB : D → B) :
    (¬(A ∨ D) ∧ ¬(C ∨ B)) ↔ ¬(A ∨ B) := by
  tauto

/-- The two lower defects occupy separate columns, so folding the reflected
right defect upward recovers the two adjacent defects exactly. -/
theorem polarize_opposite_columns (u v : ℕ) (L R : Domain)
    (hL : ColumnLower L) (hR : ColumnLower R) (hdisj : ColumnDisjoint L R) :
    polarized (oppositeColumnFaces u v L R) (axialReflection ((v : ℤ) - 1))
      (fun x => (v : ℤ) - 1 < 2 * x.2) = adjacentColumnFaces u v L R := by
  ext p
  rcases p with ⟨x, y⟩
  let y' := (v : ℤ) - 1 - y
  have hpair : axialReflection ((v : ℤ) - 1) (x, y) = (x, y') := rfl
  have hback : axialReflection ((v : ℤ) - 1) (x, y') = (x, y) := by
    dsimp [axialReflection, y']
    congr 1
    ring
  have hrect : (x, y') ∈ rectangle u v ↔ (x, y) ∈ rectangle u v :=
    axial_mem_rectangle u v (x, y)
  have hRR := hdisj x y' y'
  rw [mem_polarized (axialReflection_involutive _)]
  simp only [oppositeColumnFaces, adjacentColumnFaces, Finset.mem_sdiff,
    Finset.mem_union, mem_image_involution (axialReflection_involutive _), hpair, hback, hrect]
  by_cases hm : (x, y) ∈ rectangle u v
  · have hb := mem_rectangle.mp hm
    by_cases hp : (v : ℤ) - 1 < 2 * y
    · have hYL : (x, y) ∈ L → (x, y') ∈ L := fun h => hL x y y' h (by dsimp [y']; omega) (by dsimp [y']; omega)
      have hYR : (x, y) ∈ R → (x, y') ∈ R := fun h => hR x y y' h (by dsimp [y']; omega) (by dsimp [y']; omega)
      simp only [hp, ite_true, hm, true_and]
      exact upper_column_logic _ _ _ _ hYL hYR hRR
    · have hYL : (x, y') ∈ L → (x, y) ∈ L := fun h => hL x y' y h hb.2.2.1 (by dsimp [y']; omega)
      have hYR : (x, y') ∈ R → (x, y) ∈ R := fun h => hR x y' y h hb.2.2.1 (by dsimp [y']; omega)
      simp only [hp, ite_false, hm, true_and]
      exact lower_column_logic _ _ _ _ hYL hYR
  · simp [hm]

theorem horizontal_lattice_step (x y : ℤ) : lattice.Adj (x, y) (x + 1, y) := by
  right
  exact ⟨rfl, by norm_num⟩

def separationPath (v i : ℕ) : Vertex := (i, (v : ℤ) - 1)

theorem separation_path_mem {u v : ℕ} (hu : 2 ≤ u) (hv : 2 ≤ v) (L R : Domain)
    (hL : ColumnLower L) (hR : ColumnLower R) (hdisj : ColumnDisjoint L R)
    (htopL : ∀ x : ℤ, (x, (v : ℤ) - 1) ∉ L)
    (htopR : ∀ x : ℤ, (x, (v : ℤ) - 1) ∉ R) {i : ℕ} (hi : i ≤ u - 1) :
    separationPath v i ∈ preferredDomain (oppositeColumnFaces u v L R)
      (axialReflection ((v : ℤ) - 1)) (fun x => (v : ℤ) - 1 < 2 * x.2) := by
  rw [preferredDomain, Finset.mem_filter, polarize_opposite_columns u v L R hL hR hdisj]
  simp only [adjacentColumnFaces, Finset.mem_sdiff, Finset.mem_union, mem_rectangle, separationPath]
  have h₁ := htopL (i : ℤ)
  have h₂ := htopR (i : ℤ)
  simp only [h₁, h₂, false_or, not_false_eq_true, and_true]
  omega

theorem separation_opposite {u v : ℕ} (hu : 2 ≤ u) (hv : 2 ≤ v) (L R : Domain)
    (hdisj : ColumnDisjoint L R) (hleft : (0, 0) ∈ L) (hright : ((u : ℤ) - 1, 0) ∈ R)
    (htopL : ∀ x : ℤ, (x, (v : ℤ) - 1) ∉ L)
    (htopR : ∀ x : ℤ, (x, (v : ℤ) - 1) ∉ R) :
    OppositeSingletons (oppositeColumnFaces u v L R) (axialReflection ((v : ℤ) - 1))
      (separationPath v 0) (separationPath v (u - 1)) := by
  have huCast : ((u - 1 : ℕ) : ℤ) = (u : ℤ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hLright : ((u : ℤ) - 1, 0) ∉ L := fun h => hdisj _ _ _ h hright
  have hRleft : (0, 0) ∉ R := hdisj _ _ _ hleft
  left
  simp only [oppositeColumnFaces, Finset.mem_sdiff, Finset.mem_union,
    mem_image_involution (axialReflection_involutive _), separationPath, huCast,
    Nat.cast_zero, axialReflection]
  norm_num only [sub_sub_cancel, sub_self, sub_zero]
  have htopL0 := htopL 0
  have htopLU := htopL ((u : ℤ) - 1)
  have htopR0 := htopR 0
  have htopRU := htopR ((u : ℤ) - 1)
  simp only [mem_rectangle]
  simp only [htopL0, htopLU, htopR0, htopRU, hLright, hRleft, hleft, hright,
    or_false, or_true, not_false_eq_true, not_true_eq_false, and_true,
    and_false, not_false_eq_true, true_and]
  omega

/-- Strict separation on actual finite face sets; the path is the intact top row. -/
theorem separation_determinant {u v : ℕ} (hu : 2 ≤ u) (hv : 2 ≤ v) (L R : Domain)
    (hL : ColumnLower L) (hR : ColumnLower R) (hdisj : ColumnDisjoint L R)
    (hleft : (0, 0) ∈ L) (hright : ((u : ℤ) - 1, 0) ∈ R)
    (htopL : ∀ x : ℤ, (x, (v : ℤ) - 1) ∉ L)
    (htopR : ∀ x : ℤ, (x, (v : ℤ) - 1) ∉ R) (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (adjacentColumnFaces u v L R) z < faceDeterminant (oppositeColumnFaces u v L R) z := by
  let P := preferredDomain (oppositeColumnFaces u v L R) (axialReflection ((v : ℤ) - 1))
    (fun x => (v : ℤ) - 1 < 2 * x.2)
  have hmem : ∀ i, i ≤ u - 1 → separationPath v i ∈ P :=
    fun i hi => separation_path_mem hu hv L R hL hR hdisj htopL htopR hi
  have hadj : ∀ i, i < u - 1 → lattice.Adj (separationPath v i) (separationPath v (i + 1)) := by
    intro i _
    simpa [separationPath, Nat.cast_add, Nat.cast_one] using horizontal_lattice_step i ((v : ℤ) - 1)
  obtain ⟨p⟩ := reachable_along P (separationPath v) (u - 1) hmem hadj
  have h := axial_determinant_strict (oppositeColumnFaces u v L R) ((v : ℤ) - 1) z hz p
    (separation_opposite hu hv L R hdisj hleft hright htopL htopR)
  change faceDeterminant (polarized (oppositeColumnFaces u v L R)
    (axialReflection ((v : ℤ) - 1)) (fun x => (v : ℤ) - 1 < 2 * x.2)) z < _ at h
  rw [polarize_opposite_columns u v L R hL hR hdisj] at h
  exact h

theorem ferrers_origin_mem {M : Diagram} (hM : IsFerrers M) (hne : M.Nonempty) : (0, 0) ∈ M := by
  obtain ⟨p, hp⟩ := hne
  exact hM p hp (0, 0) (by omega) (by omega)

theorem ferrers_coordinate_lt_card {M : Diagram} (hM : IsFerrers M) {p : Point} (hp : p ∈ M) :
    p.1 < M.card ∧ p.2 < M.card := by
  have hx : horizontalStrip (p.1 + 1) ⊆ M := by
    intro q hq
    have hq' := mem_horizontalStrip.mp hq
    exact hM p hp q (by omega) (by omega)
  have hy : transpose (horizontalStrip (p.2 + 1)) ⊆ M := by
    intro q hq
    have hq' := mem_horizontalStrip.mp (mem_transpose.mp hq)
    simp only [Prod.fst_swap, Prod.snd_swap] at hq'
    exact hM p hp q (by omega) (by omega)
  have hcx := Finset.card_le_card hx
  have hcy := Finset.card_le_card hy
  simp only [card_horizontalStrip, card_transpose] at hcx hcy
  omega

/-- Actual bottom-left and bottom-right placements of the natural Ferrers diagrams. -/
def bottomRightDefect (u : ℕ) (M : Diagram) : Domain :=
  (integerFaces M).image (verticalReflection ((u : ℤ) - 1))

def adjacentCornerFaces (u v : ℕ) (A B : Diagram) : Domain :=
  adjacentColumnFaces u v (integerFaces A) (bottomRightDefect u B)

def oppositeCornerFaces (u v : ℕ) (A B : Diagram) : Domain :=
  oppositeColumnFaces u v (integerFaces A) (bottomRightDefect u B)

theorem integerFaces_columnLower {M : Diagram} (hM : IsFerrers M) : ColumnLower (integerFaces M) := by
  intro x y z hxy hz0 hzy
  obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hxy
  have hx := congrArg Prod.fst heq
  have hy := congrArg Prod.snd heq
  dsimp [SquareMaximality.Boundary.ofNatPoint] at hx hy
  apply Finset.mem_image.mpr
  refine ⟨(p.1, z.toNat), hM p hp _ le_rfl (by omega), ?_⟩
  apply Prod.ext
  · exact hx
  · exact Int.toNat_of_nonneg hz0

theorem columnLower_vertical_image {M : Domain} (hM : ColumnLower M) (c : ℤ) :
    ColumnLower (M.image (verticalReflection c)) := by
  intro x y z hxy hz0 hzy
  rw [mem_image_involution (vertical_involutive c)] at hxy ⊢
  exact hM (c - x) y z hxy hz0 hzy

theorem integerFaces_coordinate_bounds {M : Diagram} (hM : IsFerrers M) {x : Vertex}
    (hx : x ∈ integerFaces M) : 0 ≤ x.1 ∧ x.1 < M.card ∧ 0 ≤ x.2 ∧ x.2 < M.card := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  have hb := ferrers_coordinate_lt_card hM hp
  dsimp [SquareMaximality.Boundary.ofNatPoint]
  omega

theorem corner_column_disjoint {u : ℕ} {A B : Diagram} (hA : IsFerrers A) (hB : IsFerrers B)
    (hcard : A.card + B.card ≤ u) : ColumnDisjoint (integerFaces A) (bottomRightDefect u B) := by
  intro x y z hx hz
  have hL := integerFaces_coordinate_bounds hA hx
  have hR := integerFaces_coordinate_bounds hB
    ((mem_image_involution (vertical_involutive ((u : ℤ) - 1)) (x, z)).mp hz)
  dsimp [verticalReflection] at hR
  omega

theorem integerFaces_origin {M : Diagram} (hM : IsFerrers M) (hne : M.Nonempty) :
    (0, 0) ∈ integerFaces M :=
  Finset.mem_image.mpr ⟨(0, 0), ferrers_origin_mem hM hne, rfl⟩

theorem bottomRight_origin {u : ℕ} {M : Diagram} (hM : IsFerrers M) (hne : M.Nonempty) :
    ((u : ℤ) - 1, 0) ∈ bottomRightDefect u M := by
  exact Finset.mem_image.mpr ⟨(0, 0), integerFaces_origin hM hne, by simp [verticalReflection]⟩

theorem corner_top_absent {v : ℕ} {A B : Diagram} (hA : IsFerrers A) (hneB : B.Nonempty)
    (hcard : A.card + B.card ≤ v) (x : ℤ) : (x, (v : ℤ) - 1) ∉ integerFaces A := by
  intro hx
  have h := integerFaces_coordinate_bounds hA hx
  have hb := Finset.card_pos.mpr hneB
  omega

theorem bottomRight_top_absent {u v : ℕ} {A B : Diagram} (hB : IsFerrers B) (hneA : A.Nonempty)
    (hcard : A.card + B.card ≤ v) (x : ℤ) : (x, (v : ℤ) - 1) ∉ bottomRightDefect u B := by
  intro hx
  have h := integerFaces_coordinate_bounds hB
    ((mem_image_involution (vertical_involutive ((u : ℤ) - 1)) (x, (v : ℤ) - 1)).mp hx)
  have ha := Finset.card_pos.mpr hneA
  dsimp [verticalReflection] at h
  omega

/-- `prop:separate-corners`, at the level of the actual face sets and determinants. -/
theorem separate_corners_determinant {u v : ℕ} (A B : Diagram)
    (hA : IsFerrers A) (hB : IsFerrers B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hu : A.card + B.card ≤ u) (hv : A.card + B.card ≤ v) (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (adjacentCornerFaces u v A B) z <
      faceDeterminant (oppositeCornerFaces u v A B) z := by
  have ha := Finset.card_pos.mpr hneA
  have hb := Finset.card_pos.mpr hneB
  exact separation_determinant (by omega) (by omega) (integerFaces A) (bottomRightDefect u B)
    (integerFaces_columnLower hA)
    (columnLower_vertical_image (integerFaces_columnLower hB) ((u : ℤ) - 1))
    (corner_column_disjoint hA hB hu) (integerFaces_origin hA hneA) (bottomRight_origin hB hneB)
    (corner_top_absent hA hneB hv) (bottomRight_top_absent hB hneA hv) z hz

theorem corner_separation_polarization {u v : ℕ} (A B : Diagram)
    (hA : IsFerrers A) (hB : IsFerrers B) (hu : A.card + B.card ≤ u) :
    polarized (oppositeCornerFaces u v A B) (axialReflection ((v : ℤ) - 1))
      (fun x => (v : ℤ) - 1 < 2 * x.2) = adjacentCornerFaces u v A B :=
  polarize_opposite_columns u v _ _ (integerFaces_columnLower hA)
    (columnLower_vertical_image (integerFaces_columnLower hB) ((u : ℤ) - 1))
    (corner_column_disjoint hA hB hu)

theorem corner_separation_card {u v : ℕ} (A B : Diagram)
    (hA : IsFerrers A) (hB : IsFerrers B) (hu : A.card + B.card ≤ u) :
    (oppositeCornerFaces u v A B).card = (adjacentCornerFaces u v A B).card := by
  have h := card_polarized (U := oppositeCornerFaces u v A B)
    (axialReflection_involutive ((v : ℤ) - 1)) (fun x => (v : ℤ) - 1 < 2 * x.2)
    (axial_preferred_side ((v : ℤ) - 1))
  rw [corner_separation_polarization A B hA hB hu] at h
  exact h.symm

/-- Face set for opposite vertical strips in a primal `r × s` rectangle. -/
def twoVerticalFaces (r s a b : ℕ) : Domain :=
  (rectangle (r - 1) (s - 1)).filter fun x =>
    (x.1 ≠ 0 ∨ (a : ℤ) ≤ x.2) ∧
      (x.1 ≠ (r : ℤ) - 2 ∨ x.2 < (s : ℤ) - 1 - b)

/-- More elongated candidate with one top-right strip. -/
def twoStripCandidate (r s b : ℕ) : Domain :=
  (rectangle (r - 2) s).filter fun x =>
    x.1 ≠ (r : ℤ) - 3 ∨ x.2 < (s : ℤ) - 1 - b

/-- Translation by `(-1,0)` of the two-vertical-strip source. -/
def twoStripFolded (r s b : ℕ) : Domain :=
  ((Finset.Ico (-1 : ℤ) ((r : ℤ) - 2)) ×ˢ Finset.Ico (0 : ℤ) ((s : ℤ) - 1)).filter
    fun x => (x.1 ≠ -1 ∨ (s : ℤ) - r + 2 ≤ x.2) ∧
      (x.1 ≠ (r : ℤ) - 3 ∨ x.2 < (s : ℤ) - 1 - b)

@[simp] theorem mem_twoVerticalFaces {r s a b : ℕ} {x : Vertex} :
    x ∈ twoVerticalFaces r s a b ↔
      0 ≤ x.1 ∧ x.1 < (r - 1 : ℕ) ∧ 0 ≤ x.2 ∧ x.2 < (s - 1 : ℕ) ∧
        (x.1 ≠ 0 ∨ (a : ℤ) ≤ x.2) ∧
        (x.1 ≠ (r : ℤ) - 2 ∨ x.2 < (s : ℤ) - 1 - b) := by
  simp only [twoVerticalFaces, Finset.mem_filter, mem_rectangle]
  tauto

@[simp] theorem mem_twoStripCandidate {r s b : ℕ} {x : Vertex} :
    x ∈ twoStripCandidate r s b ↔
      0 ≤ x.1 ∧ x.1 < (r - 2 : ℕ) ∧ 0 ≤ x.2 ∧ x.2 < s ∧
        (x.1 ≠ (r : ℤ) - 3 ∨ x.2 < (s : ℤ) - 1 - b) := by
  simp only [twoStripCandidate, Finset.mem_filter, mem_rectangle]
  tauto

@[simp] theorem mem_twoStripFolded {r s b : ℕ} {x : Vertex} :
    x ∈ twoStripFolded r s b ↔
      -1 ≤ x.1 ∧ x.1 < (r : ℤ) - 2 ∧ 0 ≤ x.2 ∧ x.2 < (s : ℤ) - 1 ∧
        (x.1 ≠ -1 ∨ (s : ℤ) - r + 2 ≤ x.2) ∧
        (x.1 ≠ (r : ℤ) - 3 ∨ x.2 < (s : ℤ) - 1 - b) := by
  simp only [twoStripFolded, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico]
  tauto

/-- The antidiagonal fold is proved for the literal finite occupied face sets. -/
theorem polarize_twoStripCandidate {r s b : ℕ} (hrs : r ≤ s) (hb : 1 ≤ b)
    (hsize : s - r + b + 2 < r) :
    polarized (twoStripCandidate r s b) (antiDiagonalReflection ((s : ℤ) - 2))
      (fun x => x.1 + x.2 < (s : ℤ) - 2) = twoStripFolded r s b := by
  ext x
  rw [mem_polarized (antiDiagonal_involutive _)]
  simp only [mem_twoStripCandidate, mem_twoStripFolded, antiDiagonalReflection]
  have hr : 4 ≤ r := by omega
  have hr2 : ((r - 2 : ℕ) : ℤ) = (r : ℤ) - 2 := by omega
  rw [hr2]
  split_ifs <;> omega

noncomputable def twoStripSourceIso {r s b : ℕ} (hrs : r ≤ s) (hr : 2 ≤ r) :
    domainGraph (twoVerticalFaces r s (s - r + 2) b) ≃g domainGraph (twoStripFolded r s b) :=
  graphIsoOfEquiv (translationEquiv (-1, 0))
    (by
      intro x
      simp only [mem_twoVerticalFaces, mem_twoStripFolded, translationEquiv, translate,
        Equiv.coe_fn_mk, zero_add]
      omega)
    (fun x y _ _ => translate_adj (-1, 0) x y)

theorem twoStrip_determinant {r s b : ℕ} (hrs : r ≤ s) (hb : 1 ≤ b)
    (hsize : s - r + b + 2 < r) (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (twoVerticalFaces r s (s - r + 2) b) z ≤
      faceDeterminant (twoStripCandidate r s b) z := by
  have h := adjacency_determinant_of_domain_moments (twoStripCandidate r s b)
    (polarized (twoStripCandidate r s b) (antiDiagonalReflection ((s : ℤ) - 2))
      (fun x => x.1 + x.2 < (s : ℤ) - 2))
    (card_polarized (antiDiagonal_involutive _) _ (antiDiagonal_side _)).symm
    (fun i => antiDiagonal_adjacency_moments _ _ (i + 1)) z hz
  change faceDeterminant (polarized (twoStripCandidate r s b)
    (antiDiagonalReflection ((s : ℤ) - 2)) (fun x => x.1 + x.2 < (s : ℤ) - 2)) z ≤ _ at h
  rw [polarize_twoStripCandidate hrs hb hsize] at h
  rw [faceDeterminant_iso (twoStripSourceIso hrs (by omega)) z]
  exact h

/-- Vertical segment followed by a left step and an upward step. -/
def twoStripPath (s i : ℕ) : Vertex :=
  if i ≤ s - 3 then (0, i) else (-1, (i : ℤ) - 1)

theorem twoStripPath_mem {r s b : ℕ} (hrs : r ≤ s) (hr : 5 ≤ r) (hb : 1 ≤ b)
    (hsize : s - r + b + 2 < r) {i : ℕ} (hi : i ≤ s - 1) :
    twoStripPath s i ∈ preferredDomain (twoStripCandidate r s b)
      (antiDiagonalReflection ((s : ℤ) - 2)) (fun x => x.1 + x.2 < (s : ℤ) - 2) := by
  rw [preferredDomain, Finset.mem_filter, polarize_twoStripCandidate hrs hb hsize]
  simp only [mem_twoStripFolded, twoStripPath]
  split_ifs <;> omega

theorem twoStripPath_adj {s i : ℕ} (_hs : 5 ≤ s) (_hi : i < s - 1) :
    lattice.Adj (twoStripPath s i) (twoStripPath s (i + 1)) := by
  by_cases h₁ : i + 1 ≤ s - 3
  · have h₀ : i ≤ s - 3 := by omega
    simpa [twoStripPath, h₀, h₁, Nat.cast_add, Nat.cast_one] using vertical_lattice_step 0 i
  · by_cases h₀ : i ≤ s - 3
    · have hi' : i = s - 3 := by omega
      simp only [twoStripPath, h₀, h₁, ite_true, ite_false]
      right
      constructor
      · simp only [Nat.cast_add, Nat.cast_one]; omega
      · norm_num
    · simp only [twoStripPath, h₀, h₁, ite_false]
      left
      constructor
      · rfl
      · rw [Nat.cast_add, Nat.cast_one]
        norm_num

 theorem twoStripPath_opposite {r s b : ℕ} (hrs : r ≤ s) (hr : 5 ≤ r) (hb : 1 ≤ b)
    (hsize : s - r + b + 2 < r) :
    OppositeSingletons (twoStripCandidate r s b) (antiDiagonalReflection ((s : ℤ) - 2))
      (twoStripPath s 0) (twoStripPath s (s - 1)) := by
  left
  have hlast : ¬s - 1 ≤ s - 3 := by omega
  simp only [twoStripPath, Nat.zero_le, ite_true, hlast, ite_false, Nat.cast_zero,
    mem_twoStripCandidate, antiDiagonalReflection]
  omega

theorem twoStrip_determinant_strict {r s b : ℕ} (hrs : r ≤ s) (hr : 5 ≤ r) (hb : 1 ≤ b)
    (hsize : s - r + b + 2 < r) (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (twoVerticalFaces r s (s - r + 2) b) z <
      faceDeterminant (twoStripCandidate r s b) z := by
  let P := preferredDomain (twoStripCandidate r s b) (antiDiagonalReflection ((s : ℤ) - 2))
    (fun x => x.1 + x.2 < (s : ℤ) - 2)
  have hmem : ∀ i, i ≤ s - 1 → twoStripPath s i ∈ P :=
    fun i hi => twoStripPath_mem hrs hr hb hsize hi
  obtain ⟨p⟩ := reachable_along P (twoStripPath s) (s - 1) hmem
    (fun i hi => twoStripPath_adj (by omega) hi)
  have h := antiDiagonal_determinant_strict (twoStripCandidate r s b) ((s : ℤ) - 2) z hz p
    (twoStripPath_opposite hrs hr hb hsize)
  change faceDeterminant (polarized (twoStripCandidate r s b)
    (antiDiagonalReflection ((s : ℤ) - 2)) (fun x => x.1 + x.2 < (s : ℤ) - 2)) z < _ at h
  rw [polarize_twoStripCandidate hrs hb hsize] at h
  rw [faceDeterminant_iso (twoStripSourceIso hrs (by omega)) z]
  exact h

/-- Half-turn carrying the candidate defect to the standard bottom-left strip. -/
def twoStripCandidateCoordinates (r s : ℕ) : Vertex ≃ Vertex :=
  (Function.Involutive.toPerm (verticalReflection ((r : ℤ) - 3)) (vertical_involutive _)).trans
    (Function.Involutive.toPerm (axialReflection ((s : ℤ) - 1)) (axialReflection_involutive _))

@[simp] theorem twoStripCandidateCoordinates_apply (r s : ℕ) (x : Vertex) :
    twoStripCandidateCoordinates r s x = ((r : ℤ) - 3 - x.1, (s : ℤ) - 1 - x.2) := by
  rfl

noncomputable def twoStripCandidateIso {r s b : ℕ} (hr : 2 ≤ r) :
    domainGraph (twoStripCandidate r s b) ≃g domainGraph (faceStripY (r - 2) s (b + 1)) :=
  graphIsoOfEquiv (twoStripCandidateCoordinates r s)
    (by
      intro x
      simp only [mem_twoStripCandidate, mem_faceStripY, twoStripCandidateCoordinates_apply,
        Nat.cast_add, Nat.cast_one]
      omega)
    (by
      intro x y _ _
      change lattice.Adj (axialReflection ((s : ℤ) - 1) (verticalReflection ((r : ℤ) - 3) x))
        (axialReflection ((s : ℤ) - 1) (verticalReflection ((r : ℤ) - 3) y)) ↔ _
      rw [axial_adjacency_invariant, vertical_adjacency_invariant])

private def exceptionalSourceVertex (i : Fin 6) : Vertex :=
  ![(1, 1), (1, 2), (0, 2), (1, 0), (2, 0), (2, 1)] i

private def exceptionalCandidateVertex (i : Fin 6) : Vertex :=
  ![(0, 1), (0, 2), (0, 3), (0, 0), (1, 0), (1, 1)] i

private def exceptionalSourceMap (i : Fin 6) : (twoVerticalFaces 4 4 2 1 : Set Vertex) :=
  ⟨exceptionalSourceVertex i, by fin_cases i <;> decide +kernel⟩

private def exceptionalCandidateMap (i : Fin 6) : (twoStripCandidate 4 4 1 : Set Vertex) :=
  ⟨exceptionalCandidateVertex i, by fin_cases i <;> decide +kernel⟩

private theorem exceptionalSource_bijective : Function.Bijective exceptionalSourceMap := by
  decide +kernel

private theorem exceptionalCandidate_bijective : Function.Bijective exceptionalCandidateMap := by
  decide +kernel

private theorem exceptional_adj (i j : Fin 6) :
    lattice.Adj (exceptionalCandidateVertex i) (exceptionalCandidateVertex j) ↔
      lattice.Adj (exceptionalSourceVertex i) (exceptionalSourceVertex j) := by
  simp only [lattice]
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- The six faces form a four-cycle with a two-edge pendant path on either side. -/
noncomputable def exceptionalTwoStripIso :
    domainGraph (twoVerticalFaces 4 4 2 1) ≃g domainGraph (twoStripCandidate 4 4 1) := by
  let G := lattice.comap exceptionalSourceVertex
  let e : G ≃g domainGraph (twoVerticalFaces 4 4 2 1) :=
    { Equiv.ofBijective exceptionalSourceMap exceptionalSource_bijective with
      map_rel_iff' := by intro i j; rfl }
  let f : G ≃g domainGraph (twoStripCandidate 4 4 1) :=
    { Equiv.ofBijective exceptionalCandidateMap exceptionalCandidate_bijective with
      map_rel_iff' := by intro i j; exact exceptional_adj i j }
  exact e.symm.trans f

theorem twoStrip_determinant_eq_iff {r s b : ℕ} (hrs : r ≤ s) (hb : 1 ≤ b)
    (hsize : s - r + b + 2 < r) (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (twoVerticalFaces r s (s - r + 2) b) z =
      faceDeterminant (twoStripCandidate r s b) z ↔ r = 4 ∧ s = 4 ∧ b = 1 := by
  constructor
  · intro heq
    by_contra h
    have hr : 5 ≤ r := by omega
    have hlt := twoStrip_determinant_strict hrs hr hb hsize z hz
    linarith
  · rintro ⟨rfl, rfl, rfl⟩
    exact faceDeterminant_iso exceptionalTwoStripIso z

/-- Actual maximal block exists; its maximality gives the two-piece geometry. -/
theorem exists_maximal_ferrers_block {M : Diagram} (hM : IsFerrers M) (d : ℕ)
    (hheight : (0, d) ∈ M) :
    ∃ t : ℕ, 0 < t ∧ (t - 1, d + t - 1) ∈ M ∧
      (Finset.range t ×ˢ Finset.range (d + t)) ⊆ M ∧
      (∀ p ∈ M, p.1 < t ∨ p.2 < d + t) ∧ t * (d + t) ≤ M.card := by
  let sizes := (M.image (fun p => p.1 + 1)).filter fun t => (t - 1, d + t - 1) ∈ M
  have h1 : 1 ∈ sizes := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨(0, d), hheight, rfl⟩, by simpa using hheight⟩
  let t := sizes.max' ⟨1, h1⟩
  have ht : t ∈ sizes := Finset.max'_mem _ _
  have ht1 : 1 ≤ t := Finset.le_max' _ 1 h1
  have hcorner : (t - 1, d + t - 1) ∈ M := (Finset.mem_filter.mp ht).2
  have hblock : (Finset.range t ×ˢ Finset.range (d + t)) ⊆ M := by
    intro p hp
    have hp' := Finset.mem_product.mp hp
    simp only [Finset.mem_range] at hp'
    exact hM _ hcorner p (by omega) (by omega)
  have hsplit : ∀ p ∈ M, p.1 < t ∨ p.2 < d + t := by
    intro p hp
    by_contra h
    have hnext : (t, d + t) ∈ M := hM p hp _ (by omega) (by omega)
    have htNext : t + 1 ∈ sizes := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨(t, d + t), hnext, rfl⟩, ?_⟩
      simpa only [← Nat.add_assoc, Nat.add_sub_cancel] using hnext
    have hle : t + 1 ≤ t := Finset.le_max' _ _ htNext
    omega
  refine ⟨t, ht1, hcorner, hblock, hsplit, ?_⟩
  have hc := Finset.card_le_card hblock
  simpa only [Finset.card_product, Finset.card_range] using hc

end SpanningTreeIsoperimetry.CornerFolds

