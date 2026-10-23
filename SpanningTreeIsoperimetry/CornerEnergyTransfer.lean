module

public import SpanningTreeIsoperimetry.EnergyConvergence

@[expose] public section

/-!
# Finite-rectangle corrections to the closed-word corner energy

The correction below counts actual hitting starts whose translated word does
not fit the finite rectangle. All infinite sums are proved convergent. These
are the word-count and series ingredients of `lem:finite-transfer`; identifying
their sum with the Dirichlet log-determinant defect remains a separate theorem.
-/

namespace SpanningTreeIsoperimetry.CornerEnergy

open scoped BigOperators
open Ferrers

/-- The finite face rectangle, with side lengths measured in faces. -/
def faceRectangle (m n : ℕ) : Diagram := Finset.range m ×ˢ Finset.range n

@[simp] theorem mem_faceRectangle {m n : ℕ} {t : Point} :
    t ∈ faceRectangle m n ↔ t.1 < m ∧ t.2 < n := by
  simp [faceRectangle]

/-- Starts for which every visited point of the translated word fits `U`. -/
def fittingStarts (U P : Diagram) : Diagram :=
  U.filter (fun t => ∀ p ∈ P, shift t p ∈ U)

@[simp] theorem mem_fittingStarts {U P : Diagram} {t : Point} :
    t ∈ fittingStarts U P ↔ t ∈ U ∧ ∀ p ∈ P, shift t p ∈ U :=
  Finset.mem_filter

/-- Starts that hit the defect but whose full word leaves the rectangle. -/
def lostStarts (U M P : Diagram) : Diagram := hitStarts M P \ fittingStarts U P

def lostCount (U M P : Diagram) : ℕ := (lostStarts U M P).card

theorem lostCount_le_card (U M P : Diagram) : lostCount U M P ≤ M.card :=
  Finset.card_le_card (Finset.Subset.trans Finset.sdiff_subset (hitStarts_subset M P))

theorem hitStarts_mono {A B P : Diagram} (hAB : A ⊆ B) :
    hitStarts A P ⊆ hitStarts B P := by
  intro t ht
  obtain ⟨htA, p, hp, htp⟩ := mem_hitStarts.mp ht
  exact mem_hitStarts.mpr ⟨hAB htA, p, hp, hAB htp⟩

theorem lostStarts_mono {U A B P : Diagram} (hAB : A ⊆ B) :
    lostStarts U A P ⊆ lostStarts U B P :=
  Finset.sdiff_subset_sdiff (hitStarts_mono hAB) (Finset.Subset.refl _)

theorem lostCount_mono {U A B P : Diagram} (hAB : A ⊆ B) :
    lostCount U A P ≤ lostCount U B P := Finset.card_le_card (lostStarts_mono hAB)

theorem fittingStarts_faceRectangle (m n : ℕ) (P : Diagram) :
    fittingStarts (faceRectangle m n) P =
      faceRectangle (m - P.sup Prod.fst) (n - P.sup Prod.snd) := by
  ext t
  simp only [mem_fittingStarts, mem_faceRectangle]
  constructor
  · rintro ⟨⟨htx, hty⟩, hfit⟩
    have hx : P.sup Prod.fst < m - t.1 := by
      apply (Finset.sup_lt_iff (show (0 : ℕ) < _ by omega)).mpr
      intro p hp
      have := (hfit p hp).1
      dsimp [shift] at this
      omega
    have hy : P.sup Prod.snd < n - t.2 := by
      apply (Finset.sup_lt_iff (show (0 : ℕ) < _ by omega)).mpr
      intro p hp
      have := (hfit p hp).2
      dsimp [shift] at this
      omega
    constructor <;> omega
  · intro ht
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro p hp
    have hx := Finset.le_sup (f := Prod.fst) hp
    have hy := Finset.le_sup (f := Prod.snd) hp
    dsimp [shift]
    constructor <;> omega

theorem horizontalStrip_inter_rectangle (k m n : ℕ) :
    horizontalStrip k ∩ faceRectangle m n =
      horizontalStrip (if n = 0 then 0 else min k m) := by
  ext t
  simp only [Finset.mem_inter, mem_horizontalStrip, mem_faceRectangle]
  split_ifs with hn <;> omega

theorem lostCount_horizontalStrip (m n k : ℕ) {P : Diagram}
    (hP : IsNormalized P) :
    lostCount (faceRectangle m n) (horizontalStrip k) P =
      k - firstAxisX P hP -
        (if n - P.sup Prod.snd = 0 then 0 else m - P.sup Prod.fst) := by
  rw [lostCount, lostStarts,
    hitStarts_horizontalStrip (firstAxisX_mem hP) (fun _ hp hp0 => firstAxisX_le hP hp hp0),
    fittingStarts_faceRectangle, Finset.card_sdiff, Finset.inter_comm,
    horizontalStrip_inter_rectangle]
  simp only [card_horizontalStrip]
  split_ifs <;> omega

theorem lostCount_strip_convex (m n k : ℕ) {P : Diagram} (hP : IsNormalized P) :
    2 * lostCount (faceRectangle m n) (horizontalStrip (k + 1)) P ≤
      lostCount (faceRectangle m n) (horizontalStrip k) P +
        lostCount (faceRectangle m n) (horizontalStrip (k + 2)) P := by
  simp only [lostCount_horizontalStrip m n _ hP]
  omega

/-- Positive-length word sums for the finite correction. -/
def lostSum (U M : Diagram) (ℓ : ℕ) : ℕ :=
  ∑ w : ClosedWord ℓ, lostCount U M (normalizedVisited w.val)

noncomputable def correctionTerm (U M : Diagram) (n : ℕ) : ℝ :=
  (lostSum U M (n + 1) : ℝ) / ((n + 1 : ℝ) * 4 ^ (n + 1))

noncomputable def correction (U M : Diagram) : ℝ := ∑' n, correctionTerm U M n

theorem correctionTerm_nonneg (U M : Diagram) (n : ℕ) :
    0 ≤ correctionTerm U M n := by unfold correctionTerm; positivity

theorem lostSum_le_card_mul_closedWord (U M : Diagram) (ℓ : ℕ) :
    lostSum U M ℓ ≤ M.card * Fintype.card (ClosedWord ℓ) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (ClosedWord ℓ)))
    (fun w _ => lostCount_le_card U M (normalizedVisited w.val))
  simpa [lostSum, mul_comm] using h

theorem correctionTerm_le_closedWordTerm (U M : Diagram) (n : ℕ) :
    correctionTerm U M n ≤ (M.card : ℝ) * closedWordTerm n := by
  unfold correctionTerm closedWordTerm
  rw [← mul_div_assoc]
  gcongr
  exact_mod_cast lostSum_le_card_mul_closedWord U M (n + 1)

theorem correctionTerm_summable (U M : Diagram) : Summable (correctionTerm U M) :=
  Summable.of_nonneg_of_le (correctionTerm_nonneg U M)
    (correctionTerm_le_closedWordTerm U M)
    (closedWordTerm_summable.mul_left (M.card : ℝ))

theorem correction_nonneg (U M : Diagram) : 0 ≤ correction U M :=
  tsum_nonneg (correctionTerm_nonneg U M)

@[simp] theorem correction_empty (U : Diagram) : correction U ∅ = 0 := by
  simp [correction, correctionTerm, lostSum, lostCount, lostStarts, hitStarts]

theorem correction_mono {U A B : Diagram} (hAB : A ⊆ B) :
    correction U A ≤ correction U B := by
  apply (correctionTerm_summable U A).tsum_le_tsum
    (fun n => ?_) (correctionTerm_summable U B)
  unfold correctionTerm
  gcongr
  exact Finset.sum_le_sum (fun _ _ => lostCount_mono hAB)

/-- At each word length the finite strip correction is discretely convex. -/
theorem lostSum_strip_convex (m n k ℓ : ℕ) :
    2 * lostSum (faceRectangle m n) (horizontalStrip (k + 1)) ℓ ≤
      lostSum (faceRectangle m n) (horizontalStrip k) ℓ +
        lostSum (faceRectangle m n) (horizontalStrip (k + 2)) ℓ := by
  simpa only [lostSum, Finset.sum_add_distrib, Finset.mul_sum] using
    Finset.sum_le_sum (s := (Finset.univ : Finset (ClosedWord ℓ)))
      (fun w _ => lostCount_strip_convex m n k (normalizedVisited_isNormalized w.val))

theorem correctionTerm_strip_convex (m n k i : ℕ) :
    2 * correctionTerm (faceRectangle m n) (horizontalStrip (k + 1)) i ≤
      correctionTerm (faceRectangle m n) (horizontalStrip k) i +
        correctionTerm (faceRectangle m n) (horizontalStrip (k + 2)) i := by
  unfold correctionTerm
  rw [← mul_div_assoc, ← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast lostSum_strip_convex m n k (i + 1)

/-- The full convergent closed-word correction has nonnegative second difference. -/
theorem correction_strip_convex (m n k : ℕ) :
    2 * correction (faceRectangle m n) (horizontalStrip (k + 1)) ≤
      correction (faceRectangle m n) (horizontalStrip k) +
        correction (faceRectangle m n) (horizontalStrip (k + 2)) := by
  have h := ((correctionTerm_summable (faceRectangle m n)
    (horizontalStrip (k + 1))).mul_left 2).tsum_le_tsum
    (correctionTerm_strip_convex m n k)
    ((correctionTerm_summable (faceRectangle m n) (horizontalStrip k)).add
      (correctionTerm_summable (faceRectangle m n) (horizontalStrip (k + 2))))
  rw [tsum_mul_left, Summable.tsum_add
    (correctionTerm_summable (faceRectangle m n) (horizontalStrip k))
    (correctionTerm_summable (faceRectangle m n) (horizontalStrip (k + 2)))] at h
  exact h

/-- The extra contribution from a specified cell, restricted to words visiting zero. -/
def cellLostCount (U : Diagram) (t : Point) (P : Diagram) : ℕ :=
  if (0, 0) ∈ P ∧ t ∉ fittingStarts U P then 1 else 0

theorem cellLostCount_le_one (U : Diagram) (t : Point) (P : Diagram) :
    cellLostCount U t P ≤ 1 := by unfold cellLostCount; split_ifs <;> omega

/-- Adding a diagram includes every newly lost cell for words that visit zero. -/
theorem lostCount_transfer {U A B P : Diagram} (hAB : A ⊆ B) :
    lostCount U A P + ∑ t ∈ B \ A, cellLostCount U t P ≤ lostCount U B P := by
  by_cases h0 : (0, 0) ∈ P
  · have hsum : (∑ t ∈ B \ A, cellLostCount U t P) =
        ((B \ A) \ fittingStarts U P).card := by
      simp only [cellLostCount, h0, true_and, Finset.sum_boole, Nat.cast_id, Finset.sdiff_eq_filter]
    rw [hsum]
    simp only [lostCount, lostStarts, hitStarts_eq_of_origin_mem h0]
    have hsub : A \ fittingStarts U P ⊆ B \ fittingStarts U P :=
      Finset.sdiff_subset_sdiff hAB (Finset.Subset.refl _)
    have heq : (B \ fittingStarts U P) \ (A \ fittingStarts U P) =
        (B \ A) \ fittingStarts U P := by ext t; simp; tauto
    have hcard := Finset.card_sdiff_add_card_eq_card hsub
    rw [heq] at hcard
    omega
  · simpa [cellLostCount, h0] using lostCount_mono (U := U) (P := P) hAB

def cellLostSum (U : Diagram) (t : Point) (ℓ : ℕ) : ℕ :=
  ∑ w : ClosedWord ℓ, cellLostCount U t (normalizedVisited w.val)

noncomputable def cellCorrectionTerm (U : Diagram) (t : Point) (n : ℕ) : ℝ :=
  (cellLostSum U t (n + 1) : ℝ) / ((n + 1 : ℝ) * 4 ^ (n + 1))

noncomputable def cellCorrection (U : Diagram) (t : Point) : ℝ :=
  ∑' n, cellCorrectionTerm U t n

theorem cellCorrectionTerm_nonneg (U : Diagram) (t : Point) (n : ℕ) :
    0 ≤ cellCorrectionTerm U t n := by unfold cellCorrectionTerm; positivity

theorem cellLostSum_le_closedWord (U : Diagram) (t : Point) (ℓ : ℕ) :
    cellLostSum U t ℓ ≤ Fintype.card (ClosedWord ℓ) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (ClosedWord ℓ)))
    (fun w _ => cellLostCount_le_one U t (normalizedVisited w.val))
  simpa [cellLostSum] using h

theorem cellCorrectionTerm_le_closedWordTerm (U : Diagram) (t : Point) (n : ℕ) :
    cellCorrectionTerm U t n ≤ closedWordTerm n := by
  unfold cellCorrectionTerm closedWordTerm
  gcongr
  exact cellLostSum_le_closedWord U t (n + 1)

theorem cellCorrectionTerm_summable (U : Diagram) (t : Point) :
    Summable (cellCorrectionTerm U t) :=
  Summable.of_nonneg_of_le (cellCorrectionTerm_nonneg U t)
    (cellCorrectionTerm_le_closedWordTerm U t) closedWordTerm_summable

theorem lostSum_transfer {U A B : Diagram} (hAB : A ⊆ B) (ℓ : ℕ) :
    lostSum U A ℓ + ∑ t ∈ B \ A, cellLostSum U t ℓ ≤ lostSum U B ℓ := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (ClosedWord ℓ)))
    (fun w _ => lostCount_transfer (U := U) (P := normalizedVisited w.val) hAB)
  simpa only [lostSum, cellLostSum, Finset.sum_add_distrib,
    Finset.sum_comm (s := Finset.univ) (t := B \ A)] using h

theorem correctionTerm_transfer {U A B : Diagram} (hAB : A ⊆ B) (n : ℕ) :
    correctionTerm U A n + ∑ t ∈ B \ A, cellCorrectionTerm U t n ≤
      correctionTerm U B n := by
  unfold correctionTerm cellCorrectionTerm
  rw [← Finset.sum_div, ← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast lostSum_transfer (U := U) hAB (n + 1)

/-- The complete added-cell transfer inequality for the convergent loss series. -/
theorem correction_transfer {U A B : Diagram} (hAB : A ⊆ B) :
    correction U A + ∑ t ∈ B \ A, cellCorrection U t ≤ correction U B := by
  have hs : Summable (fun n => ∑ t ∈ B \ A, cellCorrectionTerm U t n) :=
    summable_sum (fun t _ => cellCorrectionTerm_summable U t)
  have h := ((correctionTerm_summable U A).add hs).tsum_le_tsum
    (correctionTerm_transfer hAB) (correctionTerm_summable U B)
  rw [Summable.tsum_add (correctionTerm_summable U A) hs,
    Summable.tsum_finsetSum (fun t _ => cellCorrectionTerm_summable U t)] at h
  exact h

theorem lostCount_singleton_origin (U P : Diagram) :
    lostCount U {(0, 0)} P = cellLostCount U (0, 0) P := by
  by_cases h0 : (0, 0) ∈ P
  · rw [lostCount, lostStarts, hitStarts_eq_of_origin_mem h0]
    by_cases hfit : (0, 0) ∈ fittingStarts U P <;>
      simp [cellLostCount, h0, hfit, Finset.card_sdiff]
  · have hhit : hitStarts {(0, 0)} P = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨ht, p, hp, htp⟩ := mem_hitStarts.mp ht
      have ht0 : t = (0, 0) := Finset.mem_singleton.mp ht
      have hp0 : p = (0, 0) := by simpa [ht0, shift] using htp
      exact h0 (hp0 ▸ hp)
    simp [lostCount, lostStarts, hhit, cellLostCount, h0]

theorem fittingStarts_translate_rectangle (m n : ℕ) (t : Point) (P : Diagram) :
    t ∈ fittingStarts (faceRectangle m n) P ↔
      (0, 0) ∈ fittingStarts (faceRectangle (m - t.1) (n - t.2)) P := by
  simp only [fittingStarts_faceRectangle, mem_faceRectangle]
  omega

/-- A cell at depth `(a,b)` has exactly the singleton loss for the smaller face rectangle. -/
theorem cellLostCount_rectangle (m n : ℕ) (t : Point) (P : Diagram) :
    cellLostCount (faceRectangle m n) t P =
      lostCount (faceRectangle (m - t.1) (n - t.2)) {(0, 0)} P := by
  rw [lostCount_singleton_origin]
  simp only [cellLostCount, fittingStarts_translate_rectangle m n t P]

theorem cellCorrection_rectangle (m n : ℕ) (t : Point) :
    cellCorrection (faceRectangle m n) t =
      correction (faceRectangle (m - t.1) (n - t.2)) {(0, 0)} := by
  simp only [cellCorrection, correction, cellCorrectionTerm, correctionTerm,
    cellLostSum, lostSum, cellLostCount_rectangle]

theorem cellLostCount_mono_position (m n : ℕ) (P : Diagram) {s t : Point}
    (hx : s.1 ≤ t.1) (hy : s.2 ≤ t.2) :
    cellLostCount (faceRectangle m n) s P ≤
      cellLostCount (faceRectangle m n) t P := by
  have hfit : t ∈ fittingStarts (faceRectangle m n) P →
      s ∈ fittingStarts (faceRectangle m n) P := by
    simp only [fittingStarts_faceRectangle, mem_faceRectangle]
    omega
  unfold cellLostCount
  split_ifs <;> simp_all

theorem cellCorrection_mono_position (m n : ℕ) {s t : Point}
    (hx : s.1 ≤ t.1) (hy : s.2 ≤ t.2) :
    cellCorrection (faceRectangle m n) s ≤ cellCorrection (faceRectangle m n) t := by
  apply (cellCorrectionTerm_summable _ _).tsum_le_tsum _
    (cellCorrectionTerm_summable _ _)
  intro i
  unfold cellCorrectionTerm
  gcongr
  exact Finset.sum_le_sum (fun _ _ => cellLostCount_mono_position m n _ hx hy)

/-- Per-cell transfer in the manuscript's shifted-rectangle form, at the series level. -/
theorem correction_transfer_rectangle (m n : ℕ) {A B : Diagram} (hAB : A ⊆ B) :
    correction (faceRectangle m n) A +
        ∑ t ∈ B \ A, correction (faceRectangle (m - t.1) (n - t.2)) {(0, 0)} ≤
      correction (faceRectangle m n) B := by
  simpa only [cellCorrection_rectangle] using correction_transfer (U := faceRectangle m n) hAB

theorem correction_ge_cell_sum (m n : ℕ) (M : Diagram) :
    (∑ t ∈ M, correction (faceRectangle (m - t.1) (n - t.2)) {(0, 0)}) ≤
      correction (faceRectangle m n) M := by
  simpa using correction_transfer_rectangle m n (A := ∅) (B := M) (Finset.empty_subset _)

theorem correction_ge_card_mul_singleton (m n : ℕ) (M : Diagram) :
    (M.card : ℝ) * correction (faceRectangle m n) {(0, 0)} ≤
      correction (faceRectangle m n) M := by
  have hsum : (∑ _t ∈ M, cellCorrection (faceRectangle m n) (0, 0)) ≤
      ∑ t ∈ M, cellCorrection (faceRectangle m n) t :=
    Finset.sum_le_sum (fun _ _ => cellCorrection_mono_position m n (Nat.zero_le _) (Nat.zero_le _))
  have htrans := correction_transfer (U := faceRectangle m n)
    (A := ∅) (B := M) (Finset.empty_subset _)
  simp only [Finset.sdiff_empty, correction_empty, zero_add] at htrans
  have h := hsum.trans htrans
  simpa only [Finset.sum_const, nsmul_eq_mul, cellCorrection_rectangle,
    Nat.sub_zero] using h

/-- Finite word energy, before the separate log-determinant identification. -/
noncomputable def finiteWordEnergy (U M : Diagram) : ℝ := realEnergy M + correction U M

theorem finiteWordEnergy_transfer (m n : ℕ) {A B : Diagram} (hAB : A ⊆ B) :
    realEnergy B - realEnergy A +
        ∑ t ∈ B \ A, correction (faceRectangle (m - t.1) (n - t.2)) {(0, 0)} ≤
      finiteWordEnergy (faceRectangle m n) B - finiteWordEnergy (faceRectangle m n) A := by
  unfold finiteWordEnergy
  linarith [correction_transfer_rectangle m n hAB]

theorem transpose_faceRectangle (m n : ℕ) :
    transpose (faceRectangle m n) = faceRectangle n m := by
  ext t
  simp only [mem_transpose, mem_faceRectangle, Prod.fst_swap, Prod.snd_swap, and_comm]

theorem fittingStarts_transpose (U P : Diagram) :
    fittingStarts (transpose U) (transpose P) = transpose (fittingStarts U P) := by
  ext t
  simp only [mem_fittingStarts, mem_transpose]
  constructor
  · rintro ⟨ht, hf⟩
    refine ⟨ht, ?_⟩
    intro p hp
    simpa [shift] using hf p.swap (by simpa using hp)
  · rintro ⟨ht, hf⟩
    refine ⟨ht, ?_⟩
    intro p hp
    exact hf p.swap hp

theorem lostCount_transpose (U M P : Diagram) :
    lostCount (transpose U) (transpose M) (transpose P) = lostCount U M P := by
  have hset : lostStarts (transpose U) (transpose M) (transpose P) =
      transpose (lostStarts U M P) := by
    unfold lostStarts
    rw [hitStarts_transpose, fittingStarts_transpose]
    ext t
    simp
  simp only [lostCount, hset, card_transpose]

theorem normalized_transpose {P : Diagram} (hP : IsNormalized P) :
    IsNormalized (transpose P) := by
  obtain ⟨p, hp, hx⟩ := hP.1
  obtain ⟨q, hq, hy⟩ := hP.2
  exact ⟨⟨q.swap, by simpa using hq, hy⟩, ⟨p.swap, by simpa using hp, hx⟩⟩

theorem lostCount_verticalStrip_convex (m n k : ℕ) {P : Diagram} (hP : IsNormalized P) :
    2 * lostCount (faceRectangle m n) (transpose (horizontalStrip (k + 1))) P ≤
      lostCount (faceRectangle m n) (transpose (horizontalStrip k)) P +
        lostCount (faceRectangle m n) (transpose (horizontalStrip (k + 2))) P := by
  have heq (j : ℕ) :
      lostCount (faceRectangle m n) (transpose (horizontalStrip j)) P =
        lostCount (faceRectangle n m) (horizontalStrip j) (transpose P) := by
    simpa only [transpose_faceRectangle, transpose_transpose] using
      lostCount_transpose (faceRectangle n m) (horizontalStrip j) (transpose P)
  simp only [heq]
  exact lostCount_strip_convex n m k (normalized_transpose hP)

theorem correctionTerm_verticalStrip_convex (m n k i : ℕ) :
    2 * correctionTerm (faceRectangle m n) (transpose (horizontalStrip (k + 1))) i ≤
      correctionTerm (faceRectangle m n) (transpose (horizontalStrip k)) i +
        correctionTerm (faceRectangle m n) (transpose (horizontalStrip (k + 2))) i := by
  unfold correctionTerm
  rw [← mul_div_assoc, ← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (ClosedWord (i + 1))))
    (fun w _ => lostCount_verticalStrip_convex m n k (normalizedVisited_isNormalized w.val))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  exact_mod_cast h

/-- The vertical-strip version used in `lem:finite-transfer`. -/
theorem correction_verticalStrip_convex (m n k : ℕ) :
    2 * correction (faceRectangle m n) (transpose (horizontalStrip (k + 1))) ≤
      correction (faceRectangle m n) (transpose (horizontalStrip k)) +
        correction (faceRectangle m n) (transpose (horizontalStrip (k + 2))) := by
  have h := ((correctionTerm_summable (faceRectangle m n)
    (transpose (horizontalStrip (k + 1)))).mul_left 2).tsum_le_tsum
    (correctionTerm_verticalStrip_convex m n k)
    ((correctionTerm_summable (faceRectangle m n) (transpose (horizontalStrip k))).add
      (correctionTerm_summable (faceRectangle m n) (transpose (horizontalStrip (k + 2)))))
  rw [tsum_mul_left, Summable.tsum_add
    (correctionTerm_summable (faceRectangle m n) (transpose (horizontalStrip k)))
    (correctionTerm_summable (faceRectangle m n) (transpose (horizontalStrip (k + 2))))] at h
  exact h

/-- An explicit horizontal out-and-back word supplies positive finite corrections. -/
def boundaryWitnessWord (j : ℕ) : Word (2 * j) := fun i => if i.val < j then 0 else 1

def boundaryWitnessPosition (j i : ℕ) : Vertex :=
  if i ≤ j then (i, 0) else ((2 * j : ℤ) - i, 0)

theorem boundaryWitnessPosition_succ (j i : ℕ) (hi : i < 2 * j) :
    boundaryWitnessPosition j (i + 1) = boundaryWitnessPosition j i +
      direction (boundaryWitnessWord j ⟨i, hi⟩) := by
  by_cases hij : i < j
  · simp [boundaryWitnessPosition, boundaryWitnessWord, hij,
      show i ≤ j by omega, show i + 1 ≤ j by omega, direction, Prod.mk_add_mk]
  · by_cases heq : i = j
    · subst i
      simp [boundaryWitnessPosition, boundaryWitnessWord, direction, Prod.mk_add_mk]
      ring
    · simp [boundaryWitnessPosition, boundaryWitnessWord, hij,
        show ¬i ≤ j by omega, show ¬i + 1 ≤ j by omega, direction, Prod.mk_add_mk]
      ring

theorem boundaryWitness_position (j i : ℕ) (hi : i ≤ 2 * j) :
    position (boundaryWitnessWord j) i = boundaryWitnessPosition j i := by
  induction i with
  | zero => simp [boundaryWitnessPosition]; rfl
  | succ i ih =>
    rw [position_succ _ (by omega), ih (by omega)]
    exact (boundaryWitnessPosition_succ j i (by omega)).symm

theorem boundaryWitness_closed (j : ℕ) : position (boundaryWitnessWord j) (2 * j) = (0, 0) := by
  rw [boundaryWitness_position j (2 * j) le_rfl]
  unfold boundaryWitnessPosition
  (split_ifs <;> push_cast <;> simp_all)
  omega

def boundaryWitness (j : ℕ) : ClosedWord (2 * j) :=
  ⟨boundaryWitnessWord j, boundaryWitness_closed j⟩

theorem boundaryWitness_visit_bounds {j : ℕ} {p : Vertex}
    (hp : p ∈ visited (boundaryWitnessWord j)) : 0 ≤ p.1 ∧ p.2 = 0 := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  have hib : i ≤ 2 * j := by have := Finset.mem_range.mp hi; omega
  rw [boundaryWitness_position j i hib]
  unfold boundaryWitnessPosition
  (split_ifs <;> simp)
  omega

theorem boundaryWitness_minimumX (j : ℕ) :
    minimumX (visited (boundaryWitnessWord j)) (visited_nonempty _) = 0 := by
  apply le_antisymm
  · exact minimumX_le _ (Finset.mem_image.mpr ⟨0, by simp, position_zero _⟩)
  · apply Finset.le_min'
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact (boundaryWitness_visit_bounds hp).1

theorem boundaryWitness_minimumY (j : ℕ) :
    minimumY (visited (boundaryWitnessWord j)) (visited_nonempty _) = 0 := by
  apply le_antisymm
  · exact minimumY_le _ (Finset.mem_image.mpr ⟨0, by simp, position_zero _⟩)
  · apply Finset.le_min'
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    exact (boundaryWitness_visit_bounds hp).2.ge

theorem boundaryWitness_origin_mem (j : ℕ) :
    (0, 0) ∈ normalizedVisited (boundaryWitnessWord j) := by
  refine Finset.mem_image.mpr ⟨(0, 0), ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨0, by simp, position_zero _⟩
  · simp [normalizePoint, boundaryWitness_minimumX, boundaryWitness_minimumY]

theorem boundaryWitness_end_mem (j : ℕ) :
    (j, 0) ∈ normalizedVisited (boundaryWitnessWord j) := by
  refine Finset.mem_image.mpr ⟨((j : ℤ), 0), ?_, ?_⟩
  · refine Finset.mem_image.mpr ⟨j, ?_, ?_⟩
    · simp; omega
    · rw [boundaryWitness_position j j (by omega)]
      simp [boundaryWitnessPosition]
  · simp [normalizePoint, boundaryWitness_minimumX, boundaryWitness_minimumY]

theorem boundaryWitness_cellLostCount (m n : ℕ) :
    cellLostCount (faceRectangle m n) (0, 0)
      (normalizedVisited (boundaryWitnessWord (m + 1))) = 1 := by
  have hnot : (0, 0) ∉ fittingStarts (faceRectangle m n)
      (normalizedVisited (boundaryWitnessWord (m + 1))) := by
    intro hfit
    have h := (mem_fittingStarts.mp hfit).2 (m + 1, 0) (boundaryWitness_end_mem (m + 1))
    simp [shift] at h
  simp [cellLostCount, boundaryWitness_origin_mem, hnot]

theorem singleton_correction_pos (m n : ℕ) :
    0 < correction (faceRectangle m n) {(0, 0)} := by
  have hsum : 0 < cellLostSum (faceRectangle m n) (0, 0) (2 * (m + 1)) := by
    have h := Finset.single_le_sum (f := fun w : ClosedWord (2 * (m + 1)) =>
      cellLostCount (faceRectangle m n) (0, 0) (normalizedVisited w.val))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (boundaryWitness (m + 1)))
    have hw : cellLostCount (faceRectangle m n) (0, 0)
        (normalizedVisited (boundaryWitness (m + 1)).val) = 1 :=
      boundaryWitness_cellLostCount m n
    rw [hw] at h
    exact lt_of_lt_of_le Nat.zero_lt_one h
  have hterm : 0 < cellCorrectionTerm (faceRectangle m n) (0, 0) (2 * m + 1) := by
    unfold cellCorrectionTerm
    apply div_pos
    · exact_mod_cast (show 0 < cellLostSum (faceRectangle m n) (0, 0) (2 * m + 1 + 1) by
        convert hsum using 1)
    · positivity
  have hle := (cellCorrectionTerm_summable (faceRectangle m n) (0, 0)).le_tsum
    (2 * m + 1) (fun _ _ => cellCorrectionTerm_nonneg _ _ _)
  have h := hterm.trans_le hle
  change 0 < cellCorrection (faceRectangle m n) (0, 0) at h
  simpa only [cellCorrection_rectangle, Nat.sub_zero] using h

end SpanningTreeIsoperimetry.CornerEnergy





