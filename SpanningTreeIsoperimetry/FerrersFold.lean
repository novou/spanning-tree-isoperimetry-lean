import SpanningTreeIsoperimetry.CornerFolds

/-! Actual maximal-block Ferrers folds on integer face domains. -/
namespace SpanningTreeIsoperimetry.CornerFolds

open Polarization StripPolarization Ferrers DomainIsometries
open scoped Classical

/-- Lower preferred half-plane for the shifted diagonal used by a Ferrers fold. -/
theorem shiftedDiagonal_lower_side (c : ℤ) (x : Vertex) :
    (shiftedDiagonalReflection c x).2 < (shiftedDiagonalReflection c x).1 + c ↔
      ¬x.2 < x.1 + c ∧ shiftedDiagonalReflection c x ≠ x := by
  have heq : shiftedDiagonalReflection c x = x ↔ x.1 + c = x.2 := by
    constructor
    · intro h
      have h' := congrArg Prod.snd h
      dsimp [shiftedDiagonalReflection] at h'
      omega
    · intro h
      apply Prod.ext <;> dsimp [shiftedDiagonalReflection] <;> omega
  change x.1 + c < x.2 - c + c ↔ _
  rw [ne_eq, heq]
  omega

theorem shiftedDiagonal_lower_no_cross (c : ℤ) (x y : Vertex)
    (hx : x.2 < x.1 + c) (hy : y.2 < y.1 + c) :
    ¬lattice.Adj x (shiftedDiagonalReflection c y) := by
  change ¬((x.1 = y.2 - c ∧ |x.2 - (y.1 + c)| = 1) ∨
    (x.2 = y.1 + c ∧ |x.1 - (y.2 - c)| = 1))
  rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;>
    rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at h₂ <;> omega

theorem shiftedDiagonal_lower_moments (U : Domain) (c : ℤ) (n : ℕ) :
    Matrix.trace (domainKernel adjacencyKernel U ^ n) ≤
      Matrix.trace (domainKernel adjacencyKernel
        (polarized U (shiftedDiagonalReflection c) (fun x => x.2 < x.1 + c)) ^ n) :=
  ordinary_moments_of_no_cross U _ _ (shiftedDiagonal_involutive c)
    (shiftedDiagonal_lower_side c) (shiftedDiagonal_adj c) (shiftedDiagonal_lower_no_cross c) n

theorem shiftedDiagonal_lower_determinant (U : Domain) (c : ℤ) (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (polarized U (shiftedDiagonalReflection c) (fun x => x.2 < x.1 + c)) z ≤
      faceDeterminant U z :=
  adjacency_determinant_of_domain_moments U _
    (card_polarized (shiftedDiagonal_involutive c) (fun x => x.2 < x.1 + c)
      (shiftedDiagonal_lower_side c)).symm
    (fun i => shiftedDiagonal_lower_moments U c (i + 1)) z hz

/-- Deleting complete reflection orbits commutes with polarization. -/
theorem polarized_remove_orbits (U D : Domain) (f : Vertex → Vertex)
    (hf : Function.Involutive f) (preferred : Vertex → Prop) [DecidablePred preferred] :
    polarized (U \ (D ∪ D.image f)) f preferred =
      polarized U f preferred \ (D ∪ D.image f) := by
  ext x
  simp only [mem_polarized hf, Finset.mem_sdiff, Finset.mem_union,
    mem_image_involution hf, hf x]
  by_cases hD : x ∈ D <;> by_cases hR : f x ∈ D <;>
    by_cases hp : preferred x <;> simp [hD, hR, hp]

/-- Maximal rectangular block absorbed by the new hull. -/
def absorbedBlock (u t c : ℕ) : Domain :=
  Finset.Ico ((u : ℤ) - t) u ×ˢ Finset.Ico (0 : ℤ) c

@[simp] theorem mem_absorbedBlock {u t c : ℕ} {x : Vertex} :
    x ∈ absorbedBlock u t c ↔ (u : ℤ) - t ≤ x.1 ∧ x.1 < u ∧ 0 ≤ x.2 ∧ x.2 < c := by
  simp only [absorbedBlock, Finset.mem_product, Finset.mem_Ico]
  tauto

/-- The full-rectangle fold removes exactly the maximal corner block. -/
theorem polarize_ferrers_rectangle {u v t : ℕ} (huv : u ≤ v) (ht : t ≤ u) :
    polarized (rectangle (u - t) (v + t)) (shiftedDiagonalReflection (v - u + t : ℕ))
      (fun x => x.2 < x.1 + (v - u + t : ℕ)) =
      rectangle u v \ absorbedBlock u t (v - u + t) := by
  ext x
  rw [mem_polarized (shiftedDiagonal_involutive _)]
  simp only [mem_rectangle, Finset.mem_sdiff, mem_absorbedBlock, shiftedDiagonalReflection]
  split_ifs <;> omega

/-- Candidate obtained by removing the actual defect and its reflected image. -/
def ferrersFoldCandidate (u v t : ℕ) (M : Diagram) : Domain :=
  rectangle (u - t) (v + t) \
    (bottomRightDefect u M ∪
      (bottomRightDefect u M).image (shiftedDiagonalReflection (v - u + t : ℕ)))

/-- Every defect point and its mirror occupy separate old/new hull pieces. -/
theorem ferrers_reflected_defect_outside {u v t : ℕ} {M : Diagram} (huv : u ≤ v)
    (hsplit : ∀ p ∈ M, p.1 < t ∨ p.2 < v - u + t) :
    Disjoint (rectangle u v)
      ((bottomRightDefect u M).image (shiftedDiagonalReflection (v - u + t : ℕ))) := by
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx'
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  have hp' := hsplit p hp
  have hrect := mem_rectangle.mp hx
  dsimp [shiftedDiagonalReflection, verticalReflection, SquareMaximality.Boundary.ofNatPoint] at hrect
  omega

theorem absorbedBlock_subset_defect {u t c : ℕ} {M : Diagram} (hM : IsFerrers M)
    (ht : 0 < t) (hc : 0 < c) (hcorner : (t - 1, c - 1) ∈ M) :
    absorbedBlock u t c ⊆ bottomRightDefect u M := by
  intro x hx
  have hb := mem_absorbedBlock.mp hx
  apply Finset.mem_image.mpr
  refine ⟨((u : ℤ) - 1 - x.1, x.2), ?_, ?_⟩
  · apply Finset.mem_image.mpr
    refine ⟨(((u : ℤ) - 1 - x.1).toNat, x.2.toNat), ?_, ?_⟩
    · exact hM _ hcorner _ (by omega) (by omega)
    · apply Prod.ext <;> dsimp [SquareMaximality.Boundary.ofNatPoint] <;> omega
  · apply Prod.ext <;> dsimp [verticalReflection] <;> omega

/-- Literal polarization identity for a Ferrers defect at an actual maximal block. -/
theorem polarize_ferrersFoldCandidate {u v t : ℕ} {M : Diagram} (hM : IsFerrers M)
    (huv : u ≤ v) (ht0 : 0 < t) (htu : t ≤ u)
    (hcorner : (t - 1, v - u + t - 1) ∈ M)
    (hsplit : ∀ p ∈ M, p.1 < t ∨ p.2 < v - u + t) :
    polarized (ferrersFoldCandidate u v t M) (shiftedDiagonalReflection (v - u + t : ℕ))
      (fun x => x.2 < x.1 + (v - u + t : ℕ)) =
      rectangle u v \ bottomRightDefect u M := by
  unfold ferrersFoldCandidate
  rw [polarized_remove_orbits _ _ _ (shiftedDiagonal_involutive _), polarize_ferrers_rectangle huv htu]
  have hB := absorbedBlock_subset_defect (u := u) hM ht0 (show 0 < v - u + t by omega) hcorner
  have hD := Finset.disjoint_left.mp (ferrers_reflected_defect_outside huv hsplit)
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨⟨hx, _⟩, hnot⟩
    exact ⟨hx, fun hm => hnot (Or.inl hm)⟩
  · rintro ⟨hx, hm⟩
    exact ⟨⟨hx, fun hb => hm (hB hb)⟩, fun h => h.elim hm (hD hx)⟩

/-- The actual maximal block supplies every geometric premise of the fold.
This endpoint concerns finite face determinants; primal realization is separate. -/
theorem exists_ferrers_fold_determinant {u v : ℕ} {M : Diagram} (hM : IsFerrers M)
    (huv : u ≤ v) (hcard : M.card ≤ u) (hheight : (0, v - u) ∈ M) :
    ∃ t : ℕ, 0 < t ∧ t ≤ u ∧ t * (v - u + t) ≤ M.card ∧
      (ferrersFoldCandidate u v t M).card = (rectangle u v \ bottomRightDefect u M).card ∧
      ∀ z : ℝ, 4 ≤ z → faceDeterminant (rectangle u v \ bottomRightDefect u M) z ≤
        faceDeterminant (ferrersFoldCandidate u v t M) z := by
  obtain ⟨t, ht0, hcorner, _, hsplit, hblockCard⟩ := exists_maximal_ferrers_block hM (v - u) hheight
  have htu : t ≤ u := by
    have h := (ferrers_coordinate_lt_card hM hcorner).1
    omega
  have hpol := polarize_ferrersFoldCandidate hM huv ht0 htu hcorner hsplit
  refine ⟨t, ht0, htu, hblockCard, ?_, ?_⟩
  · have hc := card_polarized (U := ferrersFoldCandidate u v t M)
      (shiftedDiagonal_involutive (v - u + t : ℕ)) (fun x => x.2 < x.1 + (v - u + t : ℕ))
      (shiftedDiagonal_lower_side (v - u + t : ℕ))
    rw [hpol] at hc
    exact hc.symm
  · intro z hz
    have h := shiftedDiagonal_lower_determinant (ferrersFoldCandidate u v t M) (v - u + t : ℕ) z hz
    rw [hpol] at h
    exact h

/-- Ferrers tail after removing the first `t` columns. -/
def ferrersTailX (M : Diagram) (t : ℕ) : Diagram :=
  (M.filter (fun p => t ≤ p.1)).image fun p => (p.1 - t, p.2)

/-- Ferrers tail after removing the first `c` rows. -/
def ferrersTailY (M : Diagram) (c : ℕ) : Diagram :=
  (M.filter (fun p => c ≤ p.2)).image fun p => (p.1, p.2 - c)

@[simp] theorem mem_ferrersTailX {M : Diagram} {t : ℕ} {p : Point} :
    p ∈ ferrersTailX M t ↔ (p.1 + t, p.2) ∈ M := by
  constructor
  · intro hp
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hp
    have hq' := Finset.mem_filter.mp hq
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    have he : (p.1 + t, p.2) = q := by ext <;> dsimp at h1 h2 ⊢ <;> omega
    rw [he]
    exact hq'.1
  · intro hp
    apply Finset.mem_image.mpr
    refine ⟨(p.1 + t, p.2), Finset.mem_filter.mpr ⟨hp, by omega⟩, ?_⟩
    ext <;> simp

@[simp] theorem mem_ferrersTailY {M : Diagram} {c : ℕ} {p : Point} :
    p ∈ ferrersTailY M c ↔ (p.1, p.2 + c) ∈ M := by
  constructor
  · intro hp
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hp
    have hq' := Finset.mem_filter.mp hq
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    have he : (p.1, p.2 + c) = q := by ext <;> dsimp at h1 h2 ⊢ <;> omega
    rw [he]
    exact hq'.1
  · intro hp
    apply Finset.mem_image.mpr
    refine ⟨(p.1, p.2 + c), Finset.mem_filter.mpr ⟨hp, by omega⟩, ?_⟩
    ext <;> simp

theorem ferrersTailX_isFerrers {M : Diagram} (hM : IsFerrers M) (t : ℕ) :
    IsFerrers (ferrersTailX M t) := by
  intro p hp q h1 h2
  rw [mem_ferrersTailX] at hp ⊢
  exact hM _ hp _ (by omega) h2

theorem ferrersTailY_isFerrers {M : Diagram} (hM : IsFerrers M) (c : ℕ) :
    IsFerrers (ferrersTailY M c) := by
  intro p hp q h1 h2
  rw [mem_ferrersTailY] at hp ⊢
  exact hM _ hp _ h1 (by omega)

theorem mem_integerFaces_iff {M : Diagram} {x : Vertex} :
    x ∈ integerFaces M ↔ 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ (x.1.toNat, x.2.toNat) ∈ M := by
  constructor
  · intro hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    simpa [SquareMaximality.Boundary.ofNatPoint] using hp
  · rintro ⟨h1, h2, hm⟩
    exact Finset.mem_image.mpr ⟨(x.1.toNat, x.2.toNat), hm,
      by ext <;> simp [SquareMaximality.Boundary.ofNatPoint, h1, h2]⟩

theorem mem_bottomRightDefect_iff {u : ℕ} {M : Diagram} {x : Vertex} :
    x ∈ bottomRightDefect u M ↔
      x.1 ≤ (u : ℤ) - 1 ∧ 0 ≤ x.2 ∧ (((u : ℤ) - 1 - x.1).toNat, x.2.toNat) ∈ M := by
  rw [bottomRightDefect, mem_image_involution (vertical_involutive _), mem_integerFaces_iff]
  dsimp [verticalReflection]
  constructor <;> intro h <;> exact ⟨by omega, h.2.1, h.2.2⟩

/-- Literal top-left placement in a face rectangle of height `v`. -/
def topLeftDefect (v : ℕ) (M : Diagram) : Domain :=
  (integerFaces M).image (axialReflection ((v : ℤ) - 1))

theorem mem_topLeftDefect_iff {v : ℕ} {M : Diagram} {x : Vertex} :
    x ∈ topLeftDefect v M ↔
      0 ≤ x.1 ∧ x.2 ≤ (v : ℤ) - 1 ∧ (x.1.toNat, ((v : ℤ) - 1 - x.2).toNat) ∈ M := by
  rw [topLeftDefect, mem_image_involution (axialReflection_involutive _), mem_integerFaces_iff]
  dsimp [axialReflection]
  constructor <;> intro h <;> exact ⟨h.1, by omega, h.2.2⟩

/-- The candidate deletions are precisely the left tail and reflected upper tail,
placed at opposite corners. This identity uses actual Ferrers tail diagrams. -/
theorem ferrersFoldCandidate_eq_two_corners {u v t : ℕ} (M : Diagram)
    (huv : u ≤ v) (htu : t ≤ u) :
    ferrersFoldCandidate u v t M = rectangle (u - t) (v + t) \
      (bottomRightDefect (u - t) (ferrersTailX M t) ∪
        topLeftDefect (v + t) (transpose (ferrersTailY M (v - u + t)))) := by
  ext x
  simp only [ferrersFoldCandidate, Finset.mem_sdiff, Finset.mem_union]
  by_cases hx : x ∈ rectangle (u - t) (v + t)
  · have hb := mem_rectangle.mp hx
    have h1 : x ∈ bottomRightDefect u M ↔
        x ∈ bottomRightDefect (u - t) (ferrersTailX M t) := by
      rw [mem_bottomRightDefect_iff, mem_bottomRightDefect_iff, mem_ferrersTailX]
      have he : (((u - t : ℕ) : ℤ) - 1 - x.1).toNat + t = ((u : ℤ) - 1 - x.1).toNat := by omega
      rw [he]
      have hu1 : x.1 ≤ (u : ℤ) - 1 := by omega
      have hut1 : x.1 ≤ (u - t : ℕ) - (1 : ℤ) := by omega
      simp only [hu1, hut1, hb.2.2.1, true_and]
    have h2 : x ∈ (bottomRightDefect u M).image (shiftedDiagonalReflection (v - u + t : ℕ)) ↔
        x ∈ topLeftDefect (v + t) (transpose (ferrersTailY M (v - u + t))) := by
      rw [mem_image_involution (shiftedDiagonal_involutive _), mem_bottomRightDefect_iff,
        mem_topLeftDefect_iff, mem_transpose, mem_ferrersTailY]
      dsimp [shiftedDiagonalReflection]
      have he1 : ((u : ℤ) - 1 - (x.2 - (v - u + t : ℕ))).toNat =
          ((v + t : ℕ) - (1 : ℤ) - x.2).toNat := by congr 1; omega
      have he2 : (x.1 + (v - u + t : ℕ)).toNat = x.1.toNat + (v - u + t) := by omega
      simp only [Nat.cast_add] at he1 he2
      rw [he1, he2]
      have hu1 : x.2 - (v - u + t : ℕ) ≤ (u : ℤ) - 1 := by omega
      have hu2 : 0 ≤ x.1 + (v - u + t : ℕ) := by omega
      have hv1 : x.2 ≤ (v + t : ℕ) - (1 : ℤ) := by omega
      simp only [Nat.cast_add] at hu1 hu2 hv1
      simp only [hu1, hu2, hb.1, hv1, true_and]
    simp only [hx, h1, h2]
  · simp only [hx, false_and]

theorem card_ferrersTailX (M : Diagram) (t : ℕ) :
    (ferrersTailX M t).card = (M.filter (fun p => t ≤ p.1)).card := by
  apply Finset.card_image_iff.mpr
  intro p hp q hq heq
  have hp' := (Finset.mem_filter.mp hp).2
  have hq' := (Finset.mem_filter.mp hq).2
  have h1 := congrArg Prod.fst heq
  have h2 := congrArg Prod.snd heq
  apply Prod.ext <;> dsimp at h1 h2 ⊢ <;> omega

theorem card_ferrersTailY (M : Diagram) (c : ℕ) :
    (ferrersTailY M c).card = (M.filter (fun p => c ≤ p.2)).card := by
  apply Finset.card_image_iff.mpr
  intro p hp q hq heq
  have hp' := (Finset.mem_filter.mp hp).2
  have hq' := (Finset.mem_filter.mp hq).2
  have h1 := congrArg Prod.fst heq
  have h2 := congrArg Prod.snd heq
  apply Prod.ext <;> dsimp at h1 h2 ⊢ <;> omega

/-- The two explicit tails contain exactly the vacancies outside the block. -/
theorem ferrers_tails_card {M : Diagram} {t c : ℕ}
    (hblock : (Finset.range t ×ˢ Finset.range c) ⊆ M)
    (hsplit : ∀ p ∈ M, p.1 < t ∨ p.2 < c) :
    (ferrersTailX M t).card + (ferrersTailY M c).card = M.card - t * c := by
  let B := Finset.range t ×ˢ Finset.range c
  let L := M.filter (fun p => t ≤ p.1)
  let U := M.filter (fun p => c ≤ p.2)
  have hdisjBL : Disjoint B L := by
    apply Finset.disjoint_left.mpr
    intro p hb hl
    simp only [B, Finset.mem_product, Finset.mem_range] at hb
    have hl' := (Finset.mem_filter.mp hl).2
    omega
  have hdisjBU : Disjoint B U := by
    apply Finset.disjoint_left.mpr
    intro p hb hu
    simp only [B, Finset.mem_product, Finset.mem_range] at hb
    have hu' := (Finset.mem_filter.mp hu).2
    omega
  have hdisjLU : Disjoint L U := by
    apply Finset.disjoint_left.mpr
    intro p hl hu
    have hl' := Finset.mem_filter.mp hl
    have hu' := Finset.mem_filter.mp hu
    have h := hsplit p hl'.1
    omega
  have heq : M = (B ∪ L) ∪ U := by
    ext p
    simp only [Finset.mem_union, B, L, U, Finset.mem_product, Finset.mem_range, Finset.mem_filter]
    constructor
    · intro hp
      by_cases ht : t ≤ p.1
      · exact Or.inl (Or.inr ⟨hp, ht⟩)
      · by_cases hc : c ≤ p.2
        · exact Or.inr ⟨hp, hc⟩
        · exact Or.inl (Or.inl ⟨by omega, by omega⟩)
    · rintro ((hb | hl) | hu)
      · exact hblock (Finset.mem_product.mpr ⟨Finset.mem_range.mpr hb.1, Finset.mem_range.mpr hb.2⟩)
      · exact hl.1
      · exact hu.1
  have hcard := congrArg Finset.card heq
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisjBU, hdisjLU⟩),
    Finset.card_union_of_disjoint hdisjBL] at hcard
  simp only [B, Finset.card_product, Finset.card_range] at hcard
  rw [card_ferrersTailX, card_ferrersTailY]
  change L.card + U.card = _
  omega

/-- A maximal fold exists with actual opposite Ferrers tails and the required
smaller total vacancy count on a strictly more elongated face rectangle. -/
theorem exists_ferrers_fold_geometry {u v : ℕ} {M : Diagram} (hM : IsFerrers M)
    (hu : 2 ≤ u) (huv : u ≤ v) (hcard : M.card ≤ u) (hheight : (0, v - u) ∈ M) :
    ∃ t : ℕ, 0 < t ∧ t < u ∧
      IsFerrers (ferrersTailX M t) ∧ IsFerrers (transpose (ferrersTailY M (v - u + t))) ∧
      (ferrersTailX M t).card + (transpose (ferrersTailY M (v - u + t))).card =
        M.card - t * (v - u + t) ∧
      M.card - t * (v - u + t) ≤ u - t ∧
      polarized (ferrersFoldCandidate u v t M) (shiftedDiagonalReflection (v - u + t : ℕ))
        (fun x => x.2 < x.1 + (v - u + t : ℕ)) = rectangle u v \ bottomRightDefect u M := by
  obtain ⟨t, ht0, hcorner, hblock, hsplit, hblockCard⟩ := exists_maximal_ferrers_block hM (v - u) hheight
  have htu : t ≤ u := by
    have h := (ferrers_coordinate_lt_card hM hcorner).1
    omega
  have hmul : t * t ≤ t * (v - u + t) := Nat.mul_le_mul_left t (by omega)
  have htlt : t < u := by nlinarith
  have htc : t ≤ t * (v - u + t) := by nlinarith
  refine ⟨t, ht0, htlt, ferrersTailX_isFerrers hM t,
    transpose_isFerrers (ferrersTailY_isFerrers hM _), ?_, ?_,
    polarize_ferrersFoldCandidate hM huv ht0 htu hcorner hsplit⟩
  · rw [card_transpose]
    exact ferrers_tails_card hblock hsplit
  · omega

end SpanningTreeIsoperimetry.CornerFolds
