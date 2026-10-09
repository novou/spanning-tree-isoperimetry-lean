import SpanningTreeIsoperimetry.PolarizationTrace

/-! Ordinary trace polarization for every translated diagonal used by the paper. -/
namespace SpanningTreeIsoperimetry.Polarization

theorem adjacencyKernel_invariant_of_adj (reflect : Vertex → Vertex)
    (ha : ∀ x y, lattice.Adj (reflect x) (reflect y) ↔ lattice.Adj x y) (x y : Vertex) :
    adjacencyKernel (reflect x) (reflect y) = adjacencyKernel x y := by
  classical
  by_cases h : lattice.Adj x y
  · simp [adjacencyKernel, h, (ha x y).mpr h]
  · have hn : ¬lattice.Adj (reflect x) (reflect y) := fun h' => h ((ha x y).mp h')
    simp [adjacencyKernel, h, hn]

theorem fold_preferred_or_fixed (reflect : Vertex → Vertex) (preferred : Vertex → Prop)
    (_hr : Function.Involutive reflect)
    (hside : ∀ x, preferred (reflect x) ↔ ¬preferred x ∧ reflect x ≠ x) (x : Vertex) :
    preferred (foldToPreferred reflect preferred x) ∨
      reflect (foldToPreferred reflect preferred x) = foldToPreferred reflect preferred x := by
  classical
  by_cases hp : preferred x
  · simp [foldToPreferred, hp]
  · by_cases hfix : reflect x = x
    · simp [foldToPreferred, hp, hfix]
    · have hpr := (hside x).mpr ⟨hp, hfix⟩
      simp [foldToPreferred, hp, hpr]

theorem ordinary_moments_of_no_cross (U : Domain) (reflect : Vertex → Vertex)
    (preferred : Vertex → Prop) [DecidablePred preferred] (hr : Function.Involutive reflect)
    (hside : ∀ x, preferred (reflect x) ↔ ¬preferred x ∧ reflect x ≠ x)
    (ha : ∀ x y, lattice.Adj (reflect x) (reflect y) ↔ lattice.Adj x y)
    (hcross : ∀ x y, preferred x → preferred y → ¬lattice.Adj x (reflect y)) (n : ℕ) :
    Matrix.trace (domainKernel adjacencyKernel U ^ n) ≤
      Matrix.trace (domainKernel adjacencyKernel (polarized U reflect preferred) ^ n) := by
  classical
  have hK := adjacencyKernel_invariant_of_adj reflect ha
  apply domainKernel_polarization_moments U reflect preferred hr hside adjacencyKernel hK
    adjacencyKernel_nonneg
  intro x y
  rcases fold_preferred_or_fixed reflect preferred hr hside x with hx | hx
  · rcases fold_preferred_or_fixed reflect preferred hr hside y with hy | hy
    · have hn := hcross _ _ hx hy
      change (if lattice.Adj _ _ then (1 : ℝ) else 0) ≤ adjacencyKernel _ _
      rw [ite_eq_right hn]
      exact adjacencyKernel_nonneg _ _
    · rw [hy]
  · exact le_of_eq (by simpa only [hx] using (hK
      (foldToPreferred reflect preferred x) (foldToPreferred reflect preferred y)))

def shiftedDiagonalReflection (c : ℤ) (x : Vertex) : Vertex := (x.2 - c, x.1 + c)

@[simp] theorem shiftedDiagonal_involutive (c : ℤ) (x : Vertex) :
    shiftedDiagonalReflection c (shiftedDiagonalReflection c x) = x := by
  ext <;> simp [shiftedDiagonalReflection]

theorem shiftedDiagonal_side (c : ℤ) (x : Vertex) :
    (shiftedDiagonalReflection c x).1 + c < (shiftedDiagonalReflection c x).2 ↔
      ¬x.1 + c < x.2 ∧ shiftedDiagonalReflection c x ≠ x := by
  have heq : shiftedDiagonalReflection c x = x ↔ x.1 + c = x.2 := by
    constructor
    · intro h
      have h' := congrArg Prod.snd h
      exact h'
    · intro h
      apply Prod.ext <;> dsimp [shiftedDiagonalReflection] <;> omega
  change (x.2 - c) + c < x.1 + c ↔ _
  rw [ne_eq, heq]
  omega

theorem shiftedDiagonal_adj (c : ℤ) (x y : Vertex) :
    lattice.Adj (shiftedDiagonalReflection c x) (shiftedDiagonalReflection c y) ↔
      lattice.Adj x y := by
  change (x.2 - c = y.2 - c ∧ |(x.1 + c) - (y.1 + c)| = 1) ∨
    (x.1 + c = y.1 + c ∧ |(x.2 - c) - (y.2 - c)| = 1) ↔ _
  have h₁ : x.2 - c = y.2 - c ↔ x.2 = y.2 := by omega
  have h₂ : x.1 + c = y.1 + c ↔ x.1 = y.1 := by omega
  rw [h₁, h₂, show (x.1 + c) - (y.1 + c) = x.1 - y.1 by ring,
    show (x.2 - c) - (y.2 - c) = x.2 - y.2 by ring]
  exact or_comm

theorem shiftedDiagonal_no_cross (c : ℤ) (x y : Vertex)
    (hx : x.1 + c < x.2) (hy : y.1 + c < y.2) :
    ¬lattice.Adj x (shiftedDiagonalReflection c y) := by
  change ¬((x.1 = y.2 - c ∧ |x.2 - (y.1 + c)| = 1) ∨
    (x.2 = y.1 + c ∧ |x.1 - (y.2 - c)| = 1))
  rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;>
    rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at h₂ <;> omega

theorem shiftedDiagonal_adjacency_moments (U : Domain) (c : ℤ) (n : ℕ) :
    Matrix.trace (domainKernel adjacencyKernel U ^ n) ≤
      Matrix.trace (domainKernel adjacencyKernel
        (polarized U (shiftedDiagonalReflection c) (fun x => x.1 + c < x.2)) ^ n) :=
  ordinary_moments_of_no_cross U _ _ (shiftedDiagonal_involutive c)
    (shiftedDiagonal_side c) (shiftedDiagonal_adj c) (shiftedDiagonal_no_cross c) n

def antiDiagonalReflection (c : ℤ) (x : Vertex) : Vertex := (c - x.2, c - x.1)

@[simp] theorem antiDiagonal_involutive (c : ℤ) (x : Vertex) :
    antiDiagonalReflection c (antiDiagonalReflection c x) = x := by
  ext <;> simp [antiDiagonalReflection]

theorem antiDiagonal_side (c : ℤ) (x : Vertex) :
    (antiDiagonalReflection c x).1 + (antiDiagonalReflection c x).2 < c ↔
      ¬x.1 + x.2 < c ∧ antiDiagonalReflection c x ≠ x := by
  have heq : antiDiagonalReflection c x = x ↔ x.1 + x.2 = c := by
    constructor
    · intro h
      have h' := congrArg Prod.snd h
      dsimp [antiDiagonalReflection] at h'
      omega
    · intro h
      apply Prod.ext <;> dsimp [antiDiagonalReflection] <;> omega
  change (c - x.2) + (c - x.1) < c ↔ _
  rw [ne_eq, heq]
  omega

theorem antiDiagonal_adj (c : ℤ) (x y : Vertex) :
    lattice.Adj (antiDiagonalReflection c x) (antiDiagonalReflection c y) ↔ lattice.Adj x y := by
  change (c - x.2 = c - y.2 ∧ |(c - x.1) - (c - y.1)| = 1) ∨
    (c - x.1 = c - y.1 ∧ |(c - x.2) - (c - y.2)| = 1) ↔ _
  have h₁ : c - x.2 = c - y.2 ↔ x.2 = y.2 := by omega
  have h₂ : c - x.1 = c - y.1 ↔ x.1 = y.1 := by omega
  rw [h₁, h₂, show (c - x.1) - (c - y.1) = -(x.1 - y.1) by ring,
    show (c - x.2) - (c - y.2) = -(x.2 - y.2) by ring, abs_neg, abs_neg]
  exact or_comm

theorem antiDiagonal_no_cross (c : ℤ) (x y : Vertex)
    (hx : x.1 + x.2 < c) (hy : y.1 + y.2 < c) :
    ¬lattice.Adj x (antiDiagonalReflection c y) := by
  change ¬((x.1 = c - y.2 ∧ |x.2 - (c - y.1)| = 1) ∨
    (x.2 = c - y.1 ∧ |x.1 - (c - y.2)| = 1))
  rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;>
    rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)] at h₂ <;> omega

theorem antiDiagonal_adjacency_moments (U : Domain) (c : ℤ) (n : ℕ) :
    Matrix.trace (domainKernel adjacencyKernel U ^ n) ≤
      Matrix.trace (domainKernel adjacencyKernel
        (polarized U (antiDiagonalReflection c) (fun x => x.1 + x.2 < c)) ^ n) :=
  ordinary_moments_of_no_cross U _ _ (antiDiagonal_involutive c)
    (antiDiagonal_side c) (antiDiagonal_adj c) (antiDiagonal_no_cross c) n

theorem holdingKernel_swap (x y : Vertex) : holdingKernel x.swap y.swap = holdingKernel x y := by
  have heq : x.swap = y.swap ↔ x = y := Prod.swap_injective.eq_iff
  simp only [holdingKernel, heq, diagonal_adjacencyKernel_invariant]

def verticalReflection (c : ℤ) (x : Vertex) : Vertex := (c - x.1, x.2)

@[simp] theorem vertical_involutive (c : ℤ) (x : Vertex) :
    verticalReflection c (verticalReflection c x) = x := by
  ext <;> simp [verticalReflection]

theorem vertical_preferred_side (c : ℤ) (x : Vertex) :
    c < 2 * (verticalReflection c x).1 ↔ ¬c < 2 * x.1 ∧ verticalReflection c x ≠ x := by
  have heq : verticalReflection c x = x ↔ c = 2 * x.1 := by
    constructor
    · intro h
      have h' := congrArg Prod.fst h
      dsimp [verticalReflection] at h'
      omega
    · intro h
      (apply Prod.ext <;> dsimp [verticalReflection])
      omega
  change c < 2 * (c - x.1) ↔ _
  rw [ne_eq, heq]
  omega

theorem vertical_holdingKernel_invariant (c : ℤ) (x y : Vertex) :
    holdingKernel (verticalReflection c x) (verticalReflection c y) = holdingKernel x y := by
  change holdingKernel (axialReflection c x.swap).swap (axialReflection c y.swap).swap = _
  rw [holdingKernel_swap, axial_holdingKernel_invariant, holdingKernel_swap]

theorem vertical_holdingKernel_closed_domination (c : ℤ) (x y : Vertex)
    (hx : c ≤ 2 * x.1) (hy : c ≤ 2 * y.1) :
    holdingKernel x (verticalReflection c y) ≤ holdingKernel x y := by
  calc
    holdingKernel x (verticalReflection c y) = holdingKernel x.swap (axialReflection c y.swap) :=
      (holdingKernel_swap x (verticalReflection c y)).symm
    _ ≤ holdingKernel x.swap y.swap := axial_holdingKernel_closed_domination c x.swap y.swap hx hy
    _ = holdingKernel x y := holdingKernel_swap x y

theorem vertical_fold_preferred (c : ℤ) (x : Vertex) :
    c ≤ 2 * (foldToPreferred (verticalReflection c) (fun y => c < 2 * y.1) x).1 := by
  classical
  unfold foldToPreferred
  split_ifs with h <;> (try dsimp [verticalReflection]) <;> omega

theorem vertical_holding_moments (U : Domain) (c : ℤ) (n : ℕ) :
    Matrix.trace (domainKernel holdingKernel U ^ n) ≤
      Matrix.trace (domainKernel holdingKernel
        (polarized U (verticalReflection c) (fun x => c < 2 * x.1)) ^ n) := by
  apply domainKernel_polarization_moments U (verticalReflection c) (fun x => c < 2 * x.1)
    (vertical_involutive c) (vertical_preferred_side c) holdingKernel
    (vertical_holdingKernel_invariant c) holdingKernel_nonneg
  intro x y
  exact vertical_holdingKernel_closed_domination c _ _ (vertical_fold_preferred c x) (vertical_fold_preferred c y)

theorem holdingKernel_invariant_of_adj (reflect : Vertex → Vertex)
    (hr : Function.Involutive reflect)
    (ha : ∀ x y, lattice.Adj (reflect x) (reflect y) ↔ lattice.Adj x y) (x y : Vertex) :
    holdingKernel (reflect x) (reflect y) = holdingKernel x y := by
  have heq : reflect x = reflect y ↔ x = y := hr.injective.eq_iff
  simp only [holdingKernel, heq, adjacencyKernel_invariant_of_adj reflect ha]

theorem holding_moments_of_no_cross (U : Domain) (reflect : Vertex → Vertex)
    (preferred : Vertex → Prop) [DecidablePred preferred] (hr : Function.Involutive reflect)
    (hside : ∀ x, preferred (reflect x) ↔ ¬preferred x ∧ reflect x ≠ x)
    (ha : ∀ x y, lattice.Adj (reflect x) (reflect y) ↔ lattice.Adj x y)
    (hcross : ∀ x y, preferred x → preferred y → ¬lattice.Adj x (reflect y)) (n : ℕ) :
    Matrix.trace (domainKernel holdingKernel U ^ n) ≤
      Matrix.trace (domainKernel holdingKernel (polarized U reflect preferred) ^ n) := by
  classical
  have hK := holdingKernel_invariant_of_adj reflect hr ha
  apply domainKernel_polarization_moments U reflect preferred hr hside holdingKernel hK
    holdingKernel_nonneg
  intro x y
  rcases fold_preferred_or_fixed reflect preferred hr hside x with hx | hx
  · rcases fold_preferred_or_fixed reflect preferred hr hside y with hy | hy
    · have hn := hcross _ _ hx hy
      have hne : foldToPreferred reflect preferred x ≠
          reflect (foldToPreferred reflect preferred y) := by
        intro heq
        have hp : preferred (reflect (foldToPreferred reflect preferred y)) := heq ▸ hx
        exact ((hside _).mp hp).1 hy
      simp only [holdingKernel, adjacencyKernel, ite_eq_right hn, ite_eq_right hne, zero_add]
      split_ifs <;> norm_num
    · rw [hy]
  · exact le_of_eq (by simpa only [hx] using (hK
      (foldToPreferred reflect preferred x) (foldToPreferred reflect preferred y)))

theorem shiftedDiagonal_holding_moments (U : Domain) (c : ℤ) (n : ℕ) :
    Matrix.trace (domainKernel holdingKernel U ^ n) ≤
      Matrix.trace (domainKernel holdingKernel
        (polarized U (shiftedDiagonalReflection c) (fun x => x.1 + c < x.2)) ^ n) :=
  holding_moments_of_no_cross U _ _ (shiftedDiagonal_involutive c)
    (shiftedDiagonal_side c) (shiftedDiagonal_adj c) (shiftedDiagonal_no_cross c) n

theorem antiDiagonal_holding_moments (U : Domain) (c : ℤ) (n : ℕ) :
    Matrix.trace (domainKernel holdingKernel U ^ n) ≤
      Matrix.trace (domainKernel holdingKernel
        (polarized U (antiDiagonalReflection c) (fun x => x.1 + x.2 < c)) ^ n) :=
  holding_moments_of_no_cross U _ _ (antiDiagonal_involutive c)
    (antiDiagonal_side c) (antiDiagonal_adj c) (antiDiagonal_no_cross c) n

end SpanningTreeIsoperimetry.Polarization


