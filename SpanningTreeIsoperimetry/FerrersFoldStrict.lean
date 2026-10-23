module

public import SpanningTreeIsoperimetry.FerrersFold

@[expose] public section

/-! Strict geometric witnesses for maximal-block Ferrers folds. -/
namespace SpanningTreeIsoperimetry.CornerFolds

open Polarization StripPolarization Ferrers DomainIsometries
open scoped Classical

def ferrersWidth (M : Diagram) : ℕ := M.sup (fun p => p.1 + 1)
def ferrersHeight (M : Diagram) : ℕ := M.sup (fun p => p.2 + 1)

theorem ferrers_extent_bounds {M : Diagram} {p : Point} (hp : p ∈ M) :
    p.1 < ferrersWidth M ∧ p.2 < ferrersHeight M := by
  have h1 : p.1 + 1 ≤ ferrersWidth M := Finset.le_sup (f := fun a : Point => a.1 + 1) hp
  have h2 : p.2 + 1 ≤ ferrersHeight M := Finset.le_sup (f := fun a : Point => a.2 + 1) hp
  omega

theorem ferrers_extents_pos {M : Diagram} (hne : M.Nonempty) :
    0 < ferrersWidth M ∧ 0 < ferrersHeight M := by
  obtain ⟨p, hp⟩ := hne
  have h := ferrers_extent_bounds hp
  omega

theorem ferrers_width_corner {M : Diagram} (hM : IsFerrers M) (hne : M.Nonempty) :
    (ferrersWidth M - 1, 0) ∈ M := by
  obtain ⟨p, hp, he⟩ := Finset.sup_mem_of_nonempty (f := fun p : Point => p.1 + 1) hne
  exact hM p hp _ (by change p.1 + 1 = ferrersWidth M at he; omega) (by omega)

theorem ferrers_height_corner {M : Diagram} (hM : IsFerrers M) (hne : M.Nonempty) :
    (0, ferrersHeight M - 1) ∈ M := by
  obtain ⟨p, hp, he⟩ := Finset.sup_mem_of_nonempty (f := fun p : Point => p.2 + 1) hne
  exact hM p hp _ (by omega) (by change p.2 + 1 = ferrersHeight M at he; omega)

/-- The axes and the interior of a contained block are disjoint subsets. -/
theorem ferrers_axes_block_card {M : Diagram} (hM : IsFerrers M) {p q t c : ℕ}
    (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) (hc : 0 < c)
    (hwidth : (p - 1, 0) ∈ M) (hheight : (0, q - 1) ∈ M)
    (hblock : (t - 1, c - 1) ∈ M) :
    p + (q - 1) + (t - 1) * (c - 1) ≤ M.card := by
  let R := Finset.range p ×ˢ {0}
  let C := {0} ×ˢ Finset.Ico 1 q
  let B := Finset.Ico 1 t ×ˢ Finset.Ico 1 c
  have hR : R ⊆ M := by
    intro x hx
    simp only [R, Finset.mem_product, Finset.mem_range, Finset.mem_singleton] at hx
    exact hM _ hwidth x (by omega) (by omega)
  have hC : C ⊆ M := by
    intro x hx
    simp only [C, Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton] at hx
    exact hM _ hheight x (by omega) (by omega)
  have hB : B ⊆ M := by
    intro x hx
    simp only [B, Finset.mem_product, Finset.mem_Ico] at hx
    exact hM _ hblock x (by omega) (by omega)
  have hdRC : Disjoint R C := by
    apply Finset.disjoint_left.mpr
    intro x hr hc
    simp only [R, C, Finset.mem_product, Finset.mem_range, Finset.mem_singleton, Finset.mem_Ico] at hr hc
    omega
  have hdRB : Disjoint R B := by
    apply Finset.disjoint_left.mpr
    intro x hr hb
    simp only [R, B, Finset.mem_product, Finset.mem_range, Finset.mem_singleton, Finset.mem_Ico] at hr hb
    omega
  have hdCB : Disjoint C B := by
    apply Finset.disjoint_left.mpr
    intro x hc hb
    simp only [C, B, Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico] at hc hb
    omega
  have h := Finset.card_le_card (Finset.union_subset (Finset.union_subset hR hC) hB)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdRB, hdCB⟩),
    Finset.card_union_of_disjoint hdRC] at h
  simpa [R, C, B] using h

theorem shiftedDiagonal_lower_determinant_strict (U : Domain) (c : ℤ) (z : ℝ) (hz : 4 ≤ z)
    {a b : preferredDomain U (shiftedDiagonalReflection c) (fun x => x.2 < x.1 + c)}
    (p : (domainGraph (preferredDomain U (shiftedDiagonalReflection c) (fun x => x.2 < x.1 + c))).Walk a b)
    (hopposite : OppositeSingletons U (shiftedDiagonalReflection c) a.val b.val) :
    faceDeterminant (polarized U (shiftedDiagonalReflection c) (fun x => x.2 < x.1 + c)) z <
      faceDeterminant U z := by
  apply adjacency_strict_determinant_of_domain_moments
  · exact (card_polarized (shiftedDiagonal_involutive c) (fun x => x.2 < x.1 + c)
      (shiftedDiagonal_lower_side c)).symm
  · intro i
    exact shiftedDiagonal_lower_moments U c (i + 1)
  · exact ordinary_strict_from_preferred_walk U _ _ (shiftedDiagonal_involutive c)
      (shiftedDiagonal_lower_side c) (shiftedDiagonal_adj c) (shiftedDiagonal_lower_no_cross c) p hopposite
  · exact hz

/-- Bounding-box escape proves absence from the actual right-corner defect. -/
theorem bottomRight_absent_of_left_or_above {u p q : ℕ} {M : Diagram}
    (hbox : ∀ a ∈ M, a.1 < p ∧ a.2 < q) (x : Vertex)
    (hescape : x.1 < (u : ℤ) - p ∨ (q : ℤ) ≤ x.2) : x ∉ bottomRightDefect u M := by
  intro hx
  obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
  have hb := hbox a ha
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  dsimp [verticalReflection, SquareMaximality.Boundary.ofNatPoint] at he1 he2
  omega

/-- The two straight segments of the main strict Ferrers path. -/
def ferrersStrictPath (u p q t c i : ℕ) : Vertex :=
  if i ≤ q + 1 - c then ((u : ℤ) - p - 1, (c : ℤ) - 1 + i)
  else ((u : ℤ) - p - 1 + (i - (q + 1 - c) : ℕ), q)

@[simp] theorem ferrersStrictPath_start {u p q t c : ℕ} :
    ferrersStrictPath u p q t c 0 = ((u : ℤ) - p - 1, (c : ℤ) - 1) := by
  simp [ferrersStrictPath]

theorem ferrersStrictPath_end {u p q t c : ℕ} (ht : t ≤ p) (hc : c ≤ q + 1) :
    ferrersStrictPath u p q t c ((q + 1 - c) + (p + 1 - t)) = ((u : ℤ) - t, (q : ℤ)) := by
  have hi : ¬(q + 1 - c) + (p + 1 - t) ≤ q + 1 - c := by omega
  simp only [ferrersStrictPath, hi, ite_false]
  apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega

theorem ferrersStrictPath_adj {u p q t c i : ℕ} (hc : c ≤ q + 1) :
    lattice.Adj (ferrersStrictPath u p q t c i) (ferrersStrictPath u p q t c (i + 1)) := by
  by_cases hnext : i + 1 ≤ q + 1 - c
  · have hi : i ≤ q + 1 - c := by omega
    simpa [ferrersStrictPath, hi, hnext, Nat.cast_add, Nat.cast_one, add_assoc] using
      vertical_lattice_step ((u : ℤ) - p - 1) ((c : ℤ) - 1 + i)
  · by_cases hi : i ≤ q + 1 - c
    · have heq : i = q + 1 - c := by omega
      simp only [ferrersStrictPath, hi, hnext, ite_true, ite_false]
      right
      constructor
      · omega
      · have hd : (i + 1 - (q + 1 - c) : ℕ) = 1 := by omega
        rw [hd]
        norm_num
    · simp only [ferrersStrictPath, hi, hnext, ite_false]
      right
      constructor
      · rfl
      · have hd : (i + 1 - (q + 1 - c) : ℕ) = (i - (q + 1 - c)) + 1 := by omega
        rw [hd, Nat.cast_add, Nat.cast_one]
        norm_num

theorem ferrersStrictPath_bounds {u v p q t i : ℕ}
    (huv : u ≤ v) (ht0 : 0 < t) (htp : t ≤ p) (hcq : v - u + t ≤ q)
    (hgap : 2 ≤ (u : ℤ) - p - q + (v - u + t : ℕ))
    (hi : i ≤ (q + 1 - (v - u + t)) + (p + 1 - t)) :
    let x := ferrersStrictPath u p q t (v - u + t) i
    x ∈ rectangle u v ∧ (x.1 < (u : ℤ) - p ∨ (q : ℤ) ≤ x.2) ∧
      x.2 < x.1 + (v - u + t : ℕ) := by
  simp only [ferrersStrictPath, mem_rectangle]
  split_ifs <;> omega

theorem ferrersStrictPath_mem {u v p q t : ℕ} {M : Diagram} (hM : IsFerrers M)
    (huv : u ≤ v) (ht0 : 0 < t) (htu : t ≤ u) (htp : t ≤ p) (hcq : v - u + t ≤ q)
    (hcorner : (t - 1, v - u + t - 1) ∈ M)
    (hsplit : ∀ a ∈ M, a.1 < t ∨ a.2 < v - u + t)
    (hbox : ∀ a ∈ M, a.1 < p ∧ a.2 < q)
    (hgap : 2 ≤ (u : ℤ) - p - q + (v - u + t : ℕ))
    {i : ℕ} (hi : i ≤ (q + 1 - (v - u + t)) + (p + 1 - t)) :
    ferrersStrictPath u p q t (v - u + t) i ∈
      preferredDomain (ferrersFoldCandidate u v t M) (shiftedDiagonalReflection (v - u + t : ℕ))
        (fun x => x.2 < x.1 + (v - u + t : ℕ)) := by
  rw [preferredDomain, Finset.mem_filter, polarize_ferrersFoldCandidate hM huv ht0 htu hcorner hsplit]
  have hb := ferrersStrictPath_bounds huv ht0 htp hcq hgap hi
  exact ⟨Finset.mem_sdiff.mpr ⟨hb.1, bottomRight_absent_of_left_or_above hbox _ hb.2.1⟩, hb.2.2⟩

theorem ferrersStrictPath_opposite {u v p q t : ℕ} {M : Diagram}
    (huv : u ≤ v) (ht0 : 0 < t) (htp : t ≤ p) (hcq : v - u + t ≤ q)
    (hbox : ∀ a ∈ M, a.1 < p ∧ a.2 < q)
    (hgap : 1 ≤ (u : ℤ) - p - q + (v - u + t : ℕ)) :
    OppositeSingletons (ferrersFoldCandidate u v t M) (shiftedDiagonalReflection (v - u + t : ℕ))
      ((u : ℤ) - p - 1, (v - u + t : ℕ) - (1 : ℤ)) ((u : ℤ) - t, q) := by
  let a : Vertex := ((u : ℤ) - p - 1, (v - u + t : ℕ) - (1 : ℤ))
  let b : Vertex := ((u : ℤ) - t, q)
  let f := shiftedDiagonalReflection (v - u + t : ℕ)
  have ha : a ∈ rectangle (u - t) (v + t) := by simp only [a, mem_rectangle]; omega
  have hfa : f a ∉ rectangle (u - t) (v + t) := by
    simp only [f, a, shiftedDiagonalReflection, mem_rectangle]; omega
  have hb : b ∉ rectangle (u - t) (v + t) := by simp only [b, mem_rectangle]; omega
  have hfb : f b ∈ rectangle (u - t) (v + t) := by
    simp only [f, b, shiftedDiagonalReflection, mem_rectangle]; omega
  have haD : a ∉ bottomRightDefect u M := bottomRight_absent_of_left_or_above hbox a (by dsimp [a]; omega)
  have hfaD : f a ∉ bottomRightDefect u M :=
    bottomRight_absent_of_left_or_above hbox (f a) (by dsimp [f, a, shiftedDiagonalReflection]; omega)
  have hbD : b ∉ bottomRightDefect u M := bottomRight_absent_of_left_or_above hbox b (by dsimp [b]; omega)
  have hfbD : f b ∉ bottomRightDefect u M :=
    bottomRight_absent_of_left_or_above hbox (f b) (by dsimp [f, b, shiftedDiagonalReflection]; omega)
  left
  change a ∈ ferrersFoldCandidate u v t M ∧ f a ∉ ferrersFoldCandidate u v t M ∧
    b ∉ ferrersFoldCandidate u v t M ∧ f b ∈ ferrersFoldCandidate u v t M
  simp only [ferrersFoldCandidate, Finset.mem_sdiff, Finset.mem_union,
    mem_image_involution (shiftedDiagonal_involutive _), shiftedDiagonal_involutive,
    ha, hfa, hb, hfb, haD, hfaD, hbD, hfbD, false_or, not_false_eq_true, true_and, false_and]
  constructor
  · exact hfaD
  · change f (f b) ∉ bottomRightDefect u M
    simpa only [f, shiftedDiagonal_involutive] using hbD

theorem ferrers_fold_strict_of_gap {u v p q t : ℕ} {M : Diagram} (hM : IsFerrers M)
    (huv : u ≤ v) (ht0 : 0 < t) (htu : t ≤ u) (htp : t ≤ p) (hcq : v - u + t ≤ q)
    (hcorner : (t - 1, v - u + t - 1) ∈ M)
    (hsplit : ∀ a ∈ M, a.1 < t ∨ a.2 < v - u + t)
    (hbox : ∀ a ∈ M, a.1 < p ∧ a.2 < q)
    (hgap : 2 ≤ (u : ℤ) - p - q + (v - u + t : ℕ)) (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (rectangle u v \ bottomRightDefect u M) z <
      faceDeterminant (ferrersFoldCandidate u v t M) z := by
  let P := preferredDomain (ferrersFoldCandidate u v t M) (shiftedDiagonalReflection (v - u + t : ℕ))
    (fun x => x.2 < x.1 + (v - u + t : ℕ))
  let n := (q + 1 - (v - u + t)) + (p + 1 - t)
  have hmem : ∀ i, i ≤ n → ferrersStrictPath u p q t (v - u + t) i ∈ P :=
    fun i hi => ferrersStrictPath_mem hM huv ht0 htu htp hcq hcorner hsplit hbox hgap hi
  obtain ⟨w⟩ := reachable_along P (ferrersStrictPath u p q t (v - u + t)) n hmem
    (fun i _ => ferrersStrictPath_adj (by omega))
  have hop : OppositeSingletons (ferrersFoldCandidate u v t M) (shiftedDiagonalReflection (v - u + t : ℕ))
      (ferrersStrictPath u p q t (v - u + t) 0) (ferrersStrictPath u p q t (v - u + t) n) := by
    rw [ferrersStrictPath_start, show n = (q + 1 - (v - u + t)) + (p + 1 - t) from rfl,
      ferrersStrictPath_end (u := u) (q := q) (c := v - u + t) htp (by omega)]
    exact ferrersStrictPath_opposite huv ht0 htp hcq hbox (by omega)
  have h := shiftedDiagonal_lower_determinant_strict (ferrersFoldCandidate u v t M) (v - u + t : ℕ) z hz w hop
  rw [polarize_ferrersFoldCandidate hM huv ht0 htu hcorner hsplit] at h
  exact h

theorem ferrers_gap_lower_bound {u t c : ℕ} {M : Diagram} (hM : IsFerrers M)
    (hcard : M.card ≤ u) (ht : 0 < t) (hc : 0 < c) (hcorner : (t - 1, c - 1) ∈ M) :
    (t : ℤ) * ((c : ℤ) - 1) ≤ (u : ℤ) - ferrersWidth M - ferrersHeight M + c := by
  have hne : M.Nonempty := ⟨_, hcorner⟩
  have hpos := ferrers_extents_pos hne
  have hcount := (ferrers_axes_block_card hM hpos.1 hpos.2 ht hc
    (ferrers_width_corner hM hne) (ferrers_height_corner hM hne) hcorner).trans hcard
  have hcountZ : ((ferrersWidth M + (ferrersHeight M - 1) + (t - 1) * (c - 1) : ℕ) : ℤ) ≤ u :=
    by exact_mod_cast hcount
  have hqZ : ((ferrersHeight M - 1 : ℕ) : ℤ) = (ferrersHeight M : ℤ) - 1 := by omega
  have htZ : ((t - 1 : ℕ) : ℤ) = (t : ℤ) - 1 := by omega
  have hcZ : ((c - 1 : ℕ) : ℤ) = (c : ℤ) - 1 := by omega
  simp only [Nat.cast_add, Nat.cast_mul] at hcountZ
  rw [hqZ, htZ, hcZ] at hcountZ
  nlinarith

/-- For every block except the two small cases, cardinality forces the main
strict path to lie entirely inside the strict preferred half-plane. -/
theorem ferrers_fold_strict_of_large_block {u v t : ℕ} {M : Diagram} (hM : IsFerrers M)
    (huv : u ≤ v) (hcard : M.card ≤ u) (ht0 : 0 < t)
    (hcorner : (t - 1, v - u + t - 1) ∈ M)
    (hsplit : ∀ a ∈ M, a.1 < t ∨ a.2 < v - u + t)
    (hlarge : 2 ≤ t * (v - u + t - 1)) (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (rectangle u v \ bottomRightDefect u M) z <
      faceDeterminant (ferrersFoldCandidate u v t M) z := by
  have hc : 0 < v - u + t := by omega
  have hb := ferrers_extent_bounds hcorner
  have htu : t ≤ u := by
    have h := (ferrers_coordinate_lt_card hM hcorner).1
    omega
  have hgap := ferrers_gap_lower_bound hM hcard ht0 hc hcorner
  have hlargeZ : (2 : ℤ) ≤ (t : ℤ) * (v - u + t - 1 : ℕ) := by exact_mod_cast hlarge
  have hcZ : ((v - u + t - 1 : ℕ) : ℤ) = (v - u + t : ℕ) - (1 : ℤ) := by omega
  rw [hcZ] at hlargeZ
  exact ferrers_fold_strict_of_gap hM huv ht0 htu (by omega) (by omega) hcorner hsplit
    (fun a ha => ferrers_extent_bounds ha) (by omega) z hz

end SpanningTreeIsoperimetry.CornerFolds
