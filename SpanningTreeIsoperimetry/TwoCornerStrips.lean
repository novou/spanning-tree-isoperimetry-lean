module

public import SpanningTreeIsoperimetry.CornerFolds

@[expose] public section

/-! Opposite strip orientations for the actual two-corner fold. -/
namespace SpanningTreeIsoperimetry.CornerFolds

open Polarization StripPolarization
open scoped Classical

/-- The booleans specify whether each corner strip is vertical. -/
def twoOrientedFaces (r s a b : ℕ) (leftV rightV : Bool) : Domain :=
  (rectangle (r - 1) (s - 1)).filter fun x =>
    (if leftV then x.1 ≠ 0 ∨ (a : ℤ) ≤ x.2 else x.2 ≠ 0 ∨ (a : ℤ) ≤ x.1) ∧
    (if rightV then x.1 ≠ (r : ℤ) - 2 ∨ x.2 < (s : ℤ) - 1 - b
      else x.2 ≠ (s : ℤ) - 2 ∨ x.1 < (r : ℤ) - 1 - b)

@[simp] theorem twoOrientedFaces_vertical (r s a b : ℕ) :
    twoOrientedFaces r s a b true true = twoVerticalFaces r s a b := rfl

@[simp] theorem mem_twoOrientedFaces {r s a b : ℕ} {leftV rightV : Bool} {x : Vertex} :
    x ∈ twoOrientedFaces r s a b leftV rightV ↔
      0 ≤ x.1 ∧ x.1 < (r - 1 : ℕ) ∧ 0 ≤ x.2 ∧ x.2 < (s - 1 : ℕ) ∧
      (if leftV then x.1 ≠ 0 ∨ (a : ℤ) ≤ x.2 else x.2 ≠ 0 ∨ (a : ℤ) ≤ x.1) ∧
      (if rightV then x.1 ≠ (r : ℤ) - 2 ∨ x.2 < (s : ℤ) - 1 - b
        else x.2 ≠ (s : ℤ) - 2 ∨ x.1 < (r : ℤ) - 1 - b) := by
  simp only [twoOrientedFaces, Finset.mem_filter, mem_rectangle]
  tauto

/-- Orient one corner horizontally while preserving the opposite deletion. -/
theorem polarize_twoOrientedFaces {r s a b : ℕ} (hrs : r ≤ s) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hsize : a + b < r) (rightV : Bool) (hfix : rightV = true ∨ r < s) :
    polarized (twoOrientedFaces r s a b true rightV) Prod.swap (fun x : Vertex => x.1 < x.2) =
      twoOrientedFaces r s a b false rightV := by
  ext x
  rw [mem_polarized Prod.swap_swap]
  cases rightV <;> simp only [Bool.false_eq_true, false_or] at hfix <;>
    simp only [mem_twoOrientedFaces, Bool.false_eq_true, ↓reduceIte,
    Prod.fst_swap, Prod.snd_swap] <;> split_ifs <;> omega

theorem twoOriented_left_comparison {r s a b : ℕ} (hrs : r ≤ s) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hsize : a + b < r) (rightV : Bool) (hfix : rightV = true ∨ r < s) (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (twoOrientedFaces r s a b false rightV) z ≤
      faceDeterminant (twoOrientedFaces r s a b true rightV) z := by
  have h := adjacency_determinant_of_domain_moments (twoOrientedFaces r s a b true rightV)
    (polarized (twoOrientedFaces r s a b true rightV) Prod.swap (fun x : Vertex => x.1 < x.2))
    (card_polarized Prod.swap_swap _ diagonal_preferred_side).symm
    (fun i => diagonal_adjacency_moments _ (i + 1)) z hz
  change faceDeterminant (polarized (twoOrientedFaces r s a b true rightV) Prod.swap
    (fun x : Vertex => x.1 < x.2)) z ≤ _ at h
  rw [polarize_twoOrientedFaces hrs ha hb hsize rightV hfix] at h
  exact h

def twoCornerHalfTurn (r s : ℕ) : Vertex ≃ Vertex :=
  (Function.Involutive.toPerm (verticalReflection ((r : ℤ) - 2)) (vertical_involutive _)).trans
    (Function.Involutive.toPerm (axialReflection ((s : ℤ) - 2)) (axialReflection_involutive _))

@[simp] theorem twoCornerHalfTurn_apply (r s : ℕ) (x : Vertex) :
    twoCornerHalfTurn r s x = ((r : ℤ) - 2 - x.1, (s : ℤ) - 2 - x.2) := rfl

noncomputable def twoOriented_halfTurnIso {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (a b : ℕ) (leftV rightV : Bool) :
    domainGraph (twoOrientedFaces r s a b leftV rightV) ≃g
      domainGraph (twoOrientedFaces r s b a rightV leftV) :=
  graphIsoOfEquiv (twoCornerHalfTurn r s)
    (by
      intro x
      cases leftV <;> cases rightV <;>
        simp only [mem_twoOrientedFaces, twoCornerHalfTurn_apply, Bool.false_eq_true, ↓reduceIte] <;> omega)
    (by
      intro x y _ _
      change lattice.Adj (axialReflection ((s : ℤ) - 2) (verticalReflection ((r : ℤ) - 2) x))
        (axialReflection ((s : ℤ) - 2) (verticalReflection ((r : ℤ) - 2) y)) ↔ _
      rw [axial_adjacency_invariant, vertical_adjacency_invariant])

noncomputable def twoOriented_transposeIso (r s a b : ℕ) (leftV rightV : Bool) :
    domainGraph (twoOrientedFaces r s a b leftV rightV) ≃g
      domainGraph (twoOrientedFaces s r a b (!leftV) (!rightV)) :=
  graphIsoOfEquiv (Equiv.prodComm ℤ ℤ)
    (by
      intro x
      cases leftV <;> cases rightV <;>
        simp only [mem_twoOrientedFaces, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap,
          Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] <;> tauto)
    (fun x y _ _ => diagonal_adjacency_invariant x y)

theorem twoOriented_right_comparison {r s a b : ℕ} (hrs : r ≤ s) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hsize : a + b < r) (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (twoOrientedFaces r s a b true false) z ≤
      faceDeterminant (twoOrientedFaces r s a b true true) z := by
  rw [faceDeterminant_iso (twoOriented_halfTurnIso (by omega) (by omega) a b true false) z,
    faceDeterminant_iso (twoOriented_halfTurnIso (by omega) (by omega) a b true true) z]
  exact twoOriented_left_comparison hrs hb ha (by omega) true (Or.inl rfl) z hz

/-- Among all four orientations, two vertical strips have the largest determinant. -/
theorem twoOriented_determinant_le_vertical {r s a b : ℕ} (hrs : r ≤ s) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hsize : a + b < r) (leftV rightV : Bool) (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (twoOrientedFaces r s a b leftV rightV) z ≤
      faceDeterminant (twoVerticalFaces r s a b) z := by
  change _ ≤ faceDeterminant (twoOrientedFaces r s a b true true) z
  cases leftV <;> cases rightV
  · by_cases heq : r = s
    · subst s
      exact le_of_eq (faceDeterminant_iso (twoOriented_transposeIso r r a b false false) z)
    · exact (twoOriented_left_comparison hrs ha hb hsize false (Or.inr (by omega)) z hz).trans
        (twoOriented_right_comparison hrs ha hb hsize z hz)
  · exact twoOriented_left_comparison hrs ha hb hsize true (Or.inl rfl) z hz
  · exact twoOriented_right_comparison hrs ha hb hsize z hz
  · exact le_rfl

 theorem twoOriented_exceptional_eq (leftV rightV : Bool) (z : ℝ) :
    faceDeterminant (twoOrientedFaces 4 4 2 1 leftV rightV) z =
      faceDeterminant (twoVerticalFaces 4 4 2 1) z := by
  have hright (l r₁ r₂ : Bool) : twoOrientedFaces 4 4 2 1 l r₁ = twoOrientedFaces 4 4 2 1 l r₂ := by
    ext x
    cases l <;> cases r₁ <;> cases r₂ <;>
      simp only [mem_twoOrientedFaces, Bool.false_eq_true, ↓reduceIte] <;> omega
  cases leftV
  · rw [hright false rightV false]
    exact faceDeterminant_iso (twoOriented_transposeIso 4 4 2 1 false false) z
  · rw [hright true rightV true, twoOrientedFaces_vertical]

/-- Two-corner fold for all four actual strip orientations. -/
theorem two_corner_fold_determinant {r s b : ℕ} (hrs : r ≤ s) (hb : 1 ≤ b)
    (hsize : s - r + b + 2 < r) (leftV rightV : Bool) (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (twoOrientedFaces r s (s - r + 2) b leftV rightV) z ≤
      faceDeterminant (faceStripY (r - 2) s (b + 1)) z := by
  have h := (twoOriented_determinant_le_vertical hrs (by omega) hb (by omega) leftV rightV z hz).trans
    (twoStrip_determinant hrs hb hsize z hz)
  rwa [faceDeterminant_iso (twoStripCandidateIso (by omega)) z] at h

theorem two_corner_fold_determinant_eq_iff {r s b : ℕ} (hrs : r ≤ s) (hb : 1 ≤ b)
    (hsize : s - r + b + 2 < r) (leftV rightV : Bool) (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (twoOrientedFaces r s (s - r + 2) b leftV rightV) z =
      faceDeterminant (faceStripY (r - 2) s (b + 1)) z ↔ r = 4 ∧ s = 4 ∧ b = 1 := by
  rw [← faceDeterminant_iso (twoStripCandidateIso (by omega)) z]
  constructor
  · intro heq
    by_contra h
    have hs := twoStrip_determinant_strict hrs (by omega) hb hsize z hz
    have hle := twoOriented_determinant_le_vertical (a := s - r + 2) hrs (by omega) hb (by omega) leftV rightV z hz
    linarith
  · rintro ⟨rfl, rfl, rfl⟩
    rw [show 4 - 4 + 2 = (2 : ℕ) by decide]
    exact (twoOriented_exceptional_eq leftV rightV z).trans (faceDeterminant_iso exceptionalTwoStripIso z)

end SpanningTreeIsoperimetry.CornerFolds
