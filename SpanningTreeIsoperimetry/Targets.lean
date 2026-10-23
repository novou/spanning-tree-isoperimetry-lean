module

public import SpanningTreeIsoperimetry.Grid
public import SpanningTreeIsoperimetry.HullArithmetic
public import SpanningTreeIsoperimetry.LocalBounds
public import SpanningTreeIsoperimetry.StabilityGeometry
public import Mathlib.Data.Finset.SymmDiff

@[expose] public section

open scoped symmDiff

/-! Main manuscript targets and their exact objects.
Declarations ending in `Target` are propositions, not proofs. They add no
axioms. Compilation of this file does not prove these manuscript results. -/

namespace SpanningTreeIsoperimetry

noncomputable def minimumSideSum (N : ℕ) : ℕ := ⌈2 * Real.sqrt (N : ℝ)⌉₊

noncomputable def canonicalParameters (N : ℕ) : ℕ × ℕ × ℕ :=
  let L := minimumSideSum N
  let m := L / 2
  let e := L % 2
  let d := m * (m + e) - N
  let T := selectorIndex d e
  (m - T, m + e + T, d - T * (T + e))

noncomputable def canonicalDomain (N : ℕ) : Domain :=
  let p := canonicalParameters N
  cornerStrip p.1 p.2.1 p.2.2

theorem canonicalDomain_card {N : ℕ} (hN : 0 < N) :
    (canonicalDomain N).card = N := by
  have hp := selected_hull_properties_of_ceil hN
  change 0 < (canonicalParameters N).1 ∧
    (canonicalParameters N).1 ≤ (canonicalParameters N).2.1 ∧
    (canonicalParameters N).1 + (canonicalParameters N).2.1 = minimumSideSum N ∧
    (canonicalParameters N).1 * (canonicalParameters N).2.1 =
      N + (canonicalParameters N).2.2 ∧
    (canonicalParameters N).2.2 < (canonicalParameters N).1 at hp
  unfold canonicalDomain
  rw [card_cornerStrip (by omega) (by omega)]
  omega

/-- Translation, optional coordinate exchange, and independent sign changes. -/
def rigidMotion (a : Vertex) (swap : Bool) (sx sy : ℤ) (v : Vertex) : Vertex :=
  let p := if swap then (v.2, v.1) else v
  (a.1 + sx * p.1, a.2 + sy * p.2)

def Congruent (S T : Domain) : Prop :=
  ∃ a : Vertex, ∃ swap : Bool, ∃ sx sy : ℤ,
    (sx = 1 ∨ sx = -1) ∧ (sy = 1 ∨ sy = -1) ∧
    S.image (rigidMotion a swap sx sy) = T

theorem congruent_refl (S : Domain) : Congruent S S := by
  refine ⟨(0,0), false, 1, 1, Or.inl rfl, Or.inl rfl, ?_⟩
  have hf : rigidMotion (0,0) false 1 1 = id := by
    funext v
    simp [rigidMotion]
  rw [hf, Finset.image_id]

noncomputable def edgeCount (S : Domain) : ℕ := Nat.card (domainGraph S).edgeSet

/-- Headline isoperimetry target, discharged in `Isoperimetry.lean` by
`isoperimetryTarget`. -/
def IsoperimetryTarget : Prop :=
  ∀ S : Domain, IsMaximizer S →
    edgeCount S = 2 * S.card - minimumSideSum S.card

/-- Large-cardinality uniqueness target, discharged in `LargeClassification`. -/
def UniqueClassificationTarget : Prop :=
  ∀ N : ℕ, 18 ≤ N → IsMaximizer (canonicalDomain N) ∧
    ∀ S : Domain, S.card = N → IsMaximizer S → Congruent S (canonicalDomain N)

noncomputable def normalizedAsymmetry (n : ℕ) (S : Domain) : ℝ :=
  ((sInf {k : ℕ | ∃ a : Vertex,
    k = (S ∆ (rectangle n n).image (translate a)).card} : ℕ) : ℝ) / (n : ℝ) ^ 2

/-- Manuscript geometric asymmetry bound, for any containing translated hull.
Minimality, connectivity, and convexity of the domain are unnecessary. -/
theorem normalizedAsymmetry_sq_le_of_fits {n r s : ℕ} {S : Domain}
    (hn : 0 < n) (hcard : S.card = n ^ 2) (hfit : FitsRectangle S r s) :
    normalizedAsymmetry n S ^ 2 ≤ 4 * ((r : ℝ) + s - 2 * n) / n := by
  obtain ⟨a, ha⟩ := exists_square_symmDiff_sq_bound_of_fits hn hcard hfit
  let m := sInf {k : ℕ | ∃ a : Vertex,
    k = (S ∆ (rectangle n n).image (translate a)).card}
  have hm : m ≤ (S ∆ translatedSquare n a).card := Nat.sInf_le ⟨a, rfl⟩
  have hmr : (m : ℝ) ≤ (S ∆ translatedSquare n a).card := by exact_mod_cast hm
  have hsq : (m : ℝ) ^ 2 ≤ ((S ∆ translatedSquare n a).card : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hmr
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  change ((m : ℝ) / (n : ℝ) ^ 2) ^ 2 ≤ _
  calc
    _ = (m : ℝ) ^ 2 / (n : ℝ) ^ 4 := by ring
    _ ≤ (4 * (n : ℝ) ^ 3 * ((r : ℝ) + s - 2 * n)) / (n : ℝ) ^ 4 :=
      div_le_div_of_nonneg_right (hsq.trans ha) (by positivity)
    _ = 4 * ((r : ℝ) + s - 2 * n) / n := by field_simp

noncomputable def proposedMaximum (N : ℕ) : ℕ :=
  if N = 7 then 16 else if N = 14 then 8960 else if N = 17 then 112456
  else treeCount (canonicalDomain N)

/-- All-cardinality value formula, discharged in `AllCardinalityClassification`. -/
def MaximumValueTarget : Prop :=
  ∀ N : ℕ, 0 < N →
    (∃ S : Domain, S.card = N ∧ (domainGraph S).Connected ∧
      treeCount S = proposedMaximum N) ∧
    ∀ S : Domain, S.card = N → (domainGraph S).Connected →
      treeCount S ≤ proposedMaximum N

def HasNonisometricMaximizers (N : ℕ) : Prop :=
  ∃ S T : Domain, S.card = N ∧ T.card = N ∧
    IsMaximizer S ∧ IsMaximizer T ∧ ¬Congruent S T

/-- Complete nonuniqueness target, discharged in `AllCardinalityClassification`. -/
def NonuniquenessTarget : Prop :=
  ∀ N : ℕ, 0 < N → (HasNonisometricMaximizers N ↔ N = 3 ∨ N = 8 ∨ N = 10 ∨ N = 13)

/-- Stability inequality target, discharged in `Stability.lean` by
`sharpStabilityInequalityTarget`; sharpness of the coefficient is separate. -/
def SharpStabilityInequalityTarget : Prop :=
  ∀ n : ℕ, 0 < n → ∀ S : Domain, S.card = n ^ 2 →
    (domainGraph S).Connected →
    Real.log ((treeCount (rectangle n n) : ℝ) / treeCount S) ≥
      (Real.log (1 + Real.sqrt 2) / 4) * n * normalizedAsymmetry n S ^ 2

end SpanningTreeIsoperimetry
