module

public import SquareMaximality.Boundary.Windows2D
public import SquareMaximality.Boundary.Degenerate

@[expose] public section

set_option autoImplicit false

/-!
# Encoding a normalized lattice rectangle by natural coordinates

The boundary-window development uses the finite grid
`{0, ..., R} × {0, ..., S}` on natural coordinates, whereas the main theorem
uses subsets of `ℤ × ℤ`.  This file gives the exact bridge between the two
representations.  In particular, encoded vacancies have exactly the cardinality
of the set difference in the normalized rectangular hull.
-/

namespace SquareMaximality

namespace Boundary

/-- Embed a natural-coordinate grid point in the integer lattice. -/
def ofNatPoint (z : LatticePoint) : Point := ((z.1 : ℤ), (z.2 : ℤ))

@[simp] theorem ofNatPoint_fst (z : LatticePoint) : (ofNatPoint z).1 = (z.1 : ℤ) := rfl

@[simp] theorem ofNatPoint_snd (z : LatticePoint) : (ofNatPoint z).2 = (z.2 : ℤ) := rfl

theorem ofNatPoint_injective : Function.Injective ofNatPoint := by
  intro z w h
  apply Prod.ext
  · have hx : (z.1 : ℤ) = (w.1 : ℤ) := congrArg (fun p => p.1) h
    exact_mod_cast hx
  · have hy : (z.2 : ℤ) = (w.2 : ℤ) := congrArg (fun p => p.2) h
    exact_mod_cast hy

/-- Vacancies of `A` in the natural-coordinate rectangle. -/
def encodedVacancies (R S : ℕ) (A : Finset Point) : Finset LatticePoint :=
  (grid R S).filter fun z => ofNatPoint z ∉ A

@[simp] theorem mem_encodedVacancies {R S : ℕ} {A : Finset Point} {z : LatticePoint} :
    z ∈ encodedVacancies R S A ↔ z.1 ≤ R ∧ z.2 ≤ S ∧ ofNatPoint z ∉ A := by
  simp only [encodedVacancies, Finset.mem_filter, mem_grid]
  tauto

@[simp] theorem ofNatPoint_mem_standardRectangle {R S : ℕ} {z : LatticePoint} :
    ofNatPoint z ∈ rectangle 0 0 (R + 1) (S + 1) ↔ z.1 ≤ R ∧ z.2 ≤ S := by
  simp [rectangle, ofNatPoint]
  omega

/-- The image of the encoded vacancies is literally the integer-lattice set
difference in the normalized rectangle. -/
theorem image_encodedVacancies (R S : ℕ) (A : Finset Point) :
    (encodedVacancies R S A).image ofNatPoint =
      rectangle 0 0 (R + 1) (S + 1) \ A := by
  classical
  ext p
  constructor
  · intro hp
    rw [Finset.mem_image] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    have hz' := mem_encodedVacancies.mp hz
    exact Finset.mem_sdiff.mpr ⟨ofNatPoint_mem_standardRectangle.mpr ⟨hz'.1, hz'.2.1⟩,
      hz'.2.2⟩
  · intro hp
    have hp' := Finset.mem_sdiff.mp hp
    have hpRect :
        ((0 : ℤ) ≤ p.1 ∧ p.1 < (R + 1 : ℕ)) ∧
        ((0 : ℤ) ≤ p.2 ∧ p.2 < (S + 1 : ℕ)) := by
      simpa [rectangle] using hp'.1
    let z : LatticePoint := (p.1.toNat, p.2.toNat)
    have hx0 : 0 ≤ p.1 := hpRect.1.1
    have hy0 : 0 ≤ p.2 := hpRect.2.1
    have hxR : p.1 ≤ (R : ℤ) := by omega
    have hyS : p.2 ≤ (S : ℤ) := by omega
    have hzval : ofNatPoint z = p := by
      apply Prod.ext <;> simp [z, ofNatPoint, hx0, hy0]
    rw [← hzval]
    exact Finset.mem_image.mpr ⟨z, mem_encodedVacancies.mpr ⟨by
      simpa [z] using Int.toNat_le.mpr hxR, by
      simpa [z] using Int.toNat_le.mpr hyS, by simpa [hzval] using hp'.2⟩, rfl⟩

/-- Encoded and integer-coordinate vacancy sets have the same cardinality. -/
@[simp] theorem card_encodedVacancies (R S : ℕ) (A : Finset Point) :
    (encodedVacancies R S A).card =
      (rectangle 0 0 (R + 1) (S + 1) \ A).card := by
  rw [← image_encodedVacancies R S A]
  exact (Finset.card_image_of_injective _ ofNatPoint_injective).symm

/-- Every natural-coordinate column contains an occupied point when `A` is
connected and its displayed rectangle is the minimal hull. -/
theorem exists_occupied_in_column
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    {x : ℕ} (hx : x ≤ R) :
    ∃ y ≤ S, ofNatPoint (x, y) ∈ A := by
  obtain ⟨p, hpA, hpX⟩ := hHull.exists_point_with_first_eq hconn
    (x := (x : ℤ)) (by positivity) (by exact_mod_cast Nat.lt_succ_of_le hx)
  have hpRect := hHull.2.2.1 hpA
  have hpBounds :
      ((0 : ℤ) ≤ p.1 ∧ p.1 < (R + 1 : ℕ)) ∧
      ((0 : ℤ) ≤ p.2 ∧ p.2 < (S + 1 : ℕ)) := by
    simpa [rectangle] using hpRect
  let y := p.2.toNat
  have hyS : y ≤ S := by
    apply Int.toNat_le.mpr
    omega
  have hpY : (y : ℤ) = p.2 := by
    simpa [y] using Int.toNat_of_nonneg hpBounds.2.1
  refine ⟨y, hyS, ?_⟩
  have hpEq : ofNatPoint (x, y) = p := by
    exact Prod.ext hpX.symm hpY
  simpa [hpEq] using hpA

/-- Every natural-coordinate row contains an occupied point under the same
minimal-hull and connectedness hypotheses. -/
theorem exists_occupied_in_row
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    {y : ℕ} (hy : y ≤ S) :
    ∃ x ≤ R, ofNatPoint (x, y) ∈ A := by
  obtain ⟨p, hpA, hpY⟩ := hHull.exists_point_with_second_eq hconn
    (y := (y : ℤ)) (by positivity) (by exact_mod_cast Nat.lt_succ_of_le hy)
  have hpRect := hHull.2.2.1 hpA
  have hpBounds :
      ((0 : ℤ) ≤ p.1 ∧ p.1 < (R + 1 : ℕ)) ∧
      ((0 : ℤ) ≤ p.2 ∧ p.2 < (S + 1 : ℕ)) := by
    simpa [rectangle] using hpRect
  let x := p.1.toNat
  have hxR : x ≤ R := by
    apply Int.toNat_le.mpr
    omega
  have hpX : (x : ℤ) = p.1 := by
    simpa [x] using Int.toNat_of_nonneg hpBounds.1.1
  refine ⟨x, hxR, ?_⟩
  have hpEq : ofNatPoint (x, y) = p := by
    exact Prod.ext hpX hpY.symm
  simpa [hpEq] using hpA

/-- In particular, no in-range column is entirely vacant. -/
theorem encodedVacancies_column_ne_line
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    {x : ℕ} (hx : x ≤ R) :
    column S (encodedVacancies R S A) x ≠ Windows.line S := by
  obtain ⟨y, hy, hyA⟩ := exists_occupied_in_column hHull hconn hx
  intro hfull
  have hyVac : (x, y) ∈ encodedVacancies R S A := by
    have : y ∈ column S (encodedVacancies R S A) x := by
      rw [hfull]
      exact Windows.mem_line.mpr hy
    exact (mem_column.mp this).2
  exact (mem_encodedVacancies.mp hyVac).2.2 hyA

/-- Likewise, no in-range row is entirely vacant. -/
theorem encodedVacancies_row_ne_line
    {R S : ℕ} {A : Finset Point}
    (hHull : IsRectHull A 0 0 (R + 1) (S + 1))
    (hconn : (inducedGrid A).Connected)
    {y : ℕ} (hy : y ≤ S) :
    row R (encodedVacancies R S A) y ≠ Windows.line R := by
  obtain ⟨x, hx, hxA⟩ := exists_occupied_in_row hHull hconn hy
  intro hfull
  have hxVac : (x, y) ∈ encodedVacancies R S A := by
    have : x ∈ row R (encodedVacancies R S A) y := by
      rw [hfull]
      exact Windows.mem_line.mpr hx
    exact (mem_row.mp this).2
  exact (mem_encodedVacancies.mp hxVac).2.2 hxA

end Boundary

end SquareMaximality
