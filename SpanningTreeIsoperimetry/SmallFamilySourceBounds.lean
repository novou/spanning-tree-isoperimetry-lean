module

public import SpanningTreeIsoperimetry.SmallFamilyStripCorrections
public import SpanningTreeIsoperimetry.MulticornerEnergyMinimum
public import SpanningTreeIsoperimetry.MulticornerEndpointChecks
public import SpanningTreeIsoperimetry.SmallCornerProfiles
public import SpanningTreeIsoperimetry.RefinedSmallEnergyUpper

@[expose] public section

/-! Actual finite source energies for the small-family comparisons.
The common bound keeps quadrant energies and finite corrections separate. -/
namespace SpanningTreeIsoperimetry.SmallFamilySourceBounds
open Ferrers CornerEnergy CornerPrimalDomains CornerStripBridge SmallCornerCorrections
open SmallFamilyStripCorrections StripRigidity FiniteCornerOrientation
open MulticornerEnergyMinimum RefinedStripEnergy RefinedSmallEnergyUpper
open CrossHullCountComparison
open scoped Classical BigOperators
noncomputable section

def diagramEnergy (r s : ℕ) (M : Diagram) : ℝ :=
  realEnergy M+correction (faceRectangle (r-1) (s-1)) M

def sourceEnergy (r s : ℕ) (M : Corner → Diagram) : ℝ := ∑ c,diagramEnergy r s (M c)

theorem sourceEnergy_eq_finite {r s : ℕ} {M : Corner → Diagram}
    (hM : ∀ c, IsFerrers (M c)) (hr : totalDefect M≤r-1) (hs : totalDefect M≤s-1) :
    sourceEnergy r s M=finiteSourceEnergy M hM hr hs := by
  unfold sourceEnergy finiteSourceEnergy
  apply Finset.sum_congr rfl
  intro c _
  exact (dirichletEnergy_eq (hM c) (ferrers_family_fit hM hr hs c)).symm

theorem diagramEnergy_nonneg (r s : ℕ) (M : Diagram) : 0≤diagramEnergy r s M :=
  add_nonneg (realEnergy_nonneg M) (correction_nonneg _ _)

theorem diagramEnergy_empty (r s : ℕ) : diagramEnergy r s ∅=0 := by
  simp [diagramEnergy,realEnergy_empty,correction_empty]

theorem diagramEnergy_ge_quadrant (r s : ℕ) (M : Diagram) : realEnergy M≤diagramEnergy r s M :=
  le_add_of_nonneg_right (correction_nonneg _ _)

theorem diagramEnergy_ge_cells (r s : ℕ) (M : Diagram) :
    realEnergy M+(M.card : ℝ)*single r s≤diagramEnergy r s M := by
  change realEnergy M+(M.card : ℝ)*correction (faceRectangle (r-1) (s-1)) {(0,0)}≤
    realEnergy M+correction (faceRectangle (r-1) (s-1)) M
  exact add_le_add le_rfl (correction_ge_card_mul_singleton (r-1) (s-1) M)

theorem sourceEnergy_ge_cells (r s : ℕ) (M : Corner → Diagram) :
    (∑ c,realEnergy (M c))+(totalDefect M : ℝ)*single r s≤sourceEnergy r s M := by
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset Corner))
    (fun c _ => diagramEnergy_ge_cells r s (M c))
  simpa only [Finset.sum_add_distrib,← Finset.sum_mul,totalDefect,Nat.cast_sum,sourceEnergy] using hh

theorem sourceEnergy_ge_quadrant (r s : ℕ) (M : Corner → Diagram) :
    (∑ c,realEnergy (M c))≤sourceEnergy r s M :=
  Finset.sum_le_sum (fun c _ => diagramEnergy_ge_quadrant r s (M c))

theorem sourceEnergy_pair (r s : ℕ) {c d : Corner} (hcd : c≠d) (A B : Diagram) :
    sourceEnergy r s (twoCornerFamily c d A B)=diagramEnergy r s A+diagramEnergy r s B := by
  have he : (fun e => diagramEnergy r s (twoCornerFamily c d A B e))=
      (fun e => (if e=c then diagramEnergy r s A else 0)+(if e=d then diagramEnergy r s B else 0)) := by
    funext e
    by_cases hec : e=c <;> by_cases hed : e=d <;>
      simp_all [twoCornerFamily,diagramEnergy_empty]
  rw [sourceEnergy,he,Finset.sum_add_distrib]
  simp

theorem straight_diagramEnergy_lower {r s : ℕ} {M : Diagram}
    (hr : 2≤r) (hrs : r≤s) (hk : M.card<r) (hstrip : IsStraightStrip M) :
    realEnergy (horizontalStrip M.card)+strip r s M.card≤diagramEnergy r s M := by
  have hRS : r-1≤s-1 := by omega
  have hc : strip r s M.card≤correction (faceRectangle (r-1) (s-1)) M := by
    rcases hstrip with he|he
    · have hh := long_strip_correction_le (by omega : 1≤r-1) hRS
        (by omega : M.card≤r-1) false
      change strip r s M.card≤correction (faceRectangle (r-1) (s-1)) (horizontalStrip M.card) at hh
      rwa [← he] at hh
    · have hh := long_strip_correction_le (by omega : 1≤r-1) hRS
        (by omega : M.card≤r-1) true
      change strip r s M.card≤correction (faceRectangle (r-1) (s-1)) (verticalDiagram M.card) at hh
      rw [FiniteStripError.verticalDiagram_transpose,← he] at hh
      exact hh
  rw [← straight_energy hstrip]
  change realEnergy M+strip r s M.card≤realEnergy M+correction (faceRectangle (r-1) (s-1)) M
  exact add_le_add le_rfl hc

theorem two_quadrant_lower {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c))
    {c d : Corner} (hcd : c≠d) (hc : (M c).Nonempty) (hd : (M d).Nonempty) :
    realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip (totalDefect M-1))≤
      ∑ e,realEnergy (M e) :=
  two_nonempty_minimum Finset.univ M (fun c _ => hM c) (Finset.mem_univ c) (Finset.mem_univ d)
    hcd.symm hc hd

theorem three_quadrant_lower {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c))
    {c d e : Corner} (hcd : c≠d) (hce : c≠e) (hde : d≠e)
    (hc : (M c).Nonempty) (hd : (M d).Nonempty) (he : (M e).Nonempty) :
    2*realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip (totalDefect M-2))≤
      ∑ f,realEnergy (M f) :=
  three_nonempty_minimum Finset.univ M (fun c _ => hM c)
    (Finset.mem_univ c) (Finset.mem_univ d) (Finset.mem_univ e)
    hcd.symm hce.symm hde.symm hc hd he

/-- With two occupied corners, either they are the whole support or a third
occupied corner exists. This avoids enumeration of the placements. -/
theorem pair_or_three {M : Corner → Diagram} {c d : Corner}
    (hcd : c≠d) (hc : (M c).Nonempty) (hd : (M d).Nonempty) :
    M=twoCornerFamily c d (M c) (M d) ∨
      ∃ e : Corner, c≠e ∧ d≠e ∧ (M e).Nonempty := by
  by_cases he : ∃ e : Corner, c≠e ∧ d≠e ∧ (M e).Nonempty
  · exact Or.inr he
  · left
    funext e
    by_cases hec : e=c
    · subst e
      simp [twoCornerFamily]
    · by_cases hed : e=d
      · subst e
        simp [twoCornerFamily,hcd.symm]
      · have hempty : M e=∅ := Finset.not_nonempty_iff_eq_empty.mp
          (fun hn => he ⟨e,Ne.symm hec,Ne.symm hed,hn⟩)
        simp [twoCornerFamily,hec,hed,hempty]

theorem nonrectangle_ge_ell {M : Diagram} (hM : IsFerrers M)
    (hne : M.Nonempty) (hr : ¬IsRectangle M) : realEnergy threeCell≤realEnergy M := by
  have hh := realEnergy_threeCell hM hne hr
  have hp : 0≤((maximalCells M).card-2 : ℕ)*realEnergy {(0,0)} :=
    mul_nonneg (Nat.cast_nonneg _) (realEnergy_nonneg _)
  linarith

/-- Below six cells, a nonstrip rectangle is exactly the corner square. -/
theorem small_nonstrip_square_or_ell {M : Diagram} (hM : IsFerrers M)
    (hk : M.card≤5) (hn : ¬IsStraightStrip M) :
    M=faceRectangle 2 2 ∨ realEnergy threeCell≤realEnergy M := by
  have hne := nonempty_of_not_straight hn
  by_cases hrect : IsRectangle M
  · obtain ⟨a,b,he⟩ := hrect
    change M=faceRectangle a b at he
    subst M
    have hcard : (faceRectangle a b).card=a*b := by simp [faceRectangle]
    rw [hcard] at hk
    have hpos : 0<a*b := by simpa only [hcard] using Finset.card_pos.mpr hne
    have ha : 0<a := by nlinarith
    have hb : 0<b := by nlinarith
    have ha1 : a≠1 := by
      intro he
      subst a
      apply hn
      right
      simpa only [hcard,one_mul] using rectangle_vertical b
    have hb1 : b≠1 := by
      intro he
      subst b
      apply hn
      left
      simpa only [hcard,mul_one] using rectangle_horizontal a
    have ha2 : 2≤a := by omega
    have hb2 : 2≤b := by omega
    have ham : 2*a≤a*b := by nlinarith [Nat.mul_le_mul_left a hb2]
    have hbm : 2*b≤a*b := Nat.mul_le_mul_right b ha2
    have hae : a=2 := by omega
    have hbe : b=2 := by omega
    subst a
    subst b
    exact Or.inl rfl
  · exact Or.inr (nonrectangle_ge_ell hM hne hrect)

theorem ell_ge_square : realEnergy (faceRectangle 2 2)≤realEnergy threeCell := by
  have hL := RefinedObstructionEnergy.ell.energy_lower
  have he : RefinedObstructionPolynomials.ell.diagram=threeCell := by decide +kernel
  rw [he] at hL
  have hS := square_energy_upper
  linarith only [hL,hS]

theorem small_nonstrip_ge_square {M : Diagram} (hM : IsFerrers M)
    (hk : M.card≤5) (hn : ¬IsStraightStrip M) : realEnergy (faceRectangle 2 2)≤realEnergy M := by
  rcases small_nonstrip_square_or_ell hM hk hn with rfl|h
  · exact le_refl _
  · exact ell_ge_square.trans h

end
end SpanningTreeIsoperimetry.SmallFamilySourceBounds
