import SpanningTreeIsoperimetry.SmallFamilySourceBounds
import SpanningTreeIsoperimetry.RefinedCornerEnvelope

/-! Row metadata and common algebra for the first twenty small-family
comparisons. Matching records the actual hull gap and total defect. -/
namespace SpanningTreeIsoperimetry.SmallFamilyPatternData
open Ferrers CornerEnergy CornerPrimalDomains SmallFamilySourceBounds
open SmallFamilyStripCorrections SmallCornerCorrections
open SmallFamilyProfiles SmallFamilyMonotonicity MulticornerEndpointChecks
open scoped Classical BigOperators
noncomputable section

def rowDeficit : Fin 26 → ℕ := ![2,2,3,3,3,3,4,4,4,4,4,5,5,5,5,5,5,6,6,6,7,6,0,0,0,0]

def Supported (a k : ℕ) : Prop :=
  (a=0 ∧ 2≤k ∧ k≤6) ∨ (a=1 ∧ 2≤k ∧ k≤5) ∨ (a=2 ∧ 3≤k ∧ k≤5)

def Matches (a k : ℕ) (i : Fin 26) : Prop := i.val<20 ∧ gap i=a ∧ rowDeficit i=k

def rowLower (i : Fin 26) (r : ℕ) : ℝ :=
  quadrantFloor i+weightedLoss Finset.univ (coeff i) shifts r

def RowBound (r a k : ℕ) (M : Corner → Diagram) : Prop :=
  ∃ i : Fin 26, Matches a k i ∧ rowLower i r≤sourceEnergy r (r+a) M

theorem weightedLoss_four (i : Fin 26) (r : ℕ) :
    weightedLoss Finset.univ (coeff i) shifts r=
      coeff i 0*weight r 0+coeff i 1*weight r 1+
      coeff i 2*weight r 2+coeff i 3*weight r 3 := by
  simp [weightedLoss,weight,shifts,Fin.sum_univ_succ,div_eq_mul_inv]
  <;> ring

theorem weight_le_at {r R i : ℕ} (hi : i<R) (hR : R≤r) : weight r i≤weight R i := by
  have hpos : (0 : ℝ)<(R : ℝ)-i := by
    have h := (show (i : ℝ)<R by exact_mod_cast hi)
    linarith
  have hle : (R : ℝ)-i≤(r : ℝ)-i := sub_le_sub_right (by exact_mod_cast hR) _
  unfold weight
  exact one_div_le_one_div_of_le (pow_pos hpos 4) (pow_le_pow_left₀ hpos.le hle 4)

theorem sourceEnergy_pair_cells (r s : ℕ) {c d : Corner} (hcd : c≠d) (A B : Diagram) :
    realEnergy A+realEnergy B+((A.card : ℝ)+B.card)*single r s≤
      sourceEnergy r s (twoCornerFamily c d A B) := by
  rw [sourceEnergy_pair r s hcd]
  linarith only [diagramEnergy_ge_cells r s A,diagramEnergy_ge_cells r s B]

theorem straight_pair_lower {r s : ℕ} {c d : Corner} (hcd : c≠d) {A B : Diagram}
    (hr : 2≤r) (hrs : r≤s) (hA : StripRigidity.IsStraightStrip A) (hB : StripRigidity.IsStraightStrip B)
    (hAk : A.card<r) (hBk : B.card<r) :
    realEnergy (horizontalStrip A.card)+realEnergy (horizontalStrip B.card)+
      strip r s A.card+strip r s B.card≤sourceEnergy r s (twoCornerFamily c d A B) := by
  rw [sourceEnergy_pair r s hcd]
  linarith only [straight_diagramEnergy_lower hr hrs hAk hA,straight_diagramEnergy_lower hr hrs hBk hB]

theorem nonstrip_card_ge_three {M : Diagram} (hM : IsFerrers M) (hn : ¬StripRigidity.IsStraightStrip M) :
    3≤M.card := by
  by_contra hh
  exact hn (SmallShapeCatalogue.ferrers_two_cell_strip hM (by omega))

theorem three_total_ge_three {M : Corner → Diagram} {c d e : Corner}
    (hcd : c≠d) (hce : c≠e) (hde : d≠e)
    (hc : (M c).Nonempty) (hd : (M d).Nonempty) (he : (M e).Nonempty) : 3≤totalDefect M := by
  have hh := Finset.sum_le_sum_of_subset_of_nonneg (f := fun c : Corner => (M c).card)
    (Finset.subset_univ ({c,d,e} : Finset Corner)) (fun _ _ _ => Nat.zero_le _)
  simp only [Finset.sum_insert (show c∉({d,e} : Finset Corner) by simp [hcd,hce]),
    Finset.sum_pair hde] at hh
  have hp := Finset.card_pos.mpr hc
  have hq := Finset.card_pos.mpr hd
  have ht := Finset.card_pos.mpr he
  change _≤totalDefect M at hh
  omega


def stripFloor (k : ℕ) : ℝ :=
  if k=1 then 5987/200000 else if k=2 then 40831/1000000 else
  if k=3 then 46369/1000000 else if k=4 then 19893/400000 else
  if k=5 then 13/250 else if k=6 then 107271/2000000 else 0

theorem stripFloor_le {k : ℕ} (hk : k≤6) : stripFloor k≤realEnergy (horizontalStrip k) := by
  interval_cases k <;> norm_num [stripFloor]
  · exact RefinedStripEnergy.strip_energy_bounds_1.1.le
  · exact RefinedStripEnergy.strip_energy_bounds_2.1.le
  · exact RefinedStripEnergy.strip_energy_bounds_3.1.le
  · exact RefinedStripEnergy.strip_energy_bounds_4.1.le
  · exact RefinedStripEnergy.strip_energy_bounds_5.1.le
  · exact RefinedStripEnergy.strip_energy_bounds_6.1.le

theorem diagramFloor_le {M : Diagram} (hM : IsFerrers M) (hk : M.card≤6) :
    stripFloor M.card≤realEnergy M := (stripFloor_le hk).trans (StripRigidity.strip_energy_minimal hM)

theorem three_floor {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c))
    (hk : totalDefect M≤6) {c d e : Corner} (hcd : c≠d) (hce : c≠e) (hde : d≠e)
    (hc : (M c).Nonempty) (hd : (M d).Nonempty) (he : (M e).Nonempty) :
    2*stripFloor 1+stripFloor (totalDefect M-2)≤∑ f,realEnergy (M f) := by
  have h := three_quadrant_lower hM hcd hce hde hc hd he
  have h1 := stripFloor_le (by decide : 1≤6)
  have h2 := stripFloor_le (show totalDefect M-2≤6 by omega)
  linarith only [h,h1,h2]

end
end SpanningTreeIsoperimetry.SmallFamilyPatternData
