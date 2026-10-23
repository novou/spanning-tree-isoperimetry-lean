module

public import SpanningTreeIsoperimetry.CanonicalCornerLong
public import SpanningTreeIsoperimetry.CanonicalShortStripEnergy
public import SpanningTreeIsoperimetry.CornerProfileNormalization

@[expose] public section

set_option backward.privateInPublic true

/-! Actual canonical-hull concentration for N≥18, with strict nonstrip
improvement and uniqueness up to the concrete lattice congruence relation. -/
namespace SpanningTreeIsoperimetry.CanonicalCornerConcentration
open Ferrers CornerEnergy CornerPrimalDomains CornerStripBridge CornerConcentration
  CanonicalConcentrationArithmetic CanonicalSmallBaseline CanonicalCornerLong
  CanonicalShortStripEnergy FiniteCornerCharges CornerProfileNormalization StripTreeComparisons
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem canonical_nonstrip_short {N r s k : ℕ} (hN : 18≤N) (hp : canonicalParameters N=(r,s,k))
    (hk : 2≤k) (hk4 : k≤4) {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c))
    (htotal : totalDefect M=k) (hn : ¬IsConcentrated Finset.univ M) :
    treeCount (cornerPrimal (r-1) (s-1) M)<treeCount (cornerStrip r s k) := by
  have hprop := parameters_properties (by omega) hp
  have hgap := canonical_gap (by omega) hp
  have hr0 : 1≤r-1 := by omega
  have hs0 : 1≤s-1 := by omega
  have hR : totalDefect M≤r-1 := by omega
  have hS : totalDefect M≤s-1 := by omega
  have he : dirichletEnergy (verticalDiagram_subset hr0 hS)<
      (∑ c,realEnergy (M c))+(totalDefect M : ℝ)*correction (faceRectangle (r-1) (s-1)) {(0,0)} := by
    rw [dirichletEnergy_eq (verticalDiagram_ferrers (totalDefect M)),htotal]
    interval_cases k
    · have hf := two_strip_gap (canonical_two_min hN hp) hgap
      have hb := family_two_baseline hM htotal hn
      rw [dirichletEnergy_eq (verticalDiagram_ferrers 2)] at hf
      norm_num only [Nat.cast_ofNat]
      linarith only [hf,hb]
    · have hf := three_strip_gap (canonical_three_min (by omega) hp) hgap
      have hb := family_three_baseline hM htotal hn
      rw [dirichletEnergy_eq (verticalDiagram_ferrers 3)] at hf
      norm_num only [Nat.cast_ofNat]
      linarith [correction_nonneg (faceRectangle (r-1) (s-1)) ({(0,0)} : Diagram)]
    · have hf := four_strip_gap (canonical_four_min (by omega) hp) hgap
      have hb := family_four_baseline hM htotal hn
      rw [dirichletEnergy_eq (verticalDiagram_ferrers 4)] at hf
      norm_num only [Nat.cast_ofNat]
      linarith only [hf,hb]
  have h := count_lt_strip_of_energy_gap hr0 hs0 hM hR hS he
  simpa only [htotal,Nat.sub_add_cancel (show 1≤r by omega),Nat.sub_add_cancel (show 1≤s by omega)] using h

theorem canonical_nonstrip_strict {N r s k : ℕ} (hN : 18≤N) (hp : canonicalParameters N=(r,s,k))
    (hk : 2≤k) {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c))
    (htotal : totalDefect M=k) (hn : ¬IsConcentrated Finset.univ M) :
    treeCount (cornerPrimal (r-1) (s-1) M)<treeCount (cornerStrip r s k) := by
  by_cases hk5 : 5≤k
  · exact canonical_nonstrip_long (by omega) hp hk5 hM htotal hn
  · exact canonical_nonstrip_short hN hp hk (by omega) hM htotal hn

/-- The manuscript's geometric hypotheses identify the actual selector;
there is no supplied canonical gap or finite-volume comparison premise. -/
theorem minimum_hull_nonstrip_strict {N r s k : ℕ} (hN : 18≤N) (hr : 1≤r)
    (hrs : r≤s) (hk : 2≤k) (harea : r*s=N+k) (hsum : r+s=minimumSideSum N)
    (hcanonical : k≤s-r) {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c))
    (htotal : totalDefect M=k) (hn : ¬IsConcentrated Finset.univ M) :
    treeCount (cornerPrimal (r-1) (s-1) M)<treeCount (cornerStrip r s k) := by
  have hp := CanonicalStrips.terminal_parameters (by omega) hr hrs harea hsum (by omega)
  exact canonical_nonstrip_strict hN hp hk hM htotal hn

theorem single_family_of_concentrated {M : Corner → Diagram} {k : ℕ}
    (htotal : totalDefect M=k) (hc : IsConcentrated Finset.univ M) :
    ∃ c : Corner, ∃ v : Bool, M=singleFamily c (stripDiagram k v) := by
  obtain ⟨c,hc,hne,hstrip,hother⟩ := hc
  have hsum : totalDefect M=(M c).card := by
    change (∑ d : Corner,(M d).card)=(M c).card
    apply Finset.sum_eq_single c
    · intro d hd hdc
      rw [hother d hd hdc]
      rfl
    · intro hc
      exact False.elim (hc (Finset.mem_univ _))
  have hcard : (M c).card=k := by omega
  have hv : ∃ v : Bool, M c=stripDiagram k v := by
    rcases hstrip with h | h
    · exact ⟨false,by simpa only [hcard,stripDiagram,Bool.false_eq_true,ite_false] using h⟩
    · exact ⟨true,by simpa only [hcard,stripDiagram,ite_true,FiniteStripError.verticalDiagram_transpose] using h⟩
  obtain ⟨v,hv⟩ := hv
  refine ⟨c,v,?_⟩
  funext d
  by_cases hdc : d=c
  · subst d
    simp [singleFamily,twoCornerFamily,hv]
  · have he := hother d (Finset.mem_univ _) hdc
    simp [singleFamily,twoCornerFamily,hdc,he]

theorem empty_family_single {M : Corner → Diagram} (hk : totalDefect M=0) :
    M=singleFamily (true,true) (stripDiagram 0 true) := by
  have he (c : Corner) : M c=∅ := Finset.card_eq_zero.mp (by have h:=corner_card_le_total M c; omega)
  funext c
  simp [singleFamily,twoCornerFamily,stripDiagram,verticalDiagram,he]

private theorem single_family_comparison {N r s k : ℕ} (hN : 18≤N)
    (hp : canonicalParameters N=(r,s,k)) (c : Corner) (v : Bool) :
    treeCount (cornerPrimal (r-1) (s-1) (singleFamily c (stripDiagram k v)))≤treeCount (canonicalDomain N) ∧
    (treeCount (cornerPrimal (r-1) (s-1) (singleFamily c (stripDiagram k v)))=treeCount (canonicalDomain N) →
      Congruent (cornerPrimal (r-1) (s-1) (singleFamily c (stripDiagram k v))) (canonicalDomain N)) := by
  have hprop := parameters_properties (by omega) hp
  have hr : r-1+1=r := by omega
  have hs : s-1+1=s := by omega
  have hn := single_normalization (R := r-1) (S := s-1) c (stripDiagram_ferrers k v)
    (by rw [stripDiagram_card]; omega) (by rw [stripDiagram_card]; omega)
  refine ⟨single_strip_le_canonical (by omega) (by omega) (by omega)
    (by simpa only [hr,hs] using hprop.2.2.2.1) (by simpa only [hr,hs] using hprop.2.2.1) c v,?_⟩
  intro hcount
  have he := hn.treeCount_eq.symm.trans hcount
  have hshape : cornerPrimal (r-1) (s-1) (singleFamily (true,true) (stripDiagram k v))=cornerStrip r s k ∨
      cornerPrimal (r-1) (s-1) (singleFamily (true,true) (stripDiagram k v))=horizontalCornerStrip r s k := by
    rw [single_strip_primal,hr,hs]
    cases v <;> simp
  exact hn.trans (CanonicalStrips.strip_family_equality_congruent hN (by omega) hprop.2.1
    hprop.2.2.2.2 hprop.2.2.2.1 hprop.2.2.1 hshape he)

/-- Full canonical concentration: every actual four-corner family is bounded
by the canonical strip, with equality exactly at its lattice-isometric copies. -/
theorem canonical_family_optimal {N r s k : ℕ} (hN : 18≤N) (hp : canonicalParameters N=(r,s,k))
    {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c)) (htotal : totalDefect M=k) :
    treeCount (cornerPrimal (r-1) (s-1) M)≤treeCount (canonicalDomain N) ∧
    (treeCount (cornerPrimal (r-1) (s-1) M)=treeCount (canonicalDomain N) ↔
      Congruent (cornerPrimal (r-1) (s-1) M) (canonicalDomain N)) := by
  have hsingle : (∃ c : Corner, ∃ v : Bool, M=singleFamily c (stripDiagram k v)) ∨
      treeCount (cornerPrimal (r-1) (s-1) M)<treeCount (canonicalDomain N) := by
    by_cases hk0 : k=0
    · have hz : totalDefect M=0 := htotal.trans hk0
      rw [hk0]
      exact Or.inl ⟨(true,true),true,empty_family_single hz⟩
    · by_cases hc : IsConcentrated Finset.univ M
      · exact Or.inl (single_family_of_concentrated htotal hc)
      · have hk2 : 2≤k := by
          by_contra hh
          have hk1 : k=1 := by omega
          exact hc (total_one_concentrated hM (by omega))
        have hh := canonical_nonstrip_strict hN hp hk2 hM htotal hc
        right
        simpa only [canonicalDomain,hp] using hh
  rcases hsingle with ⟨c,v,rfl⟩ | hstrict
  · have hh := single_family_comparison hN hp c v
    exact ⟨hh.1,⟨hh.2,fun hc => hc.treeCount_eq⟩⟩
  · exact ⟨hstrict.le,⟨fun he => False.elim (hstrict.ne he),fun hc => hc.treeCount_eq⟩⟩

/-- Geometric-hypothesis formulation of canonical concentration, including
all deficits and the complete equality classification. -/
theorem minimum_hull_family_optimal {N r s k : ℕ} (hN : 18≤N) (hr : 1≤r)
    (hrs : r≤s) (harea : r*s=N+k) (hsum : r+s=minimumSideSum N)
    (hcanonical : k≤s-r) {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c))
    (htotal : totalDefect M=k) :
    treeCount (cornerPrimal (r-1) (s-1) M)≤treeCount (cornerStrip r s k) ∧
    (treeCount (cornerPrimal (r-1) (s-1) M)=treeCount (cornerStrip r s k) ↔
      Congruent (cornerPrimal (r-1) (s-1) M) (cornerStrip r s k)) := by
  have hp := CanonicalStrips.terminal_parameters (by omega) hr hrs harea hsum (by omega)
  simpa only [canonicalDomain,hp] using canonical_family_optimal hN hp hM htotal

end
end SpanningTreeIsoperimetry.CanonicalCornerConcentration
