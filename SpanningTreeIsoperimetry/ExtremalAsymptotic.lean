module

public import SpanningTreeIsoperimetry.AllCardinalityClassification
public import SpanningTreeIsoperimetry.CanonicalCountAsymptotic
public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-! The actual global maximum and its complete asymptotic expansion. The
maximum is defined intrinsically from all connected lattice domains. -/
namespace SpanningTreeIsoperimetry.ExtremalAsymptotic
open Filter Asymptotics CanonicalCountAsymptotic
noncomputable section

def maximumCount (N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Domain, A.card=N ∧ (domainGraph A).Connected ∧ treeCount A=k}

theorem maximumCount_eq_proposed {N : ℕ} (hN : 0<N) : maximumCount N=proposedMaximum N := by
  obtain ⟨hw,hu⟩ := AllCardinalityClassification.maximumValueTarget N hN
  apply IsGreatest.csSup_eq
  refine ⟨hw,?_⟩
  rintro k ⟨A,hcard,hconn,hcount⟩
  rw [← hcount]
  exact hu A hcard hconn

theorem maximumCount_attained {N : ℕ} (hN : 0<N) :
    ∃ A : Domain, A.card=N ∧ (domainGraph A).Connected ∧ treeCount A=maximumCount N := by
  rw [maximumCount_eq_proposed hN]
  exact (AllCardinalityClassification.maximumValueTarget N hN).1

theorem treeCount_le_maximum {A : Domain} (hA : (domainGraph A).Connected) :
    treeCount A≤maximumCount A.card := by
  have hN : 0<A.card := Finset.card_pos.mpr (connected_domain_nonempty hA)
  rw [maximumCount_eq_proposed hN]
  exact (AllCardinalityClassification.maximumValueTarget A.card hN).2 A rfl hA

theorem extremal_count_asymptotic :
    (fun N : ℕ => Real.log (maximumCount N : ℝ)-mainTerm N)=O[atTop]
      (fun N : ℕ => 1/Real.sqrt (N : ℝ)) := by
  obtain ⟨C,hC⟩ := canonical_count_asymptotic.bound
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC,eventually_ge_atTop 18] with N hbound hN
  have he : maximumCount N=treeCount (canonicalDomain N) := by
    rw [maximumCount_eq_proposed (by omega : 0<N)]
    simp only [proposedMaximum,show N≠7 by omega,show N≠14 by omega,show N≠17 by omega,ite_false]
  rw [he]
  exact hbound

end
end SpanningTreeIsoperimetry.ExtremalAsymptotic
