module

public import SpanningTreeIsoperimetry.SmallFamilyPatternData
public import SpanningTreeIsoperimetry.FoldableCornerPairs

@[expose] public section

/-! A placement-independent description of the strip pairs removed by the
strict fold, together with its actual count consequence. -/
namespace SpanningTreeIsoperimetry.SmallFamilyFoldable
open Ferrers CornerEnergy CornerPrimalDomains CornerStripBridge StripRigidity
open scoped Classical
noncomputable section

def Foldable (a : ℕ) (M : Corner → Diagram) : Prop :=
  ∃ c d : Corner, c≠d ∧ ∃ b : ℕ, 1≤b ∧ ∃ v w : Bool,
    M=twoCornerFamily c d (stripDiagram (a+2) v) (stripDiagram b w)

theorem straight_eq_stripDiagram {M : Diagram} (hs : IsStraightStrip M) :
    ∃ v : Bool, M=stripDiagram M.card v := by
  rcases hs with hs|hs
  · exact ⟨false,hs⟩
  · refine ⟨true,?_⟩
    change M=verticalDiagram M.card
    rw [FiniteStripError.verticalDiagram_transpose]
    exact hs

theorem twoCornerFamily_swap {c d : Corner} (hcd : c≠d) (A B : Diagram) :
    twoCornerFamily c d A B=twoCornerFamily d c B A := by
  funext e
  by_cases hec : e=c <;> by_cases hed : e=d <;> simp_all [twoCornerFamily]

theorem pair_foldable {a : ℕ} {A B : Diagram} {c d : Corner} (hcd : c≠d)
    (hA : IsStraightStrip A) (hB : IsStraightStrip B) (hp : 1≤A.card) (hq : 1≤B.card)
    (hfold : A.card=a+2 ∨ B.card=a+2) : Foldable a (twoCornerFamily c d A B) := by
  obtain ⟨v,hv⟩ := straight_eq_stripDiagram hA
  obtain ⟨w,hw⟩ := straight_eq_stripDiagram hB
  rcases hfold with ha|hb
  · refine ⟨c,d,hcd,B.card,hq,v,w,?_⟩
    rw [← ha,← hv,← hw]
  · refine ⟨d,c,hcd.symm,A.card,hp,w,v,?_⟩
    rw [← hb,← hv,← hw]
    exact twoCornerFamily_swap hcd A B

theorem foldable_count_lt {N r a k : ℕ} {M : Corner → Diagram}
    (hN : 18≤N) (hcard : totalDefect M=k) (hk : k<r)
    (harea : r*(r+a)=N+k) (hsum : r+(r+a)=minimumSideSum N) (hf : Foldable a M) :
    treeCount (cornerPrimal (r-1) (r+a-1) M)<treeCount (canonicalDomain N) := by
  obtain ⟨c,d,hcd,b,hb,v,w,rfl⟩ := hf
  rw [totalDefect_twoCornerFamily hcd,stripDiagram_card,stripDiagram_card] at hcard
  have h := FoldableCornerPairs.foldable_pair_lt_canonical hN (by omega : r≤r+a) hb
    (by omega : (r+a)-r+b+2<r) (by omega : r*(r+a)=N+((r+a)-r+2+b)) hsum
    hcd v w
  simpa only [Nat.add_sub_cancel_left] using h

end
end SpanningTreeIsoperimetry.SmallFamilyFoldable
