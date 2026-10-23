module

public import SpanningTreeIsoperimetry.CornerStripBridge

@[expose] public section

/-! Every finite lower-ideal vacancy set is attached to the rectangular
boundary. The corresponding primal construction has no interior component. -/
namespace SpanningTreeIsoperimetry.FerrersBoundaryAttachment
open Ferrers CornerEnergy SquareMaximality.Boundary
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem king_horizontal_reachable (M : Diagram) (y x x' : ℕ) (hxx' : x≤x')
    (hmem : ∀ t, x≤t → t≤x' → (t,y)∈M) :
    (kingGraph M).Reachable ⟨(x,y),hmem x le_rfl hxx'⟩ ⟨(x',y),hmem x' hxx' le_rfl⟩ := by
  induction x',hxx' using Nat.le_induction with
  | base => exact SimpleGraph.Reachable.refl _
  | succ n hxn ih =>
    have hmem' : ∀ t, x≤t → t≤n → (t,y)∈M :=
      fun t hxt htn => hmem t hxt (htn.trans (Nat.le_succ n))
    have hr:=ih hmem'
    have hn : (n,y)∈M := hmem n hxn (Nat.le_succ n)
    have hs : (n+1,y)∈M := hmem (n+1) (hxn.trans (Nat.le_succ n)) le_rfl
    have ha : (kingGraph M).Adj ⟨(n,y),hn⟩ ⟨(n+1,y),hs⟩ := by
      rw [kingGraph_adj_iff]
      change (n,y)≠(n+1,y) ∧ Nat.dist n (n+1)≤1 ∧ Nat.dist y y≤1
      constructor
      · intro he
        have hx:=congrArg Prod.fst he
        omega
      · constructor <;> simp [Nat.dist]
    exact hr.trans ha.reachable

theorem ferrers_boundary_attached {M : Diagram} (hM : IsFerrers M) (R S : ℕ)
    {p : Ferrers.Point} (hp : p∈M) : IsBoundaryAttached R S M p := by
  have h0 : (0,p.2)∈M := hM p hp _ (Nat.zero_le _) le_rfl
  have hmem : ∀ t, 0≤t → t≤p.1 → (t,p.2)∈M :=
    fun t _ ht => hM p hp _ ht le_rfl
  refine ⟨hp,⟨(0,p.2),h0⟩,Or.inl rfl,?_⟩
  have h:=king_horizontal_reachable M p.2 0 p.1 (Nat.zero_le _) hmem
  simpa only [Prod.mk.eta] using h.symm

theorem boundaryVacancies_ferrers {M : Diagram} (hM : IsFerrers M) (R S : ℕ) :
    boundaryVacancies R S M=M := by
  apply Finset.Subset.antisymm (boundaryVacancies_subset R S M)
  intro p hp
  exact mem_boundaryVacancies.mpr (ferrers_boundary_attached hM R S hp)

theorem interiorVacancies_ferrers {M : Diagram} (hM : IsFerrers M) (R S : ℕ) :
    interiorVacancies R S M=∅ := by
  rw [interiorVacancies,boundaryVacancies_ferrers hM,Finset.sdiff_self]

theorem canonicalInteriorCount_zero_of_all_boundary {R S : ℕ} {A : Domain}
    (hb : boundaryVacancies R S (encodedVacancies R S A)=encodedVacancies R S A) :
    canonicalInteriorCount R S A=0 := by
  have hi : interiorVacancies R S (encodedVacancies R S A)=∅ := by
    rw [interiorVacancies,hb,Finset.sdiff_self]
  by_contra hz
  let i : Fin (canonicalInteriorCount R S A) := ⟨0,Nat.pos_of_ne_zero hz⟩
  let c := (canonicalInteriorEquiv R S A).symm i
  obtain ⟨p,hp⟩:=interiorComponent_nonempty R S (canonicalVacancies R S A) c
  have hpi:=interiorComponent_subset_interiorVacancies R S (canonicalVacancies R S A) c hp
  simpa only [canonicalVacancies,hi,Finset.notMem_empty] using hpi

theorem canonicalInteriorCount_zero_of_ferrers {R S : ℕ} {A : Domain}
    (hM : IsFerrers (encodedVacancies R S A)) : canonicalInteriorCount R S A=0 :=
  canonicalInteriorCount_zero_of_all_boundary (boundaryVacancies_ferrers hM R S)

end SpanningTreeIsoperimetry.FerrersBoundaryAttachment
