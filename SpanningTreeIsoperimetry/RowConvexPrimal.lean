module

public import SpanningTreeIsoperimetry.FerrersPrimalBridge

@[expose] public section

/-! Sparse row-convex primal domains: actual connectivity, hull, boundary
attachment and the finite Dirichlet tree-count identity. -/
namespace SpanningTreeIsoperimetry.RowConvexPrimal

open Ferrers CornerEnergy DomainIsometries SquareMaximality.Boundary
open FerrersPrimalBridge FerrersBoundaryAttachment
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

/-- Every occupied row is an interval in natural coordinates. -/
def RowConvex (U : Diagram) : Prop :=
  ∀ x₁ x x₂ y : ℕ, (x₁,y)∈U → (x₂,y)∈U → x₁≤x → x≤x₂ → (x,y)∈U

theorem exists_intact_column {R S : ℕ} {M : Diagram} (hk : M.card≤R) :
    ∃ x≤R, ∀ y≤S, (x,y)∈faceRectangle (R+1) (S+1) \ M := by
  have hc : (M.image Prod.fst).card < (Finset.range (R+1)).card := by
    have h := Finset.card_image_le (s := M) (f := Prod.fst)
    simpa only [Finset.card_range] using (h.trans hk).trans_lt (Nat.lt_succ_self R)
  obtain ⟨x,hx,hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have hxR : x≤R := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hx
  refine ⟨x,hxR,fun y hy => Finset.mem_sdiff.mpr ⟨?_,?_⟩⟩
  · exact mem_faceRectangle.mpr ⟨by omega,by omega⟩
  · intro hm
    exact hnot (Finset.mem_image.mpr ⟨(x,y),hm,rfl⟩)

theorem exists_intact_row {R S : ℕ} {M : Diagram} (hk : M.card≤S) :
    ∃ y≤S, ∀ x≤R, (x,y)∈faceRectangle (R+1) (S+1) \ M := by
  have hc : (M.image Prod.snd).card < (Finset.range (S+1)).card := by
    have h := Finset.card_image_le (s := M) (f := Prod.snd)
    simpa only [Finset.card_range] using (h.trans hk).trans_lt (Nat.lt_succ_self S)
  obtain ⟨y,hy,hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have hyS : y≤S := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hy
  refine ⟨y,hyS,fun x hx => Finset.mem_sdiff.mpr ⟨?_,?_⟩⟩
  · exact mem_faceRectangle.mpr ⟨by omega,by omega⟩
  · intro hm
    exact hnot (Finset.mem_image.mpr ⟨(x,y),hm,rfl⟩)

theorem natural_connected {R S : ℕ} {M : Diagram}
    (hrow : RowConvex (faceRectangle (R+1) (S+1) \ M)) (hk : M.card≤R) :
    (faceGraph (faceRectangle (R+1) (S+1) \ M)).Connected := by
  obtain ⟨c,hc,hcol⟩ := exists_intact_column (S := S) hk
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨(c,0),hcol 0 (Nat.zero_le _)⟩,?_⟩
  intro p
  have hb := mem_faceRectangle.mp (Finset.mem_sdiff.mp p.property).1
  have hcy := hcol p.val.2 (by omega)
  have hh : (faceGraph (faceRectangle (R+1) (S+1) \ M)).Reachable p ⟨(c,p.val.2),hcy⟩ := by
    by_cases hpc : p.val.1≤c
    · have hmem : ∀ t, p.val.1≤t → t≤c → (t,p.val.2)∈faceRectangle (R+1) (S+1) \ M :=
        fun t ht htc => hrow _ _ _ _ p.property hcy ht htc
      simpa only [Prod.mk.eta] using horizontal_reachable _ _ _ _ hpc hmem
    · have hmem : ∀ t, c≤t → t≤p.val.1 → (t,p.val.2)∈faceRectangle (R+1) (S+1) \ M :=
        fun t ht htc => hrow _ _ _ _ hcy p.property ht htc
      simpa only [Prod.mk.eta] using (horizontal_reachable _ _ _ _ (by omega) hmem).symm
  have hv := vertical_reachable _ c 0 p.val.2 (Nat.zero_le _) (fun t _ ht => hcol t (by omega))
  exact (hh.trans hv.symm).symm

theorem primal_connected {R S : ℕ} {M : Diagram}
    (hrow : RowConvex (faceRectangle (R+1) (S+1) \ M)) (hk : M.card≤R) :
    (domainGraph (primalDomain R S M)).Connected :=
  (integerFacesGraphIso (faceRectangle (R+1) (S+1) \ M)).connected_iff.mp (natural_connected hrow hk)

theorem primal_hull {R S : ℕ} {M : Diagram} (hR : M.card≤R) (hS : M.card≤S) :
    SquareMaximality.IsRectHull (primalDomain R S M) 0 0 (R+1) (S+1) := by
  obtain ⟨c,hc,hcol⟩ := exists_intact_column (S := S) hR
  obtain ⟨d,hd,hrow⟩ := exists_intact_row (R := R) hS
  have hl : ((0 : ℤ),(d : ℤ))∈primalDomain R S M :=
    Finset.mem_image.mpr ⟨(0,d),hrow 0 (Nat.zero_le _),rfl⟩
  have hr : ((R : ℤ),(d : ℤ))∈primalDomain R S M :=
    Finset.mem_image.mpr ⟨(R,d),hrow R le_rfl,rfl⟩
  have hb : ((c : ℤ),(0 : ℤ))∈primalDomain R S M :=
    Finset.mem_image.mpr ⟨(c,0),hcol 0 (Nat.zero_le _),rfl⟩
  have ht : ((c : ℤ),(S : ℤ))∈primalDomain R S M :=
    Finset.mem_image.mpr ⟨(c,S),hcol S le_rfl,rfl⟩
  refine ⟨by omega,by omega,?_,⟨(0,d),hl,rfl⟩,⟨(R,d),hr,by simp⟩,
    ⟨(c,0),hb,rfl⟩,⟨(c,S),ht,by simp⟩⟩
  rw [← rectangle_eq_foundation,primalDomain_eq]
  exact Finset.sdiff_subset

theorem encodedVacancies_primal {R S : ℕ} {M : Diagram}
    (hfit : M⊆faceRectangle (R+1) (S+1)) : encodedVacancies R S (primalDomain R S M)=M := by
  ext p
  rw [mem_encodedVacancies]
  constructor
  · rintro ⟨hx,hy,hn⟩
    by_contra hp
    apply hn
    rw [primalDomain_eq]
    apply Finset.mem_sdiff.mpr
    constructor
    · rw [mem_rectangle]
      dsimp [ofNatPoint]
      omega
    · exact fun h => hp ((integerFaces_mem M p).mp h)
  · intro hp
    have hb := mem_faceRectangle.mp (hfit hp)
    refine ⟨by omega,by omega,?_⟩
    rw [primalDomain_eq]
    intro h
    exact (Finset.mem_sdiff.mp h).2 ((integerFaces_mem M p).mpr hp)

/-- Row convexity forces each vacancy to have an empty horizontal interval
all the way to one of the two vertical hull sides. -/
theorem rowConvex_boundary_attached {R S : ℕ} {M : Diagram}
    (hfit : M⊆faceRectangle (R+1) (S+1))
    (hrow : RowConvex (faceRectangle (R+1) (S+1) \ M))
    {p : Ferrers.Point} (hp : p∈M) : IsBoundaryAttached R S M p := by
  have hb := mem_faceRectangle.mp (hfit hp)
  by_cases hl : ∀ t, t≤p.1 → (t,p.2)∈M
  · have h0 := hl 0 (Nat.zero_le _)
    refine ⟨hp,⟨(0,p.2),h0⟩,Or.inl rfl,?_⟩
    have hr := king_horizontal_reachable M p.2 0 p.1 (Nat.zero_le _) (fun t _ ht => hl t ht)
    simpa only [Prod.mk.eta] using hr.symm
  · push Not at hl
    obtain ⟨l,hlp,hlM⟩ := hl
    have hlU : (l,p.2)∈faceRectangle (R+1) (S+1) \ M :=
      Finset.mem_sdiff.mpr ⟨mem_faceRectangle.mpr ⟨by omega,hb.2⟩,hlM⟩
    have hrAll : ∀ t, p.1≤t → t≤R → (t,p.2)∈M := by
      intro t hpt htR
      by_contra htM
      have htU : (t,p.2)∈faceRectangle (R+1) (S+1) \ M :=
        Finset.mem_sdiff.mpr ⟨mem_faceRectangle.mpr ⟨by omega,hb.2⟩,htM⟩
      exact (Finset.mem_sdiff.mp (hrow l p.1 t p.2 hlU htU hlp hpt)).2 hp
    have hR := hrAll R (by omega) le_rfl
    refine ⟨hp,⟨(R,p.2),hR⟩,Or.inr (Or.inl rfl),?_⟩
    have hr := king_horizontal_reachable M p.2 p.1 R (by omega) hrAll
    simpa only [Prod.mk.eta] using hr

theorem primal_no_interior {R S : ℕ} {M : Diagram}
    (hfit : M⊆faceRectangle (R+1) (S+1))
    (hrow : RowConvex (faceRectangle (R+1) (S+1) \ M)) :
    canonicalInteriorCount R S (primalDomain R S M)=0 := by
  apply canonicalInteriorCount_zero_of_all_boundary
  rw [encodedVacancies_primal hfit]
  apply Finset.Subset.antisymm (boundaryVacancies_subset R S M)
  intro p hp
  exact mem_boundaryVacancies.mpr (rowConvex_boundary_attached hfit hrow hp)

theorem primal_treeCount_eq_dirichlet {R S : ℕ} {M : Diagram} (hR : 1≤R) (hS : 1≤S)
    (hfit : M⊆faceRectangle (R+1) (S+1))
    (hrow : RowConvex (faceRectangle (R+1) (S+1) \ M)) (hkR : M.card≤R) (hkS : M.card≤S) :
    (treeCount (primalDomain R S M) : ℝ)=
      Matrix.det (fourIminusAdjacency (unmarkedFaces R S M)) := by
  have h := (PrimalDirichlet.treeCount_pair_eq_dirichlet hR hS (primal_hull hkR hkS)
    (primal_connected hrow hkR) (primal_no_interior hfit hrow)).2
  have heq : PrimalDirichlet.remainingFaces R S (primalDomain R S M)=unmarkedFaces R S M := by
    unfold PrimalDirichlet.remainingFaces unmarkedFaces
    rw [encodedVacancies_primal hfit]
  rw [heq] at h
  exact h

theorem primal_card {R S : ℕ} {M : Diagram} (hfit : M⊆faceRectangle (R+1) (S+1)) :
    (primalDomain R S M).card=(R+1)*(S+1)-M.card := by
  unfold primalDomain integerFaces
  rw [Finset.card_image_of_injective _ ofNatPoint_injective,Finset.card_sdiff_of_subset hfit]
  simp [faceRectangle]

end
end SpanningTreeIsoperimetry.RowConvexPrimal
