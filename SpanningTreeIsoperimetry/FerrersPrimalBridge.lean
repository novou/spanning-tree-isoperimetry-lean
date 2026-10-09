import SpanningTreeIsoperimetry.FerrersBoundaryAttachment

/-! A single Ferrers corner gives an actual connected primal domain.
Its hull, vacancy components and tree count are constructed explicitly. -/
namespace SpanningTreeIsoperimetry.FerrersPrimalBridge
open Ferrers CornerEnergy DomainIsometries SquareMaximality.Boundary
open FerrersBoundaryAttachment
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def primalDomain (R S : ℕ) (M : Diagram) : Domain :=
  integerFaces (faceRectangle (R+1) (S+1) \ M)

theorem primalDomain_eq (R S : ℕ) (M : Diagram) :
    primalDomain R S M=rectangle (R+1) (S+1) \ integerFaces M := by
  unfold primalDomain integerFaces
  rw [Finset.image_sdiff _ _ ofNatPoint_injective]
  change integerFaces (faceRectangle (R+1) (S+1)) \ integerFaces M=_
  rw [CornerStripBridge.integerFaces_faceRectangle]
  rfl

theorem horizontal_reachable (U : Diagram) (y x x' : ℕ) (hxx' : x≤x')
    (hmem : ∀ t, x≤t → t≤x' → (t,y)∈U) :
    (faceGraph U).Reachable ⟨(x,y),hmem x le_rfl hxx'⟩ ⟨(x',y),hmem x' hxx' le_rfl⟩ := by
  induction x',hxx' using Nat.le_induction with
  | base => exact SimpleGraph.Reachable.refl _
  | succ n hxn ih =>
    have hmem' : ∀ t, x≤t → t≤n → (t,y)∈U :=
      fun t hxt htn => hmem t hxt (htn.trans (Nat.le_succ n))
    have hr:=ih hmem'
    have hn : (n,y)∈U := hmem n hxn (Nat.le_succ n)
    have hs : (n+1,y)∈U := hmem (n+1) (hxn.trans (Nat.le_succ n)) le_rfl
    have ha : (faceGraph U).Adj ⟨(n,y),hn⟩ ⟨(n+1,y),hs⟩ := by
      rw [faceGraph_adj_iff]
      simp [natManhattanDist,Nat.dist]
    exact hr.trans ha.reachable

theorem vertical_reachable (U : Diagram) (x y y' : ℕ) (hyy' : y≤y')
    (hmem : ∀ t, y≤t → t≤y' → (x,t)∈U) :
    (faceGraph U).Reachable ⟨(x,y),hmem y le_rfl hyy'⟩ ⟨(x,y'),hmem y' hyy' le_rfl⟩ := by
  induction y',hyy' using Nat.le_induction with
  | base => exact SimpleGraph.Reachable.refl _
  | succ n hyn ih =>
    have hmem' : ∀ t, y≤t → t≤n → (x,t)∈U :=
      fun t hyt htn => hmem t hyt (htn.trans (Nat.le_succ n))
    have hr:=ih hmem'
    have hn : (x,n)∈U := hmem n hyn (Nat.le_succ n)
    have hs : (x,n+1)∈U := hmem (n+1) (hyn.trans (Nat.le_succ n)) le_rfl
    have ha : (faceGraph U).Adj ⟨(x,n),hn⟩ ⟨(x,n+1),hs⟩ := by
      rw [faceGraph_adj_iff]
      simp [natManhattanDist,Nat.dist]
    exact hr.trans ha.reachable

theorem remaining_upper_closed {R S : ℕ} {M : Diagram} (hM : IsFerrers M)
    {p q : Ferrers.Point} (hp : p∈faceRectangle (R+1) (S+1) \ M)
    (hx : p.1≤q.1) (hy : p.2≤q.2) (hq : q∈faceRectangle (R+1) (S+1)) :
    q∈faceRectangle (R+1) (S+1) \ M :=
  Finset.mem_sdiff.mpr ⟨hq,fun h => (Finset.mem_sdiff.mp hp).2 (hM q h p hx hy)⟩

theorem top_mem {R S : ℕ} {M : Diagram} (hfit : M⊆faceRectangle R S) {x : ℕ} (hx : x≤R) :
    (x,S)∈faceRectangle (R+1) (S+1) \ M := by
  refine Finset.mem_sdiff.mpr ⟨mem_faceRectangle.mpr ⟨by omega,by omega⟩,?_⟩
  intro hm
  have h:=(mem_faceRectangle.mp (hfit hm)).2
  omega

theorem right_mem {R S : ℕ} {M : Diagram} (hfit : M⊆faceRectangle R S) {y : ℕ} (hy : y≤S) :
    (R,y)∈faceRectangle (R+1) (S+1) \ M := by
  refine Finset.mem_sdiff.mpr ⟨mem_faceRectangle.mpr ⟨by omega,by omega⟩,?_⟩
  intro hm
  have h:=(mem_faceRectangle.mp (hfit hm)).1
  omega

theorem natural_connected {R S : ℕ} {M : Diagram} (hM : IsFerrers M) (hfit : M⊆faceRectangle R S) :
    (faceGraph (faceRectangle (R+1) (S+1) \ M)).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨(R,S),top_mem hfit le_rfl⟩,?_⟩
  intro p
  have hb:=mem_faceRectangle.mp (Finset.mem_sdiff.mp p.property).1
  have hh : ∀ t, p.val.1≤t → t≤R → (t,p.val.2)∈faceRectangle (R+1) (S+1) \ M := by
    intro t ht hR
    exact remaining_upper_closed hM p.property ht le_rfl (mem_faceRectangle.mpr ⟨by omega,hb.2⟩)
  have hv : ∀ t, p.val.2≤t → t≤S → (R,t)∈faceRectangle (R+1) (S+1) \ M :=
    fun t _ ht => right_mem hfit ht
  have h1:=horizontal_reachable _ p.val.2 p.val.1 R (by omega) hh
  have h2:=vertical_reachable _ R p.val.2 S (by omega) hv
  simpa only [Prod.mk.eta] using (h1.trans h2).symm

theorem primal_connected {R S : ℕ} {M : Diagram} (hM : IsFerrers M) (hfit : M⊆faceRectangle R S) :
    (domainGraph (primalDomain R S M)).Connected :=
  (integerFacesGraphIso (faceRectangle (R+1) (S+1) \ M)).connected_iff.mp (natural_connected hM hfit)

theorem primal_hull {R S : ℕ} {M : Diagram} (hfit : M⊆faceRectangle R S) :
    SquareMaximality.IsRectHull (primalDomain R S M) 0 0 (R+1) (S+1) := by
  have ht : ((0 : ℤ),(S : ℤ))∈primalDomain R S M :=
    Finset.mem_image.mpr ⟨(0,S),top_mem hfit (Nat.zero_le _),rfl⟩
  have hr : ((R : ℤ),(0 : ℤ))∈primalDomain R S M :=
    Finset.mem_image.mpr ⟨(R,0),right_mem hfit (Nat.zero_le _),rfl⟩
  refine ⟨by omega,by omega,?_,⟨(0,S),ht,rfl⟩,⟨(R,0),hr,by simp⟩,
    ⟨(R,0),hr,rfl⟩,⟨(0,S),ht,by simp⟩⟩
  rw [← rectangle_eq_foundation,primalDomain_eq]
  exact Finset.sdiff_subset

theorem integerFaces_mem (M : Diagram) (p : Ferrers.Point) : ofNatPoint p∈integerFaces M ↔ p∈M := by
  simp only [integerFaces,Finset.mem_image,ofNatPoint_injective.eq_iff]
  simp

theorem encodedVacancies_primal {R S : ℕ} {M : Diagram} (hfit : M⊆faceRectangle R S) :
    encodedVacancies R S (primalDomain R S M)=M := by
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
    have hb:=mem_faceRectangle.mp (hfit hp)
    refine ⟨by omega,by omega,?_⟩
    rw [primalDomain_eq]
    intro h
    exact (Finset.mem_sdiff.mp h).2 ((integerFaces_mem M p).mpr hp)

theorem primal_no_interior {R S : ℕ} {M : Diagram} (hM : IsFerrers M) (hfit : M⊆faceRectangle R S) :
    canonicalInteriorCount R S (primalDomain R S M)=0 := by
  apply canonicalInteriorCount_zero_of_ferrers
  simpa only [encodedVacancies_primal hfit] using hM

theorem remainingFaces_primal {R S : ℕ} {M : Diagram} (hM : IsFerrers M) (hfit : M⊆faceRectangle R S) :
    PrimalDirichlet.remainingFaces R S (primalDomain R S M)=faceRectangle R S \ M := by
  unfold PrimalDirichlet.remainingFaces
  rw [encodedVacancies_primal hfit,foundation_markedFaces hM hfit,foundation_faceIndices]

/-- Complete determinant bridge with connectedness and hull hypotheses discharged. -/
theorem primal_treeCount_eq_dirichlet {R S : ℕ} {M : Diagram} (hR : 1≤R) (hS : 1≤S)
    (hM : IsFerrers M) (hfit : M⊆faceRectangle R S) :
    (treeCount (primalDomain R S M) : ℝ)=
      Matrix.det (fourIminusAdjacency (faceRectangle R S \ M)) := by
  have h := (PrimalDirichlet.treeCount_pair_eq_dirichlet hR hS (primal_hull hfit)
    (primal_connected hM hfit) (primal_no_interior hM hfit)).2
  rw [remainingFaces_primal hM hfit] at h
  exact h

end
end SpanningTreeIsoperimetry.FerrersPrimalBridge
