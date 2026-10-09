import SpanningTreeIsoperimetry.PrimalDirichlet
import SpanningTreeIsoperimetry.DomainIsometries
import SpanningTreeIsoperimetry.ComparisonDomain

/-! Concrete primal corner strips and their boundary Green minors. -/
namespace SpanningTreeIsoperimetry.CornerStripBridge

open CornerEnergy Ferrers DomainIsometries SquareMaximality.Boundary
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[simp] theorem mem_cornerStrip {r s k : ℕ} {p : Vertex} :
    p ∈ cornerStrip r s k ↔
      0≤p.1 ∧ p.1<r ∧ 0≤p.2 ∧ p.2<s ∧ (p.1≠0 ∨ (k : ℤ)≤p.2) := by
  simp only [cornerStrip,Finset.mem_sdiff,mem_rectangle]
  omega

theorem rowExtension_rotate {R S k : ℕ} (hk : k≤S) :
    (ComparisonDomain.rowExtension (S+1) R (S+1-k)).image (quarterTurn S)=
      cornerStrip (R+1) (S+1) k := by
  have hcast : ((S+1-k : ℕ) : ℤ)=(S : ℤ)+1-k := by
    rw [Nat.cast_sub (by omega : k≤S+1)]
    push_cast
    rfl
  ext p
  constructor
  · intro hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    rw [ComparisonDomain.mem_rowExtension] at hq
    rw [mem_cornerStrip]
    simp only [quarterTurn,Equiv.coe_fn_mk,Prod.fst,Prod.snd]
    rw [hcast] at hq
    push_cast at hq ⊢
    omega
  · intro hp
    rw [mem_cornerStrip] at hp
    refine Finset.mem_image.mpr ⟨((S : ℤ)-p.2,p.1),?_,?_⟩
    · rw [ComparisonDomain.mem_rowExtension,hcast]
      push_cast
      omega
    · ext <;> simp [quarterTurn]

theorem cornerStrip_connected {R S k : ℕ} (hR : 1≤R) (hk : k≤S) :
    (domainGraph (cornerStrip (R+1) (S+1) k)).Connected := by
  have h := ComparisonDomain.rowExtension_connected (by omega : 0<S+1)
    (by omega : 0<R) (S+1-k)
  rw [← domainGraph_eq_foundation] at h
  have ht := (quarterTurnGraphIso S
    (ComparisonDomain.rowExtension (S+1) R (S+1-k))).connected_iff.mp h
  rwa [rowExtension_rotate hk] at ht

theorem cornerStrip_hull {R S k : ℕ} (hR : 1≤R) (hk : k≤S) :
    SquareMaximality.IsRectHull (cornerStrip (R+1) (S+1) k) 0 0 (R+1) (S+1) := by
  have htop (x : ℤ) (hx : 0≤x ∧ x≤R) : (x,(S : ℤ)) ∈ cornerStrip (R+1) (S+1) k := by
    rw [mem_cornerStrip]
    push_cast
    omega
  have hright (y : ℤ) (hy : 0≤y ∧ y≤S) : ((R : ℤ),y) ∈ cornerStrip (R+1) (S+1) k := by
    rw [mem_cornerStrip]
    push_cast
    omega
  refine ⟨by omega,by omega,?_,⟨(0,S),htop 0 (by omega),rfl⟩,
    ⟨(R,0),hright 0 (by omega),by simp⟩,⟨(R,0),hright 0 (by omega),rfl⟩,
    ⟨(0,S),htop 0 (by omega),by simp⟩⟩
  rw [← rectangle_eq_foundation]
  exact Finset.sdiff_subset

def verticalDiagram (k : ℕ) : Diagram := {(0 : ℕ)} ×ˢ Finset.range k

@[simp] theorem mem_verticalDiagram {k : ℕ} {p : Ferrers.Point} :
    p ∈ verticalDiagram k ↔ p.1=0 ∧ p.2<k := by
  rcases p with ⟨x,y⟩
  simp [verticalDiagram,eq_comm,and_comm]

theorem verticalDiagram_ferrers (k : ℕ) : IsFerrers (verticalDiagram k) := by
  intro p hp q hqx hqy
  rw [mem_verticalDiagram] at hp ⊢
  omega

theorem verticalDiagram_subset {R S k : ℕ} (hR : 1≤R) (hk : k≤S) :
    verticalDiagram k ⊆ faceRectangle R S := by
  intro p hp
  rw [mem_verticalDiagram] at hp
  rw [mem_faceRectangle]
  omega

theorem encodedVacancies_cornerStrip {R S k : ℕ} (hk : k≤S) :
    encodedVacancies R S (cornerStrip (R+1) (S+1) k)=verticalDiagram k := by
  ext p
  simp only [mem_encodedVacancies,mem_cornerStrip,ofNatPoint,mem_verticalDiagram]
  push_cast
  omega

theorem boundaryVacancies_verticalDiagram (R S k : ℕ) :
    boundaryVacancies R S (verticalDiagram k)=verticalDiagram k := by
  apply Finset.Subset.antisymm (boundaryVacancies_subset R S _)
  intro p hp
  apply mem_boundaryVacancies.mpr
  refine ⟨hp,⟨p,hp⟩,Or.inl (mem_verticalDiagram.mp hp).1,SimpleGraph.Reachable.refl _⟩

theorem cornerStrip_no_interior {R S k : ℕ} (hk : k≤S) :
    canonicalInteriorCount R S (cornerStrip (R+1) (S+1) k)=0 := by
  have hi : interiorVacancies R S (encodedVacancies R S (cornerStrip (R+1) (S+1) k))=∅ := by
    rw [encodedVacancies_cornerStrip hk,interiorVacancies,boundaryVacancies_verticalDiagram,
      Finset.sdiff_self]
  by_contra hz
  let i : Fin (canonicalInteriorCount R S (cornerStrip (R+1) (S+1) k)) := ⟨0,Nat.pos_of_ne_zero hz⟩
  let c := (canonicalInteriorEquiv R S (cornerStrip (R+1) (S+1) k)).symm i
  obtain ⟨p,hp⟩ := interiorComponent_nonempty R S
    (canonicalVacancies R S (cornerStrip (R+1) (S+1) k)) c
  have hpI := interiorComponent_subset_interiorVacancies R S
    (canonicalVacancies R S (cornerStrip (R+1) (S+1) k)) c hp
  simpa only [canonicalVacancies,hi,Finset.notMem_empty] using hpI

theorem remainingFaces_cornerStrip {R S k : ℕ} (hR : 1≤R) (hk : k≤S) :
    PrimalDirichlet.remainingFaces R S (cornerStrip (R+1) (S+1) k)=
      faceRectangle R S \ verticalDiagram k := by
  unfold PrimalDirichlet.remainingFaces
  rw [encodedVacancies_cornerStrip hk,foundation_markedFaces (verticalDiagram_ferrers k)
    (verticalDiagram_subset hR hk),foundation_faceIndices]

/-- Exact face-determinant formula for the actual primal corner strip. -/
theorem cornerStrip_treeCount_eq_dirichlet {R S k : ℕ}
    (hR : 1≤R) (hS : 1≤S) (hk : k≤S) :
    (treeCount (cornerStrip (R+1) (S+1) k) : ℝ)=
      Matrix.det (fourIminusAdjacency (faceRectangle R S \ verticalDiagram k)) := by
  have h := (PrimalDirichlet.treeCount_pair_eq_dirichlet hR hS
    (cornerStrip_hull hR hk) (cornerStrip_connected hR hk) (cornerStrip_no_interior hk)).2
  rw [remainingFaces_cornerStrip hR hk] at h
  exact h

/-- The deletion factor is the actual leading boundary Green minor. -/
theorem cornerStrip_treeCount_eq_greenMinor {R S k : ℕ}
    (hR : 1≤R) (hS : 1≤S) (hk : k≤S) :
    (treeCount (cornerStrip (R+1) (S+1) k) : ℝ)=
      (treeCount (rectangle (R+1) (S+1)) : ℝ)*
        Matrix.det (greenMinor (verticalDiagram_subset hR hk)) := by
  have hfull := (PrimalDirichlet.treeCount_pair_eq_dirichlet hR hS
    (cornerStrip_hull hR hk) (cornerStrip_connected hR hk) (cornerStrip_no_interior hk)).1
  rw [cornerStrip_treeCount_eq_dirichlet hR hS hk,hfull]
  exact greenMinor_det_identity (Finset.Subset.refl (faceRectangle R S))
    (verticalDiagram_subset hR hk)

theorem integerFaces_faceRectangle (m n : ℕ) :
    integerFaces (faceRectangle m n)=rectangle m n := by
  ext v
  constructor
  · intro hv
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    have hp' := mem_faceRectangle.mp hp
    rw [mem_rectangle]
    exact ⟨by simp [ofNatPoint],by dsimp [ofNatPoint]; exact_mod_cast hp'.1,
      by simp [ofNatPoint],by dsimp [ofNatPoint]; exact_mod_cast hp'.2⟩
  · intro hv
    have hb := mem_rectangle.mp hv
    apply Finset.mem_image.mpr
    refine ⟨(v.1.toNat,v.2.toNat),mem_faceRectangle.mpr ⟨by omega,by omega⟩,?_⟩
    ext <;> simp [ofNatPoint,Int.toNat_of_nonneg hb.1,Int.toNat_of_nonneg hb.2.2.1]

theorem integerFaces_verticalDiagram (k : ℕ) :
    integerFaces (verticalDiagram k)=rectangle 1 k := by
  have h : verticalDiagram k=faceRectangle 1 k := by
    ext p
    rw [mem_verticalDiagram,mem_faceRectangle]
    omega
  rw [h,integerFaces_faceRectangle]

theorem integerFaces_strip_faces (R S k : ℕ) :
    integerFaces (faceRectangle R S \ verticalDiagram k)=cornerStrip R S k := by
  unfold integerFaces
  rw [Finset.image_sdiff _ _ ofNatPoint_injective]
  change integerFaces (faceRectangle R S) \ integerFaces (verticalDiagram k)=_
  rw [integerFaces_faceRectangle,integerFaces_verticalDiagram]
  rfl

end SpanningTreeIsoperimetry.CornerStripBridge
