import SpanningTreeIsoperimetry.FoundationsBridge
import SquareMaximality.Boundary.Faces
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Finite induced-graph transport for the coordinate maps used by strip
domains, and the natural-face/integer-domain determinant identification. -/
namespace SpanningTreeIsoperimetry.DomainIsometries

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def inducedImageIso {V W : Type*} [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (hadj : ∀ p q, H.Adj (e p) (e q) ↔ G.Adj p q) (A : Finset V) :
    G.induce (A : Set V) ≃g H.induce (A.image e : Set W) :=
  { Equiv.ofBijective (fun p => ⟨e p,Finset.mem_image_of_mem _ p.property⟩)
      ⟨by
        intro p q hpq
        apply Subtype.ext
        exact e.injective (congrArg Subtype.val hpq),
       by
        intro q
        obtain ⟨p,hp,he⟩ := Finset.mem_image.mp q.property
        exact ⟨⟨p,hp⟩,Subtype.ext he⟩⟩ with
    map_rel_iff' := by intro p q; exact hadj p q }

def quarterTurn (height : ℤ) : Vertex ≃ Vertex where
  toFun p := (p.2,height-p.1)
  invFun p := (height-p.2,p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

theorem quarterTurn_adj (height : ℤ) (p q : Vertex) :
    lattice.Adj (quarterTurn height p) (quarterTurn height q) ↔ lattice.Adj p q := by
  simp only [lattice,quarterTurn,Equiv.coe_fn_mk]
  rw [abs_eq (by norm_num : (0 : ℤ)≤1),abs_eq (by norm_num : (0 : ℤ)≤1),
    abs_eq (by norm_num : (0 : ℤ)≤1)]
  omega

noncomputable def quarterTurnGraphIso (height : ℤ) (A : Domain) :
    domainGraph A ≃g domainGraph (A.image (quarterTurn height)) :=
  inducedImageIso lattice lattice (quarterTurn height).toEmbedding (quarterTurn_adj height) A

theorem treeCount_image_quarterTurn (height : ℤ) (A : Domain) :
    treeCount (A.image (quarterTurn height))=treeCount A := by
  change SquareMaximality.treeCount (domainGraph (A.image (quarterTurn height)))=
    SquareMaximality.treeCount (domainGraph A)
  exact (SquareMaximality.treeCount_congr (quarterTurnGraphIso height A)).symm

open SquareMaximality.Boundary

def integerFaces (U : Finset LatticePoint) : Domain := U.image ofNatPoint

theorem ofNatPoint_adj (p q : LatticePoint) :
    lattice.Adj (ofNatPoint p) (ofNatPoint q) ↔ faceLattice.Adj p q := by
  change (((p.1 : ℤ)=q.1 ∧ |(p.2 : ℤ)-q.2|=1) ∨
    ((p.2 : ℤ)=q.2 ∧ |(p.1 : ℤ)-q.1|=1)) ↔
      Nat.dist p.1 q.1+Nat.dist p.2 q.2=1
  rw [abs_eq (by norm_num : (0 : ℤ)≤1),abs_eq (by norm_num : (0 : ℤ)≤1)]
  unfold Nat.dist
  omega

noncomputable def integerFacesGraphIso (U : Finset LatticePoint) :
    faceGraph U ≃g domainGraph (integerFaces U) :=
  inducedImageIso faceLattice lattice ⟨ofNatPoint,ofNatPoint_injective⟩ ofNatPoint_adj U

theorem shiftedAdjacency_det_iso {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) (z : ℝ) :
    Matrix.det (z • (1 : Matrix V V ℝ)-G.adjMatrix ℝ)=
      Matrix.det (z • (1 : Matrix W W ℝ)-H.adjMatrix ℝ) := by
  have hm : (z • (1 : Matrix W W ℝ)-H.adjMatrix ℝ).submatrix e e=
      z • (1 : Matrix V V ℝ)-G.adjMatrix ℝ := by
    ext i j
    simp only [Matrix.submatrix_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.one_apply,SimpleGraph.adjMatrix_apply,e.map_adj_iff,e.injective.eq_iff]
  have h := congrArg Matrix.det hm
  exact h.symm.trans (Matrix.det_submatrix_equiv_self e.toEquiv
    (z • (1 : Matrix W W ℝ)-H.adjMatrix ℝ))

noncomputable local instance (S : Domain) : DecidableRel (domainGraph S).Adj := Classical.decRel _

theorem face_dirichlet_det_eq_integer (U : Finset LatticePoint) :
    Matrix.det (fourIminusAdjacency U)=
      Matrix.det ((4 : ℝ) • (1 : Matrix (integerFaces U : Set Vertex) (integerFaces U : Set Vertex) ℝ)-
        (domainGraph (integerFaces U)).adjMatrix ℝ) := by
  have h := shiftedAdjacency_det_iso (faceGraph U) (domainGraph (integerFaces U)) (integerFacesGraphIso U) 4
  have hm : fourIminusAdjacency U=(4 : ℝ) • (1 : Matrix U U ℝ)-(faceGraph U).adjMatrix ℝ := by
    ext i j
    by_cases hij : i=j <;> by_cases ha : (faceGraph U).Adj i j <;>
      simp [fourIminusAdjacency,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply,
        SimpleGraph.adjMatrix_apply,hij,ha]
  rw [hm]
  exact h

end SpanningTreeIsoperimetry.DomainIsometries
