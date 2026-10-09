import SpanningTreeIsoperimetry.CornerStripBridge
import SpanningTreeIsoperimetry.StripPolarization
import SpanningTreeIsoperimetry.ThinRectangles

/-! The strip orientation and adjacent-hull comparisons for actual primal
spanning-tree counts, including the one-dimensional endpoints. -/
namespace SpanningTreeIsoperimetry.StripTreeComparisons

open CornerStripBridge CornerEnergy Ferrers DomainIsometries StripPolarization
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def horizontalCornerStrip (r s k : ℕ) : Domain := rectangle r s \ rectangle k 1

theorem horizontal_eq_transpose (r s k : ℕ) :
    horizontalCornerStrip r s k=transposeDomain (cornerStrip s r k) := by
  ext p
  simp only [horizontalCornerStrip,mem_transposeDomain,cornerStrip,Finset.mem_sdiff,mem_rectangle]
  simp only [Prod.fst_swap,Prod.snd_swap]
  omega

@[simp] theorem faceDeterminant_empty (z : ℝ) : faceDeterminant ∅ z=1 := by
  haveI : IsEmpty ((∅ : Domain) : Set Vertex) := ⟨fun p => Finset.notMem_empty p.val p.property⟩
  exact Matrix.det_isEmpty

theorem treeCount_transpose (A : Domain) : treeCount (transposeDomain A)=treeCount A := by
  change SquareMaximality.treeCount (domainGraph (transposeDomain A))=
    SquareMaximality.treeCount (domainGraph A)
  exact (SquareMaximality.treeCount_congr (transposeGraphIso A)).symm

theorem cornerStrip_count_face_nondegenerate {R S k : ℕ}
    (hR : 1≤R) (hS : 1≤S) (hk : k≤S) :
    (treeCount (cornerStrip (R+1) (S+1) k) : ℝ)=faceDeterminant (faceStripY R S k) 4 := by
  have h := cornerStrip_treeCount_eq_dirichlet hR hS hk
  have hi := face_dirichlet_det_eq_integer (faceRectangle R S \ verticalDiagram k)
  change Matrix.det (SquareMaximality.Boundary.fourIminusAdjacency
      (faceRectangle R S \ verticalDiagram k))=
    faceDeterminant (integerFaces (faceRectangle R S \ verticalDiagram k)) 4 at hi
  have he : integerFaces (faceRectangle R S \ verticalDiagram k)=faceStripY R S k :=
    integerFaces_strip_faces R S k
  exact h.trans (hi.trans (congrArg (fun U => faceDeterminant U 4) he))

theorem cornerStrip_count_face {r s k : ℕ}
    (hr : 0<r) (hs : 0<s) (hk : k<min r s) :
    (treeCount (cornerStrip r s k) : ℝ)=faceDeterminant (faceStripY (r-1) (s-1) k) 4 := by
  by_cases hr1 : r=1
  · subst r
    have hk0 : k=0 := by omega
    subst k
    rw [cornerStrip_zero,treeCount_rectangle_one_width hs]
    have he : faceStripY 0 (s-1) 0=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hm := mem_faceStripY.mp hp
      omega
    simpa only [Nat.sub_self,he,faceDeterminant_empty,Nat.cast_one]
  by_cases hs1 : s=1
  · subst s
    have hk0 : k=0 := by omega
    subst k
    rw [cornerStrip_zero,treeCount_rectangle_one_height hr]
    have he : faceStripY (r-1) 0 0=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hm := mem_faceStripY.mp hp
      omega
    simpa only [Nat.sub_self,he,faceDeterminant_empty,Nat.cast_one]
  obtain ⟨R,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  obtain ⟨S,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  simpa only [Nat.succ_sub_one] using cornerStrip_count_face_nondegenerate
    (by omega : 1≤R) (by omega : 1≤S) (by omega : k≤S)

theorem horizontalCornerStrip_count_face {r s k : ℕ}
    (hr : 0<r) (hs : 0<s) (hk : k<min r s) :
    (treeCount (horizontalCornerStrip r s k) : ℝ)=
      faceDeterminant (faceStripX (r-1) (s-1) k) 4 := by
  rw [horizontal_eq_transpose,treeCount_transpose,cornerStrip_count_face hs hr (by omega)]
  rw [faceDeterminant_transpose,transpose_faceStripY]

theorem orientation_treeCount {r s k : ℕ} (hr : 1≤r) (hrs : r≤s) (hk : k<r) :
    treeCount (horizontalCornerStrip r s k)≤treeCount (cornerStrip r s k) := by
  have h := orientation_determinant (by omega : r-1≤s-1) (by omega : k≤r-1) 4 le_rfl
  rw [← horizontalCornerStrip_count_face (by omega) (by omega) (by omega),
    ← cornerStrip_count_face (by omega) (by omega) (by omega)] at h
  exact_mod_cast h

theorem orientation_treeCount_eq_iff {r s k : ℕ} (hr : 1≤r) (hrs : r≤s) (hk : k<r) :
    treeCount (horizontalCornerStrip r s k)=treeCount (cornerStrip r s k) ↔ r=s ∨ k≤1 := by
  have h := orientation_determinant_eq_iff (by omega : r-1≤s-1) (by omega : k≤r-1) 4 le_rfl
  rw [← horizontalCornerStrip_count_face (by omega) (by omega) (by omega),
    ← cornerStrip_count_face (by omega) (by omega) (by omega)] at h
  have hside : r-1=s-1 ↔ r=s := by omega
  simpa only [Nat.cast_inj,hside] using h

theorem adjacent_hull_treeCount {r s k : ℕ} (hr : 1≤r) (hrs : r≤s) (hk : k<r)
    (hgap : s-r+1≤k) :
    treeCount (cornerStrip r s k)≤treeCount (horizontalCornerStrip (r-1) (s+1) (k-(s-r+1))) ∧
    treeCount (horizontalCornerStrip (r-1) (s+1) (k-(s-r+1)))≤
      treeCount (cornerStrip (r-1) (s+1) (k-(s-r+1))) := by
  have h := adjacent_hull_faces hr hrs hk hgap 4 le_rfl
  have hy := cornerStrip_count_face (by omega : 0<r) (by omega : 0<s) (by omega : k<min r s)
  have hx' := horizontalCornerStrip_count_face (by omega : 0<r-1) (by omega : 0<s+1)
    (by omega : k-(s-r+1)<min (r-1) (s+1))
  have hy' := cornerStrip_count_face (by omega : 0<r-1) (by omega : 0<s+1)
    (by omega : k-(s-r+1)<min (r-1) (s+1))
  simp only [Nat.sub_sub,Nat.reduceAdd,Nat.add_sub_cancel] at hx' hy'
  rw [← hy,← hx',← hy'] at h
  exact_mod_cast h

theorem adjacent_hull_treeCount_eq_iff {r s k : ℕ} (hr : 1≤r) (hrs : r≤s) (hk : k<r)
    (hgap : s-r+1≤k) :
    treeCount (cornerStrip r s k)=treeCount (cornerStrip (r-1) (s+1) (k-(s-r+1))) ↔
      s-1-k≤1 ∧ k-(s-r+1)≤1 := by
  have h := adjacent_hull_faces_eq_iff hr hrs hk hgap 4 le_rfl
  have hy := cornerStrip_count_face (by omega : 0<r) (by omega : 0<s) (by omega : k<min r s)
  have hy' := cornerStrip_count_face (by omega : 0<r-1) (by omega : 0<s+1)
    (by omega : k-(s-r+1)<min (r-1) (s+1))
  simp only [Nat.sub_sub,Nat.reduceAdd,Nat.add_sub_cancel] at hy'
  rw [← hy,← hy'] at h
  exact_mod_cast h

end SpanningTreeIsoperimetry.StripTreeComparisons
