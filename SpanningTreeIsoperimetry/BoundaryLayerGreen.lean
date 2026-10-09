import SpanningTreeIsoperimetry.QuadrantBoundaryGreen
import SpanningTreeIsoperimetry.BoundaryGreenPolynomials

/-! The first two actual quadrant Green rows, obtained from finite
Dirichlet equations and the checked boundary exhaustion. -/
namespace SpanningTreeIsoperimetry.BoundaryLayerGreen

open Ferrers CornerEnergy BoundaryGreenPolynomials Filter SquareMaximality.Boundary
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

abbrev window (N : ℕ) := QuadrantBoundaryGreen.window 4 N
abbrev bottomSite (N : ℕ) (i : Fin 4) := QuadrantBoundaryGreen.boundarySite N i
abbrev boundaryEntry (N : ℕ) (i j : Fin 4) := QuadrantBoundaryGreen.greenEntry N i j

def lowerIndex (i : Fin 3) : Fin 4 := ⟨i.val,by have hi:=i.isLt; omega⟩
def nextIndex (i : Fin 3) : Fin 4 := ⟨i.val+1,by have hi:=i.isLt; omega⟩
def prevIndex (i : Fin 3) : Fin 4 := ⟨i.val-1,by have hi:=i.isLt; omega⟩

def upperSite (N : ℕ) (i : Fin 3) : {p // p∈window N} :=
  ⟨(i.val,1),by
    change (i.val,1)∈faceIndices (N+5) (N+5)
    rw [mem_faceIndices]
    have hi:=i.isLt
    omega⟩

theorem window_posDef (N : ℕ) : (fourIminusAdjacency (window N)).PosDef := by
  apply dirichlet_posDef (m := N+5) (n := N+5)
  change faceIndices (N+5) (N+5)⊆faceRectangle (N+5) (N+5)
  rw [foundation_faceIndices]

theorem green_symm (N : ℕ) (p q : {p // p∈window N}) :
    (fourIminusAdjacency (window N))⁻¹ p q=(fourIminusAdjacency (window N))⁻¹ q p := by
  simpa only [star_trivial] using ((window_posDef N).isHermitian.inv.apply q p)

theorem bottomSite_eq (N : ℕ) (i j : Fin 4) : bottomSite N i=bottomSite N j ↔ i=j := by
  simp only [bottomSite,QuadrantBoundaryGreen.boundarySite,Subtype.ext_iff,Prod.ext_iff,
    and_true,Fin.ext_iff]

theorem row_entry (N : ℕ) (i : Fin 3) (p : {p // p∈window N}) :
    fourIminusAdjacency (window N) (bottomSite N (lowerIndex i)) p=
      (if p=bottomSite N (lowerIndex i) then 4 else 0)-
      (if p=bottomSite N (nextIndex i) then 1 else 0)-
      (if i.val=0 then 0 else if p=bottomSite N (prevIndex i) then 1 else 0)-
      (if p=upperSite N i then 1 else 0) := by
  have he : bottomSite N (lowerIndex i)=p ↔ p=bottomSite N (lowerIndex i) := eq_comm
  have ha : natManhattanDist (bottomSite N (lowerIndex i)).val p.val=1 ↔
      p=bottomSite N (nextIndex i) ∨ (i.val≠0 ∧ p=bottomSite N (prevIndex i)) ∨ p=upperSite N i := by
    simp only [bottomSite,QuadrantBoundaryGreen.boundarySite,lowerIndex,nextIndex,prevIndex,
      upperSite,natManhattanDist,Nat.dist,Subtype.ext_iff,Prod.ext_iff]
    omega
  have hnp : bottomSite N (nextIndex i)≠bottomSite N (prevIndex i) := by
    intro h
    simp only [bottomSite_eq,Fin.ext_iff,nextIndex,prevIndex] at h
    omega
  have hnu : bottomSite N (nextIndex i)≠upperSite N i := by
    intro h
    have hy:=congrArg (fun p : {p // p∈window N} => p.val.2) h
    norm_num [bottomSite,QuadrantBoundaryGreen.boundarySite,upperSite] at hy
  have hpu : bottomSite N (prevIndex i)≠upperSite N i := by
    intro h
    have hy:=congrArg (fun p : {p // p∈window N} => p.val.2) h
    norm_num [bottomSite,QuadrantBoundaryGreen.boundarySite,upperSite] at hy
  have hind : (if natManhattanDist (bottomSite N (lowerIndex i)).val p.val=1 then (1 : ℝ) else 0)=
      (if p=bottomSite N (nextIndex i) then 1 else 0)+
      (if i.val=0 then 0 else if p=bottomSite N (prevIndex i) then 1 else 0)+
      (if p=upperSite N i then 1 else 0) := by
    simp only [ha]
    by_cases hi : i.val=0
    · by_cases hn : p=bottomSite N (nextIndex i)
      · have hu : p≠upperSite N i := by intro h; exact hnu (hn.symm.trans h)
        simp [hi,hn,hu,hnu]
      · simp [hi,hn]
    · by_cases hn : p=bottomSite N (nextIndex i)
      · have hp : p≠bottomSite N (prevIndex i) := by intro h; exact hnp (hn.symm.trans h)
        have hu : p≠upperSite N i := by intro h; exact hnu (hn.symm.trans h)
        simp [hi,hn,hp,hu,hnp,hnu]
      · by_cases hp : p=bottomSite N (prevIndex i)
        · have hu : p≠upperSite N i := by intro h; exact hpu (hp.symm.trans h)
          simp [hi,hn,hp,hu,hnp.symm,hpu]
        · simp [hi,hn,hp]
  simp only [fourIminusAdjacency_apply,he]
  rw [hind]
  ring

theorem row_green_equation (N : ℕ) (i : Fin 3) (q : {p // p∈window N}) :
    4*(fourIminusAdjacency (window N))⁻¹ (bottomSite N (lowerIndex i)) q-
      (fourIminusAdjacency (window N))⁻¹ (bottomSite N (nextIndex i)) q-
      (if i.val=0 then 0 else (fourIminusAdjacency (window N))⁻¹ (bottomSite N (prevIndex i)) q)-
      (fourIminusAdjacency (window N))⁻¹ (upperSite N i) q=
      (if bottomSite N (lowerIndex i)=q then 1 else 0) := by
  have h := congrArg (fun M => M (bottomSite N (lowerIndex i)) q)
    (Matrix.mul_nonsing_inv (fourIminusAdjacency (window N))
      (isUnit_iff_ne_zero.mpr (window_posDef N).det_pos.ne'))
  simp only [Matrix.mul_apply,Matrix.one_apply] at h
  simp_rw [row_entry,sub_mul] at h
  simp only [Finset.sum_sub_distrib,ite_mul,zero_mul,Finset.sum_ite_irrel,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,one_mul,Finset.sum_const_zero] at h
  exact h

def crossEntry (N : ℕ) (i : Fin 3) (j : Fin 4) : ℝ :=
  4*boundaryEntry N (lowerIndex i) j-boundaryEntry N (nextIndex i) j-
    (if i.val=0 then 0 else boundaryEntry N (prevIndex i) j)-
    (if lowerIndex i=j then 1 else 0)

theorem crossEntry_eq (N : ℕ) (i : Fin 3) (j : Fin 4) :
    (fourIminusAdjacency (window N))⁻¹ (upperSite N i) (bottomSite N j)=crossEntry N i j := by
  have h := row_green_equation N i (bottomSite N j)
  simp only [bottomSite_eq] at h
  change 4*boundaryEntry N (lowerIndex i) j-boundaryEntry N (nextIndex i) j-
    (if i.val=0 then 0 else boundaryEntry N (prevIndex i) j)-
    (fourIminusAdjacency (window N))⁻¹ (upperSite N i) (bottomSite N j)=
    (if lowerIndex i=j then 1 else 0) at h
  unfold crossEntry
  linarith

theorem crossEntry_symm (N : ℕ) (i : Fin 3) (j : Fin 4) :
    (fourIminusAdjacency (window N))⁻¹ (bottomSite N j) (upperSite N i)=crossEntry N i j :=
  (green_symm N _ _).trans (crossEntry_eq N i j)

def upperEntry (N : ℕ) (i j : Fin 3) : ℝ :=
  4*crossEntry N i (lowerIndex j)-crossEntry N i (nextIndex j)-
    (if j.val=0 then 0 else crossEntry N i (prevIndex j))

theorem upperEntry_eq (N : ℕ) (i j : Fin 3) :
    (fourIminusAdjacency (window N))⁻¹ (upperSite N i) (upperSite N j)=upperEntry N i j := by
  have h := row_green_equation N j (upperSite N i)
  have hne : bottomSite N (lowerIndex j)≠upperSite N i := by
    intro he
    have hy := congrArg (fun p : {p // p∈window N} => p.val.2) he
    norm_num [bottomSite,QuadrantBoundaryGreen.boundarySite,upperSite] at hy
  rw [if_neg hne,crossEntry_symm N i (lowerIndex j),crossEntry_symm N i (nextIndex j),
    crossEntry_symm N i (prevIndex j),green_symm N (upperSite N j) (upperSite N i)] at h
  unfold upperEntry
  linarith

def crossValue (t : ℝ) (i : Fin 3) (j : Fin 4) : ℝ :=
  4*cornerEntry t (lowerIndex i) j-cornerEntry t (nextIndex i) j-
    (if i.val=0 then 0 else cornerEntry t (prevIndex i) j)-
    (if lowerIndex i=j then 1 else 0)

def upperValue (t : ℝ) (i j : Fin 3) : ℝ :=
  4*crossValue t i (lowerIndex j)-crossValue t i (nextIndex j)-
    (if j.val=0 then 0 else crossValue t i (prevIndex j))

theorem boundaryEntry_tendsto (i j : Fin 4) :
    Tendsto (fun N => boundaryEntry N i j) atTop (𝓝 (cornerEntry (1/Real.pi) i j)) := by
  have h := QuadrantBoundaryGreen.greenEntry_tendsto (by decide : 4≤4) i j
  simp only [QuadrantBoundaryGreen.greenValue,boundaryValueNine_eq] at h
  exact h

theorem crossEntry_tendsto (i : Fin 3) (j : Fin 4) :
    Tendsto (fun N => crossEntry N i j) atTop (𝓝 (crossValue (1/Real.pi) i j)) := by
  have h0:=boundaryEntry_tendsto (lowerIndex i) j
  have h1:=boundaryEntry_tendsto (nextIndex i) j
  have hp : Tendsto (fun N => if i.val=0 then (0 : ℝ) else boundaryEntry N (prevIndex i) j)
      atTop (𝓝 (if i.val=0 then 0 else cornerEntry (1/Real.pi) (prevIndex i) j)) := by
    by_cases hi : i.val=0
    · simpa only [hi,ite_true] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · simpa only [hi,ite_false] using boundaryEntry_tendsto (prevIndex i) j
  exact (((h0.const_mul (4 : ℝ)).sub h1).sub hp).sub_const (if lowerIndex i=j then 1 else 0)

theorem upperEntry_tendsto (i j : Fin 3) :
    Tendsto (fun N => upperEntry N i j) atTop (𝓝 (upperValue (1/Real.pi) i j)) := by
  have h0:=crossEntry_tendsto i (lowerIndex j)
  have h1:=crossEntry_tendsto i (nextIndex j)
  have hp : Tendsto (fun N => if j.val=0 then (0 : ℝ) else crossEntry N i (prevIndex j))
      atTop (𝓝 (if j.val=0 then 0 else crossValue (1/Real.pi) i (prevIndex j))) := by
    by_cases hj : j.val=0
    · simpa only [hj,ite_true] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · simpa only [hj,ite_false] using crossEntry_tendsto i (prevIndex j)
  exact ((h0.const_mul (4 : ℝ)).sub h1).sub hp

def twoRowSite (N : ℕ) (p : Fin 3 × Fin 2) : {p // p∈window N} :=
  ⟨(p.1.val,p.2.val),by
    change (p.1.val,p.2.val)∈faceIndices (N+5) (N+5)
    rw [mem_faceIndices]
    have hx:=p.1.isLt; have hy:=p.2.isLt
    omega⟩

def twoRowFinite (N : ℕ) : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℝ :=
  fun p q => (fourIminusAdjacency (window N))⁻¹ (twoRowSite N p) (twoRowSite N q)

def twoRowValue (t : ℝ) : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℝ :=
  fun p q => if p.2=0 then
    (if q.2=0 then cornerEntry t (lowerIndex p.1) (lowerIndex q.1)
      else crossValue t q.1 (lowerIndex p.1))
    else (if q.2=0 then crossValue t p.1 (lowerIndex q.1) else upperValue t p.1 q.1)

theorem twoRowFinite_eq (N : ℕ) (p q : Fin 3 × Fin 2) : twoRowFinite N p q=
    (if p.2=0 then (if q.2=0 then boundaryEntry N (lowerIndex p.1) (lowerIndex q.1)
      else crossEntry N q.1 (lowerIndex p.1))
    else (if q.2=0 then crossEntry N p.1 (lowerIndex q.1) else upperEntry N p.1 q.1)) := by
  rcases p with ⟨px,py⟩
  rcases q with ⟨qx,qy⟩
  fin_cases py <;> fin_cases qy
  · rfl
  · exact crossEntry_symm N qx (lowerIndex px)
  · exact crossEntry_eq N px (lowerIndex qx)
  · exact upperEntry_eq N px qx

theorem twoRowFinite_tendsto : Tendsto twoRowFinite atTop (𝓝 (twoRowValue (1/Real.pi))) := by
  apply tendsto_pi_nhds.mpr
  intro p
  apply tendsto_pi_nhds.mpr
  intro q
  simp only [twoRowFinite_eq,twoRowValue]
  rcases p with ⟨px,py⟩
  rcases q with ⟨qx,qy⟩
  fin_cases py <;> fin_cases qy
  · exact boundaryEntry_tendsto (lowerIndex px) (lowerIndex qx)
  · exact crossEntry_tendsto qx (lowerIndex px)
  · exact crossEntry_tendsto px (lowerIndex qx)
  · exact upperEntry_tendsto px qx

end
end SpanningTreeIsoperimetry.BoundaryLayerGreen
