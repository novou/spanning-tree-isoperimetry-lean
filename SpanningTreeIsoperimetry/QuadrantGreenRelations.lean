import SpanningTreeIsoperimetry.SingletonEnergy

/-! Actual quadrant inverse entries satisfy symmetry and the corner
Dirichlet equation. These identities evaluate the three-cell Green minor. -/
namespace SpanningTreeIsoperimetry.QuadrantGreenRelations

open Ferrers CornerEnergy QuadrantGreen Filter SquareMaximality.Boundary
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def topSite (N : ℕ) : {p // p∈window N} :=
  ⟨(0,1),by rw [window,mem_faceIndices]; omega⟩

def swapSites (N : ℕ) : {p // p∈window N} ≃ {p // p∈window N} where
  toFun p := ⟨p.val.swap,by
    have hp := mem_faceIndices.mp p.property
    exact mem_faceIndices.mpr ⟨hp.2,hp.1⟩⟩
  invFun p := ⟨p.val.swap,by
    have hp := mem_faceIndices.mp p.property
    exact mem_faceIndices.mpr ⟨hp.2,hp.1⟩⟩
  left_inv p := Subtype.ext p.val.swap_swap
  right_inv p := Subtype.ext p.val.swap_swap

theorem dirichlet_swap (N : ℕ) :
    (fourIminusAdjacency (window N)).submatrix (swapSites N) (swapSites N)=
      fourIminusAdjacency (window N) := by
  ext p q
  simp only [Matrix.submatrix_apply,fourIminusAdjacency_apply,(swapSites N).injective.eq_iff]
  have he : natManhattanDist (swapSites N p).val (swapSites N q).val=
      natManhattanDist p.val q.val := by
    simp only [swapSites,Equiv.coe_fn_mk,natManhattanDist,Prod.fst_swap,Prod.snd_swap,add_comm]
  rw [he]

theorem green_swap (N : ℕ) (p q : {p // p∈window N}) :
    (fourIminusAdjacency (window N))⁻¹ (swapSites N p) (swapSites N q)=
      (fourIminusAdjacency (window N))⁻¹ p q := by
  have h := congrArg Inv.inv (dirichlet_swap N)
  rw [Matrix.inv_submatrix_equiv] at h
  exact congrArg (fun M => M p q) h

theorem window_posDef (N : ℕ) : (fourIminusAdjacency (window N)).PosDef := by
  apply dirichlet_posDef (m := N+3) (n := N+3)
  rw [window,foundation_faceIndices]

theorem green_symm (N : ℕ) (p q : {p // p∈window N}) :
    (fourIminusAdjacency (window N))⁻¹ p q=(fourIminusAdjacency (window N))⁻¹ q p := by
  simpa only [star_trivial] using ((window_posDef N).isHermitian.inv.apply q p)

theorem origin_row_entry (N : ℕ) (p : {p // p∈window N}) :
    fourIminusAdjacency (window N) (boundarySite N 0) p=
      (if p=boundarySite N 0 then 4 else 0)-
      (if p=boundarySite N 1 then 1 else 0)-
      (if p=topSite N then 1 else 0) := by
  have h0 : boundarySite N 0=p ↔ p=boundarySite N 0 := eq_comm
  have ha : natManhattanDist (boundarySite N 0).val p.val=1 ↔
      p=boundarySite N 1 ∨ p=topSite N := by
    simp only [boundarySite,topSite,natManhattanDist,Nat.dist,Subtype.ext_iff,Prod.ext_iff]
    omega
  simp only [fourIminusAdjacency_apply,h0,ha]
  by_cases hp1 : p=boundarySite N 1
  · subst p
    norm_num [boundarySite,topSite,Subtype.ext_iff]
  · by_cases hp2 : p=topSite N
    · subst p
      norm_num [boundarySite,topSite,Subtype.ext_iff]
    · simp [hp1,hp2]

theorem origin_green_equation (N : ℕ) (q : {p // p∈window N}) :
    4*(fourIminusAdjacency (window N))⁻¹ (boundarySite N 0) q-
      (fourIminusAdjacency (window N))⁻¹ (boundarySite N 1) q-
      (fourIminusAdjacency (window N))⁻¹ (topSite N) q=
      (if boundarySite N 0=q then 1 else 0) := by
  have h := congrArg (fun M => M (boundarySite N 0) q)
    (Matrix.mul_nonsing_inv (fourIminusAdjacency (window N))
      (isUnit_iff_ne_zero.mpr (window_posDef N).det_pos.ne'))
  simp only [Matrix.mul_apply,Matrix.one_apply] at h
  simp_rw [origin_row_entry,sub_mul] at h
  simp only [Finset.sum_sub_distrib,ite_mul,zero_mul,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,one_mul] at h
  exact h

theorem green_cross (N : ℕ) :
    (fourIminusAdjacency (window N))⁻¹ (topSite N) (boundarySite N 1)=
      4*greenEntry N 0 1-greenEntry N 1 1 := by
  have h := origin_green_equation N (boundarySite N 1)
  have hne : boundarySite N 0≠boundarySite N 1 := by
    intro he
    have hx:=congrArg (fun p : {p // p∈window N} => p.val.1) he
    norm_num [boundarySite] at hx
  rw [if_neg hne] at h
  change 4*greenEntry N 0 1-greenEntry N 1 1-
    (fourIminusAdjacency (window N))⁻¹ (topSite N) (boundarySite N 1)=0 at h
  linarith

def ellPoint : Fin 3 → Ferrers.Point := ![(0,0),(1,0),(0,1)]

theorem ellPoint_mem (i : Fin 3) : ellPoint i∈threeCell := by
  fin_cases i <;> simp [ellPoint,threeCell]

def ellEquiv : Fin 3 ≃ {p // p∈threeCell} :=
  Equiv.ofBijective (fun i => ⟨ellPoint i,ellPoint_mem i⟩) (by
    constructor
    · intro i j h
      have hp := congrArg (fun p : {p // p∈threeCell} => p.val) h
      fin_cases i <;> fin_cases j <;> simp [ellPoint] at hp ⊢
    · intro p
      have hp := p.property
      simp only [threeCell,Finset.mem_insert,Finset.mem_singleton] at hp
      rcases hp with h|h|h
      · exact ⟨0,Subtype.ext h.symm⟩
      · exact ⟨1,Subtype.ext h.symm⟩
      · exact ⟨2,Subtype.ext h.symm⟩)

theorem ellFit (N : ℕ) : threeCell ⊆ faceRectangle (N+3) (N+3) := by
  intro p hp
  simp only [threeCell,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl|rfl|rfl <;> rw [mem_faceRectangle] <;> omega

theorem ellWindowFit (N : ℕ) : threeCell ⊆ window N := by
  rw [window,foundation_faceIndices]
  exact ellFit N

def ellSite (N : ℕ) (i : Fin 3) : {p // p∈window N} :=
  ⟨ellPoint i,ellWindowFit N (ellPoint_mem i)⟩

def ellGreenMatrix (N : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (fourIminusAdjacency (window N))⁻¹ (ellSite N i) (ellSite N j)

theorem ellGreenMatrix_eq (N : ℕ) : ellGreenMatrix N=
    !![greenEntry N 0 0,greenEntry N 0 1,greenEntry N 0 1;
      greenEntry N 0 1,greenEntry N 1 1,4*greenEntry N 0 1-greenEntry N 1 1;
      greenEntry N 0 1,4*greenEntry N 0 1-greenEntry N 1 1,greenEntry N 1 1] := by
  have hs0 : swapSites N (boundarySite N 0)=boundarySite N 0 := rfl
  have hs1 : swapSites N (boundarySite N 1)=topSite N := rfl
  have hb := green_swap N (boundarySite N 0) (boundarySite N 1)
  have hc := green_swap N (boundarySite N 1) (boundarySite N 1)
  rw [hs0,hs1] at hb
  rw [hs1] at hc
  have h10 := green_symm N (boundarySite N 1) (boundarySite N 0)
  have h20 := green_symm N (topSite N) (boundarySite N 0)
  have h12 := green_symm N (boundarySite N 1) (topSite N)
  have hcross := green_cross N
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · exact hb
  · exact h10
  · rfl
  · exact h12.trans hcross
  · exact h20.trans hb
  · exact hcross
  · exact hc

def ellGreenLimit : Matrix (Fin 3) (Fin 3) ℝ :=
  !![greenValue 0 0,greenValue 0 1,greenValue 0 1;
    greenValue 0 1,greenValue 1 1,4*greenValue 0 1-greenValue 1 1;
    greenValue 0 1,4*greenValue 0 1-greenValue 1 1,greenValue 1 1]

theorem ellGreenMatrix_tendsto : Tendsto ellGreenMatrix atTop (𝓝 ellGreenLimit) := by
  have h00:=greenEntry_tendsto (0 : Fin 2) (0 : Fin 2)
  have h01:=greenEntry_tendsto (0 : Fin 2) (1 : Fin 2)
  have h11:=greenEntry_tendsto (1 : Fin 2) (1 : Fin 2)
  have hcross:=(h01.const_mul (4 : ℝ)).sub h11
  have he : ellGreenMatrix=(fun N =>
      !![greenEntry N 0 0,greenEntry N 0 1,greenEntry N 0 1;
        greenEntry N 0 1,greenEntry N 1 1,4*greenEntry N 0 1-greenEntry N 1 1;
        greenEntry N 0 1,4*greenEntry N 0 1-greenEntry N 1 1,greenEntry N 1 1]) :=
    funext ellGreenMatrix_eq
  rw [he]
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h01
  · exact h01
  · exact h11
  · exact hcross
  · exact h01
  · exact hcross
  · exact h11

theorem ellMinor_det (N : ℕ) : Matrix.det (greenMinor (ellFit N))=Matrix.det (ellGreenMatrix N) := by
  rw [UniformStripEnergy.greenMinor_det_transport
    (foundation_faceIndices (N+3) (N+3)).symm rfl (ellFit N) (ellWindowFit N)]
  rw [← Matrix.det_submatrix_equiv_self ellEquiv]
  rfl

theorem ellGreenLimit_det : Matrix.det ellGreenLimit=
    77-(2368/5)/Real.pi+(32768/45)/(Real.pi^2) := by
  have h := greenValue_matrix
  have h00:=congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  have h01:=congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  have h11:=congrFun (congrFun h (1 : Fin 2)) (1 : Fin 2)
  norm_num at h00 h01 h11
  norm_num [ellGreenLimit,Matrix.det_fin_three,h00,h01,h11]
  field_simp
  <;> ring

end
end SpanningTreeIsoperimetry.QuadrantGreenRelations
