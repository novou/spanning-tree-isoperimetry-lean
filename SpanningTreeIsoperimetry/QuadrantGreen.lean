import SpanningTreeIsoperimetry.QuadrantWalkCount
import SpanningTreeIsoperimetry.MatrixGreenSeries
import SpanningTreeIsoperimetry.HalfPlaneWalks
import SpanningTreeIsoperimetry.CornerLimit
import Mathlib.Analysis.Normed.Group.Tannery

/-! The boundary Green entries of the quadrant, obtained from actual finite
walks and the second reflection, without assuming the method of images. -/
namespace SpanningTreeIsoperimetry.QuadrantGreen

open SquareMaximality SquareMaximality.Boundary SquareMaximality.ClosedWalk
open FaceWalkWords QuadrantWalkCount BoundaryGreen Filter
open scoped Topology Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def window (N : ℕ) : Finset LatticePoint := faceIndices (N+3) (N+3)

def boundarySite (N : ℕ) (i : Fin 2) : {p // p∈window N} :=
  ⟨(i.val,0),by rw [window,mem_faceIndices]; have hi:=i.isLt; omega⟩

def finiteCoefficient (N : ℕ) (a b : Fin 2) (n : ℕ) : ℝ :=
  (Fintype.card {p : (faceGraph (window N)).Walk (boundarySite N a) (boundarySite N b) //
    p.length=n} : ℝ)/(4 : ℝ)^(n+1)

def toQuadrantWord {N n : ℕ} (a b : Fin 2)
    (w : EndpointWord (window N) (boundarySite N a) (boundarySite N b) n) :
    QuadrantBoundaryWord n a.val b.val := ⟨w.val,by
  constructor
  · simpa only [latticePointToPoint,boundarySite,Prod.mk_sub_mk,Nat.cast_zero,sub_self] using w.property.1
  constructor
  · intro t ht
    obtain ⟨q,hq⟩ := w.property.2 t ht
    have hy := congrArg Prod.snd hq
    dsimp [latticePointToPoint,boundarySite] at hy
    omega
  · intro x hx
    obtain ⟨t,ht,hx⟩ := mem_visitedX.mp hx
    obtain ⟨q,hq⟩ := w.property.2 t ht
    have hy := congrArg Prod.fst hq
    dsimp [latticePointToPoint,boundarySite] at hy
    omega⟩

theorem toQuadrantWord_injective {N n : ℕ} (a b : Fin 2) :
    Function.Injective (toQuadrantWord (N := N) (n := n) a b) := by
  intro w v h
  exact Subtype.ext (congrArg (fun q : QuadrantBoundaryWord n a.val b.val => q.val) h)

theorem quadrantWord_staysIn {N n : ℕ} (a b : Fin 2) (hn : n≤N)
    (w : QuadrantBoundaryWord n a.val b.val) : StaysIn (window N) (boundarySite N a) w.val := by
  intro t ht
  have hb := HalfPlaneWalks.position_coordinate_bounds w.val ht
  have hx := w.property.2.2 _ (mem_visitedX.mpr ⟨t,ht,rfl⟩)
  have hy := w.property.2.1 t ht
  let x : ℤ := (a.val : ℤ)+(position w.val t).1
  let y : ℤ := (position w.val t).2
  have ha := a.isLt
  have hx0 : 0≤x := by dsimp [x]; omega
  have hy0 : 0≤y := hy
  have hm : (x.toNat,y.toNat)∈window N := by
    rw [window,mem_faceIndices]
    dsimp [x,y]
    constructor <;> omega
  refine ⟨⟨(x.toNat,y.toNat),hm⟩,?_⟩
  apply Prod.ext <;> simp [latticePointToPoint,boundarySite,x,y,hx0,hy0]

def quadrantEndpointEquiv {N n : ℕ} (a b : Fin 2) (hn : n≤N) :
    EndpointWord (window N) (boundarySite N a) (boundarySite N b) n ≃
      QuadrantBoundaryWord n a.val b.val where
  toFun := toQuadrantWord a b
  invFun w := ⟨w.val,by
    constructor
    · simpa only [latticePointToPoint,boundarySite,Prod.mk_sub_mk,Nat.cast_zero,sub_self] using w.property.1
    · exact quadrantWord_staysIn a b hn w⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finiteCoefficient_nonneg (N : ℕ) (a b : Fin 2) (n : ℕ) :
    0≤finiteCoefficient N a b n := by unfold finiteCoefficient; positivity

theorem finiteCoefficient_le (N : ℕ) (a b : Fin 2) (n : ℕ) :
    finiteCoefficient N a b n≤quadrantCoefficient n a.val b.val := by
  have hw := Fintype.card_congr (endpointWordEquiv (window N) (boundarySite N a) (boundarySite N b) n)
  have hc := Fintype.card_le_of_injective _ (toQuadrantWord_injective (N := N) (n := n) a b)
  unfold finiteCoefficient quadrantCoefficient
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast hw.trans_le hc

theorem finiteCoefficient_eq {N n : ℕ} (a b : Fin 2) (hn : n≤N) :
    finiteCoefficient N a b n=quadrantCoefficient n a.val b.val := by
  have he := (endpointWordEquiv (window N) (boundarySite N a) (boundarySite N b) n).trans
    (quadrantEndpointEquiv a b hn)
  unfold finiteCoefficient quadrantCoefficient
  rw [Fintype.card_congr he]

def greenEntry (N : ℕ) (a b : Fin 2) : ℝ :=
  (fourIminusAdjacency (window N))⁻¹ (boundarySite N a) (boundarySite N b)

def greenValue (a b : Fin 2) : ℝ :=
  boundaryValue ⟨Nat.dist a.val b.val,by have ha:=a.isLt; have hb:=b.isLt; unfold Nat.dist; omega⟩-
    boundaryValue ⟨a.val+b.val+2,by have ha:=a.isLt; have hb:=b.isLt; omega⟩

theorem greenEntry_hasSum (N : ℕ) (a b : Fin 2) :
    HasSum (finiteCoefficient N a b) (greenEntry N a b) :=
  MatrixGreenSeries.face_inverse_walk_hasSum (Finset.Subset.refl (window N))
    (boundarySite N a) (boundarySite N b)

theorem greenEntry_tendsto (a b : Fin 2) :
    Tendsto (fun N => greenEntry N a b) atTop (𝓝 (greenValue a b)) := by
  have hs := quadrantCoefficient_hasSum (a := a.val) (b := b.val)
    (by have ha:=a.isLt; have hb:=b.isLt; omega)
  have ht := tendsto_tsum_of_dominated_convergence hs.summable
    (f := fun N n => finiteCoefficient N a b n)
    (g := fun n => quadrantCoefficient n a.val b.val)
    (fun n => (tendsto_const_nhds : Tendsto (fun _ : ℕ => quadrantCoefficient n a.val b.val)
      atTop (𝓝 (quadrantCoefficient n a.val b.val))).congr'
      ((eventually_ge_atTop n).mono (fun N hN => (finiteCoefficient_eq a b hN).symm)))
    (Eventually.of_forall (fun N n => by
      rw [Real.norm_eq_abs,abs_of_nonneg (finiteCoefficient_nonneg N a b n)]
      exact finiteCoefficient_le N a b n))
  have hf : (fun N => ∑' n,finiteCoefficient N a b n)=(fun N => greenEntry N a b) := by
    funext N
    exact (greenEntry_hasSum N a b).tsum_eq
  rw [hf,hs.tsum_eq] at ht
  exact ht

theorem greenValue_matrix : (fun a b => greenValue a b)=
    (!![2-(16/3)/Real.pi,7/2-(32/3)/Real.pi;
      7/2-(32/3)/Real.pi,18-(832/15)/Real.pi] : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [greenValue,boundaryValue,limitSix,initialSix,Nat.dist] <;> ring

end
end SpanningTreeIsoperimetry.QuadrantGreen
