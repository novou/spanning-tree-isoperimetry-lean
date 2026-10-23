module

public import SpanningTreeIsoperimetry.QuadrantWalkCount
public import SpanningTreeIsoperimetry.BoundaryGreenExtension
public import SpanningTreeIsoperimetry.MatrixGreenSeries
public import SpanningTreeIsoperimetry.HalfPlaneWalks
public import SpanningTreeIsoperimetry.CornerLimit
public import Mathlib.Analysis.Normed.Group.Tannery

@[expose] public section

/-! The boundary Green entries of the quadrant, obtained from actual finite
walks and the second reflection, without assuming the method of images. -/
namespace SpanningTreeIsoperimetry.QuadrantBoundaryGreen

open SquareMaximality SquareMaximality.Boundary SquareMaximality.ClosedWalk
open FaceWalkWords QuadrantWalkCount BoundaryGreen BoundaryGreenExtension Filter
open scoped Topology Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def window (K N : ℕ) : Finset LatticePoint := faceIndices (N+K+1) (N+K+1)

variable {K : ℕ}

def boundarySite (N : ℕ) (i : Fin K) : {p // p∈window K N} :=
  ⟨(i.val,0),by rw [window,mem_faceIndices]; have hi:=i.isLt; omega⟩

def finiteCoefficient (N : ℕ) (a b : Fin K) (n : ℕ) : ℝ :=
  (Fintype.card {p : (faceGraph (window K N)).Walk (boundarySite N a) (boundarySite N b) //
    p.length=n} : ℝ)/(4 : ℝ)^(n+1)

def toQuadrantWord {N n : ℕ} (a b : Fin K)
    (w : EndpointWord (window K N) (boundarySite N a) (boundarySite N b) n) :
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

theorem toQuadrantWord_injective {N n : ℕ} (a b : Fin K) :
    Function.Injective (toQuadrantWord (N := N) (n := n) a b) := by
  intro w v h
  exact Subtype.ext (congrArg (fun q : QuadrantBoundaryWord n a.val b.val => q.val) h)

theorem quadrantWord_staysIn {N n : ℕ} (a b : Fin K) (hn : n≤N)
    (w : QuadrantBoundaryWord n a.val b.val) : StaysIn (window K N) (boundarySite N a) w.val := by
  intro t ht
  have hb := HalfPlaneWalks.position_coordinate_bounds w.val ht
  have hx := w.property.2.2 _ (mem_visitedX.mpr ⟨t,ht,rfl⟩)
  have hy := w.property.2.1 t ht
  let x : ℤ := (a.val : ℤ)+(position w.val t).1
  let y : ℤ := (position w.val t).2
  have ha := a.isLt
  have hx0 : 0≤x := by dsimp [x]; omega
  have hy0 : 0≤y := hy
  have hm : (x.toNat,y.toNat)∈window K N := by
    rw [window,mem_faceIndices]
    dsimp [x,y]
    constructor <;> omega
  refine ⟨⟨(x.toNat,y.toNat),hm⟩,?_⟩
  apply Prod.ext <;> simp [latticePointToPoint,boundarySite,x,y,hx0,hy0]

def quadrantEndpointEquiv {N n : ℕ} (a b : Fin K) (hn : n≤N) :
    EndpointWord (window K N) (boundarySite N a) (boundarySite N b) n ≃
      QuadrantBoundaryWord n a.val b.val where
  toFun := toQuadrantWord a b
  invFun w := ⟨w.val,by
    constructor
    · simpa only [latticePointToPoint,boundarySite,Prod.mk_sub_mk,Nat.cast_zero,sub_self] using w.property.1
    · exact quadrantWord_staysIn a b hn w⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem finiteCoefficient_nonneg (N : ℕ) (a b : Fin K) (n : ℕ) :
    0≤finiteCoefficient N a b n := by unfold finiteCoefficient; positivity

theorem finiteCoefficient_le (N : ℕ) (a b : Fin K) (n : ℕ) :
    finiteCoefficient N a b n≤quadrantCoefficient n a.val b.val := by
  have hw := Fintype.card_congr (endpointWordEquiv (window K N) (boundarySite N a) (boundarySite N b) n)
  have hc := Fintype.card_le_of_injective _ (toQuadrantWord_injective (N := N) (n := n) a b)
  unfold finiteCoefficient quadrantCoefficient
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast hw.trans_le hc

theorem finiteCoefficient_eq {N n : ℕ} (a b : Fin K) (hn : n≤N) :
    finiteCoefficient N a b n=quadrantCoefficient n a.val b.val := by
  have he := (endpointWordEquiv (window K N) (boundarySite N a) (boundarySite N b) n).trans
    (quadrantEndpointEquiv a b hn)
  unfold finiteCoefficient quadrantCoefficient
  rw [Fintype.card_congr he]

def greenEntry (N : ℕ) (a b : Fin K) : ℝ :=
  (fourIminusAdjacency (window K N))⁻¹ (boundarySite N a) (boundarySite N b)

def greenValue (hK : K≤4) (a b : Fin K) : ℝ :=
  boundaryValueNine ⟨Nat.dist a.val b.val,by have ha:=a.isLt; have hb:=b.isLt; unfold Nat.dist; omega⟩-
    boundaryValueNine ⟨a.val+b.val+2,by have ha:=a.isLt; have hb:=b.isLt; omega⟩

theorem quadrantCoefficient_nine_hasSum (hK : K≤4) (a b : Fin K) :
    HasSum (fun n => quadrantCoefficient n a.val b.val) (greenValue hK a b) := by
  have hdist : Nat.dist a.val b.val<9 := by have ha:=a.isLt; have hb:=b.isLt; unfold Nat.dist; omega
  have hsum : a.val+b.val+2<9 := by have ha:=a.isLt; have hb:=b.isLt; omega
  exact ((halfPlaneCoefficient_nine_hasSum ⟨Nat.dist a.val b.val,hdist⟩).sub
    (halfPlaneCoefficient_nine_hasSum ⟨a.val+b.val+2,hsum⟩)).congr_fun
      (fun n => quadrantCoefficient_eq n a.val b.val)

theorem greenEntry_hasSum (N : ℕ) (a b : Fin K) :
    HasSum (finiteCoefficient N a b) (greenEntry N a b) :=
  MatrixGreenSeries.face_inverse_walk_hasSum (Finset.Subset.refl (window K N))
    (boundarySite N a) (boundarySite N b)

theorem greenEntry_tendsto (hK : K≤4) (a b : Fin K) :
    Tendsto (fun N => greenEntry N a b) atTop (𝓝 (greenValue hK a b)) := by
  have hs := quadrantCoefficient_nine_hasSum hK a b
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

end
end SpanningTreeIsoperimetry.QuadrantBoundaryGreen
