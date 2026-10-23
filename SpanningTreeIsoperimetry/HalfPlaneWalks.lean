module

public import SpanningTreeIsoperimetry.FaceWalkWords
public import SpanningTreeIsoperimetry.HalfPlaneWords
public import SquareMaximality.ClosedWalk.Symmetry

@[expose] public section

/-! Exact finite-window walks and half-plane words. Every fixed-length path
fits in the chosen window once its radius is at least that length. -/
namespace SpanningTreeIsoperimetry.HalfPlaneWalks

open SquareMaximality SquareMaximality.Boundary SquareMaximality.ClosedWalk
open FaceWalkWords BoundaryGreen
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Face windows centered around six consecutive boundary sites. -/
def window (N : ℕ) : Finset LatticePoint := faceIndices (2 * N + 6) (N + 1)

def boundarySite (N : ℕ) (i : Fin 6) : {p // p ∈ window N} :=
  ⟨(N + i.val, 0), by rw [window, mem_faceIndices]; have hi := i.isLt; omega⟩

/-- The actual normalized count of finite graph walks between boundary sites. -/
noncomputable def finiteBoundaryCoefficient (N : ℕ) (i j : Fin 6) (n : ℕ) : ℝ :=
  (Fintype.card {p : (faceGraph (window N)).Walk (boundarySite N i) (boundarySite N j) // p.length = n} : ℝ) /
    (4 : ℝ) ^ (n + 1)

theorem finiteBoundaryCoefficient_nonneg (N : ℕ) (i j : Fin 6) (n : ℕ) :
    0 ≤ finiteBoundaryCoefficient N i j n := by
  unfold finiteBoundaryCoefficient
  positivity

theorem swapWord_position {n : ℕ} (w : Word n) (t : ℕ) :
    position (swapWord w) t = (position w t).swap := position_swapWord w t

theorem swapWord_total {n : ℕ} (w : Word n) :
    total (swapWord w) = (total w).swap := total_swapWord w

/-- Unit steps give a deterministic radius bound at every visited time. -/
theorem position_coordinate_bounds {n t : ℕ} (w : Word n) (ht : t ≤ n) :
    -(t : ℤ) ≤ (position w t).1 ∧ (position w t).1 ≤ t ∧
      -(t : ℤ) ≤ (position w t).2 ∧ (position w t).2 ≤ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hb := ih (by omega)
    rw [position_succ w (by omega)]
    cases h : w ⟨t, by omega⟩ <;>
      simp only [h, Step.vector_east, Step.vector_west, Step.vector_north, Step.vector_south,
        Prod.fst_add, Prod.snd_add, Nat.cast_add, Nat.cast_one] <;> omega

/-- Swapping a bottom-boundary walk makes a nonnegative first-coordinate word. -/
noncomputable def endpointToHalfPlaneWord {N n : ℕ} {i j : Fin 6} (hij : i.val ≤ j.val)
    (w : EndpointWord (window N) (boundarySite N i) (boundarySite N j) n) :
    HalfPlaneWord n (j.val - i.val) :=
  ⟨swapWord w.val, by
    constructor
    · rw [swapWord_total, w.property.1]
      apply Prod.ext <;> dsimp [latticePointToPoint, boundarySite] <;> omega
    · intro x hx
      obtain ⟨t, ht, hpos⟩ := mem_visitedX.mp hx
      rw [swapWord_position] at hpos
      obtain ⟨q, hq⟩ := w.property.2 t ht
      have hy := congrArg Prod.snd hq
      dsimp [latticePointToPoint, boundarySite] at hy
      change (position w.val t).2 = x at hpos
      omega⟩

theorem endpointToHalfPlaneWord_injective {N n : ℕ} {i j : Fin 6} (hij : i.val ≤ j.val) :
    Function.Injective (endpointToHalfPlaneWord (N := N) (n := n) hij) := by
  intro w v h
  apply Subtype.ext
  have hh := congrArg (fun w : HalfPlaneWord n (j.val - i.val) => swapWord w.val) h
  simpa only [endpointToHalfPlaneWord, swapWord_swapWord] using hh

/-- Once `n≤N`, every admissible word stays inside the actual face window. -/
theorem halfPlaneWord_staysIn {N n : ℕ} (i : Fin 6) (hn : n ≤ N)
    {j : ℕ} (w : HalfPlaneWord n j) : StaysIn (window N) (boundarySite N i) (swapWord w.val) := by
  intro t ht
  have hb := position_coordinate_bounds w.val ht
  have hy : 0 ≤ (position w.val t).1 := w.property.2 _ (mem_visitedX.mpr ⟨t, ht, rfl⟩)
  let x : ℤ := (N : ℤ) + i.val + (position w.val t).2
  let y : ℤ := (position w.val t).1
  have hi := i.isLt
  have hx0 : 0 ≤ x := by dsimp [x]; omega
  have hx1 : x < 2 * N + 6 := by dsimp [x]; omega
  have hy0 : 0 ≤ y := hy
  have hy1 : y < N + 1 := by dsimp [y]; omega
  have hmem : (x.toNat, y.toNat) ∈ window N := by
    rw [window, mem_faceIndices]
    constructor <;> dsimp only <;> omega
  refine ⟨⟨(x.toNat, y.toNat), hmem⟩, ?_⟩
  rw [swapWord_position]
  apply Prod.ext <;> simp [latticePointToPoint, boundarySite, x, y, hx0, hy0]

noncomputable def halfPlaneToEndpointWord {N n : ℕ} {i j : Fin 6}
    (hij : i.val ≤ j.val) (hn : n ≤ N) (w : HalfPlaneWord n (j.val - i.val)) :
    EndpointWord (window N) (boundarySite N i) (boundarySite N j) n :=
  ⟨swapWord w.val, by
    constructor
    · rw [swapWord_total, w.property.1]
      apply Prod.ext <;> dsimp [latticePointToPoint, boundarySite] <;> omega
    · exact halfPlaneWord_staysIn i hn w⟩

/-- Exact finite equivalence at every length up to the window radius. -/
noncomputable def halfPlaneEndpointEquiv {N n : ℕ} {i j : Fin 6}
    (hij : i.val ≤ j.val) (hn : n ≤ N) :
    EndpointWord (window N) (boundarySite N i) (boundarySite N j) n ≃
      HalfPlaneWord n (j.val - i.val) where
  toFun := endpointToHalfPlaneWord hij
  invFun := halfPlaneToEndpointWord hij hn
  left_inv w := Subtype.ext (swapWord_swapWord w.val)
  right_inv w := Subtype.ext (swapWord_swapWord w.val)

theorem finiteBoundaryCoefficient_le_ordered {N n : ℕ} {i j : Fin 6} (hij : i.val ≤ j.val) :
    finiteBoundaryCoefficient N i j n ≤ halfPlaneCoefficient n (j.val - i.val) := by
  have hc := Fintype.card_le_of_injective _ (endpointToHalfPlaneWord_injective (N := N) (n := n) hij)
  have hw := Fintype.card_congr (endpointWordEquiv (window N) (boundarySite N i) (boundarySite N j) n)
  unfold finiteBoundaryCoefficient halfPlaneCoefficient
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast hw.trans_le hc

theorem finiteBoundaryCoefficient_eq_ordered {N n : ℕ} {i j : Fin 6}
    (hij : i.val ≤ j.val) (hn : n ≤ N) :
    finiteBoundaryCoefficient N i j n = halfPlaneCoefficient n (j.val - i.val) := by
  have he := (endpointWordEquiv (window N) (boundarySite N i) (boundarySite N j) n).trans
    (halfPlaneEndpointEquiv hij hn)
  unfold finiteBoundaryCoefficient halfPlaneCoefficient
  rw [Fintype.card_congr he]

noncomputable def boundaryWalkReverseEquiv (N n : ℕ) (i j : Fin 6) :
    {p : (faceGraph (window N)).Walk (boundarySite N i) (boundarySite N j) // p.length = n} ≃
      {p : (faceGraph (window N)).Walk (boundarySite N j) (boundarySite N i) // p.length = n} where
  toFun p := ⟨p.val.reverse, by simpa using p.property⟩
  invFun p := ⟨p.val.reverse, by simpa using p.property⟩
  left_inv p := Subtype.ext p.val.reverse_reverse
  right_inv p := Subtype.ext p.val.reverse_reverse

theorem finiteBoundaryCoefficient_symm (N : ℕ) (i j : Fin 6) (n : ℕ) :
    finiteBoundaryCoefficient N i j n = finiteBoundaryCoefficient N j i n := by
  unfold finiteBoundaryCoefficient
  rw [Fintype.card_congr (boundaryWalkReverseEquiv N n i j)]

/-- Uniform domination by actual half-plane word counts, for either endpoint order. -/
theorem finiteBoundaryCoefficient_le_halfPlane (N : ℕ) (i j : Fin 6) (n : ℕ) :
    finiteBoundaryCoefficient N i j n ≤ halfPlaneCoefficient n (Nat.dist i.val j.val) := by
  by_cases hij : i.val ≤ j.val
  · rw [Nat.dist_eq_sub_of_le hij]
    exact finiteBoundaryCoefficient_le_ordered hij
  · rw [finiteBoundaryCoefficient_symm N i j n, Nat.dist_comm, Nat.dist_eq_sub_of_le (by omega : j.val ≤ i.val)]
    exact finiteBoundaryCoefficient_le_ordered (by omega)

/-- Stabilization of each coefficient is exact at radius at least the walk length. -/
theorem finiteBoundaryCoefficient_eq_halfPlane_of_le {N n : ℕ} (i j : Fin 6) (hn : n ≤ N) :
    finiteBoundaryCoefficient N i j n = halfPlaneCoefficient n (Nat.dist i.val j.val) := by
  by_cases hij : i.val ≤ j.val
  · rw [Nat.dist_eq_sub_of_le hij]
    exact finiteBoundaryCoefficient_eq_ordered hij hn
  · rw [finiteBoundaryCoefficient_symm N i j n, Nat.dist_comm, Nat.dist_eq_sub_of_le (by omega : j.val ≤ i.val)]
    exact finiteBoundaryCoefficient_eq_ordered (by omega) hn

end SpanningTreeIsoperimetry.HalfPlaneWalks
