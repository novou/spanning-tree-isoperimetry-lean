import SquareMaximality.Graph
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace SquareMaximality

open SimpleGraph

/-- Coordinate form of unit Manhattan distance. -/
theorem manhattanDist_eq_one_iff (p q : Point) :
    manhattanDist p q = 1 ↔
      (((p.1 + 1 = q.1) ∨ (q.1 + 1 = p.1)) ∧ p.2 = q.2) ∨
      (((p.2 + 1 = q.2) ∨ (q.2 + 1 = p.2)) ∧ p.1 = q.1) := by
  rw [manhattanDist, Nat.add_eq_one_iff]
  simp only [Int.natAbs_eq_iff]
  omega

section TreeCount

universe u v

variable {V : Type u} {W : Type v}
variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- Transporting a spanning subgraph along a graph isomorphism preserves the
condition of lying below the ambient graph. -/
private theorem transport_le_iff (f : G ≃g H) (T : SimpleGraph V) :
    f.toEquiv.simpleGraph T ≤ H ↔ T ≤ G := by
  constructor
  · intro h u v huv
    apply f.map_adj_iff.mp
    apply h
    change T.Adj (f.symm (f u)) (f.symm (f v))
    simpa
  · intro h u v huv
    change T.Adj (f.symm u) (f.symm v) at huv
    have hG := h huv
    have hH := f.map_adj_iff.mpr hG
    simpa using hH

/-- Transporting a graph along an equivalence preserves the tree predicate. -/
private theorem transport_isTree_iff (e : V ≃ W) (T : SimpleGraph V) :
    (e.simpleGraph T).IsTree ↔ T.IsTree :=
  (SimpleGraph.Iso.comap e.symm T).isTree_iff

/-- Spanning-tree counts are invariant under graph isomorphism. -/
theorem treeCount_congr [Finite V] [Finite W] (f : G ≃g H) :
    treeCount G = treeCount H := by
  unfold treeCount
  apply Nat.card_congr
  apply f.toEquiv.simpleGraph.subtypeEquiv
  intro T
  constructor
  · rintro ⟨hTG, hT⟩
    exact ⟨(transport_le_iff f T).mpr hTG,
      (transport_isTree_iff f.toEquiv T).mpr hT⟩
  · rintro ⟨hTH, hT⟩
    exact ⟨(transport_le_iff f T).mp hTH,
      (transport_isTree_iff f.toEquiv T).mp hT⟩

end TreeCount

section Translation

/-- Translation by `(a,b)` as an equivalence of the integer lattice. -/
def pointTranslation (a b : ℤ) : Point ≃ Point where
  toFun p := (p.1 + a, p.2 + b)
  invFun p := (p.1 - a, p.2 - b)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

@[simp]
theorem pointTranslation_apply (a b : ℤ) (p : Point) :
    pointTranslation a b p = (p.1 + a, p.2 + b) :=
  rfl

@[simp]
theorem manhattanDist_pointTranslation (a b : ℤ) (p q : Point) :
    manhattanDist (pointTranslation a b p) (pointTranslation a b q) =
      manhattanDist p q := by
  simp only [manhattanDist, pointTranslation_apply]
  congr 1
  · congr 1
    ring
  · congr 1
    ring

/-- Translate every point of a finite lattice set by `(a,b)`. -/
def translateFinset (a b : ℤ) (S : Finset Point) : Finset Point :=
  S.map (pointTranslation a b).toEmbedding

@[simp]
theorem mem_translateFinset (a b : ℤ) (S : Finset Point) (p : Point) :
    pointTranslation a b p ∈ translateFinset a b S ↔ p ∈ S := by
  rw [translateFinset, Finset.mem_map]
  constructor
  · rintro ⟨q, hq, hqp⟩
    have : q = p := (pointTranslation a b).injective hqp
    simpa [this] using hq
  · intro hp
    exact ⟨p, hp, rfl⟩

/-- Translation restricts to an equivalence between a finite set and its
translate. -/
def translateFinsetEquiv (a b : ℤ) (S : Finset Point) :
    {p : Point // p ∈ S} ≃ {p : Point // p ∈ translateFinset a b S} :=
  (pointTranslation a b).subtypeEquiv fun p => by
    simp only [mem_translateFinset]

@[simp]
theorem translateFinsetEquiv_apply (a b : ℤ) (S : Finset Point)
    (p : {p : Point // p ∈ S}) :
    (translateFinsetEquiv a b S p : Point) = pointTranslation a b p :=
  rfl

/-- Translation is a graph isomorphism between the grids induced by an
arbitrary finite lattice set and by its translate. -/
def inducedGridTranslationIso (a b : ℤ) (S : Finset Point) :
    inducedGrid S ≃g inducedGrid (translateFinset a b S) where
  __ := translateFinsetEquiv a b S
  map_rel_iff' := by
    intro p q
    simp only [inducedGrid_adj_iff, translateFinsetEquiv_apply,
      manhattanDist_pointTranslation]

/-- Translating an arbitrary finite lattice set preserves its spanning-tree
count. -/
@[simp]
theorem tau_translateFinset (a b : ℤ) (S : Finset Point) :
    tau (translateFinset a b S) = tau S :=
  (treeCount_congr (inducedGridTranslationIso a b S)).symm

/-- Translation identifies the standard rectangle with its translate. -/
def rectangleTranslationEquiv (a b : ℤ) (r s : ℕ) :
    {p : Point // p ∈ rectangle 0 0 r s} ≃
      {p : Point // p ∈ rectangle a b r s} :=
  (pointTranslation a b).subtypeEquiv fun p => by
    simp [rectangle, pointTranslation]
    omega

@[simp]
theorem rectangleTranslationEquiv_apply (a b : ℤ) (r s : ℕ)
    (p : {p : Point // p ∈ rectangle 0 0 r s}) :
    (rectangleTranslationEquiv a b r s p : Point) = pointTranslation a b p :=
  rfl

/-- Translation is an isomorphism between the corresponding induced grids. -/
def rectangleTranslationIso (a b : ℤ) (r s : ℕ) :
    inducedGrid (rectangle 0 0 r s) ≃g inducedGrid (rectangle a b r s) where
  __ := rectangleTranslationEquiv a b r s
  map_rel_iff' := by
    intro p q
    simp only [inducedGrid_adj_iff, rectangleTranslationEquiv_apply,
      manhattanDist_pointTranslation]

/-- The spanning-tree count of a rectangle is independent of its base point. -/
theorem tau_rectangle_eq_tauRect (a b : ℤ) (r s : ℕ) :
    tau (rectangle a b r s) = tauRect r s := by
  rw [tauRect_eq]
  exact (treeCount_congr (rectangleTranslationIso a b r s)).symm

end Translation

section CoordinateSwap

/-- Interchange the two coordinates of an integer lattice point. -/
def pointSwap : Point ≃ Point where
  toFun p := (p.2, p.1)
  invFun p := (p.2, p.1)
  left_inv p := by ext <;> rfl
  right_inv p := by ext <;> rfl

@[simp]
theorem pointSwap_apply (p : Point) : pointSwap p = (p.2, p.1) :=
  rfl

@[simp]
theorem manhattanDist_pointSwap (p q : Point) :
    manhattanDist (pointSwap p) (pointSwap q) = manhattanDist p q := by
  simp only [manhattanDist, pointSwap_apply]
  rw [Nat.add_comm]

/-- Swapping coordinates identifies the standard `r × s` rectangle with
the standard `s × r` rectangle. -/
def rectangleSwapEquiv (r s : ℕ) :
    {p : Point // p ∈ rectangle 0 0 r s} ≃
      {p : Point // p ∈ rectangle 0 0 s r} :=
  pointSwap.subtypeEquiv fun p => by
    simp [rectangle, pointSwap, and_comm, and_left_comm]

@[simp]
theorem rectangleSwapEquiv_apply (r s : ℕ)
    (p : {p : Point // p ∈ rectangle 0 0 r s}) :
    (rectangleSwapEquiv r s p : Point) = pointSwap p :=
  rfl

/-- Coordinate swap is an isomorphism between the two orientations of a
rectangular grid. -/
def rectangleSwapIso (r s : ℕ) :
    inducedGrid (rectangle 0 0 r s) ≃g inducedGrid (rectangle 0 0 s r) where
  __ := rectangleSwapEquiv r s
  map_rel_iff' := by
    intro p q
    simp only [inducedGrid_adj_iff, rectangleSwapEquiv_apply,
      manhattanDist_pointSwap]

/-- Rectangular spanning-tree counts are symmetric in the two side lengths. -/
theorem tauRect_comm (r s : ℕ) : tauRect r s = tauRect s r := by
  unfold tauRect tau
  exact treeCount_congr (rectangleSwapIso r s)

end CoordinateSwap

section RectangleConnectivity

/-- The vertices of the standard `r × s` rectangle are naturally indexed by
`Fin r × Fin s`. -/
def standardRectangleEquivFin (r s : ℕ) :
    {p : Point // p ∈ rectangle 0 0 r s} ≃ Fin r × Fin s where
  toFun p :=
    (⟨p.1.1.toNat, by
        have hp := p.2
        simp [rectangle] at hp
        omega⟩,
      ⟨p.1.2.toNat, by
        have hp := p.2
        simp [rectangle] at hp
        omega⟩)
  invFun p :=
    ⟨((p.1.1 : ℤ), (p.2.1 : ℤ)), by
      simp [rectangle]⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change ((p.1.1.toNat : ℕ) : ℤ) = p.1.1
      have hp := p.2
      simp [rectangle] at hp
      omega
    · change ((p.1.2.toNat : ℕ) : ℤ) = p.1.2
      have hp := p.2
      simp [rectangle] at hp
      omega
  right_inv p := by
    apply Prod.ext <;> apply Fin.ext <;> simp

@[simp]
theorem standardRectangleEquivFin_apply_val (r s : ℕ)
    (p : {p : Point // p ∈ rectangle 0 0 r s}) :
    (standardRectangleEquivFin r s p).1.1 = p.1.1.toNat ∧
      (standardRectangleEquivFin r s p).2.1 = p.1.2.toNat :=
  ⟨rfl, rfl⟩

@[simp]
theorem standardRectangleEquivFin_apply_fst (r s : ℕ)
    (p : {p : Point // p ∈ rectangle 0 0 r s}) :
    (standardRectangleEquivFin r s p).1.1 = p.1.1.toNat :=
  rfl

@[simp]
theorem standardRectangleEquivFin_apply_snd (r s : ℕ)
    (p : {p : Point // p ∈ rectangle 0 0 r s}) :
    (standardRectangleEquivFin r s p).2.1 = p.1.2.toNat :=
  rfl

/-- The standard rectangular grid is the box product of two finite path
graphs. -/
def standardRectangleGridIso (r s : ℕ) :
    inducedGrid (rectangle 0 0 r s) ≃g pathGraph r □ pathGraph s where
  __ := standardRectangleEquivFin r s
  map_rel_iff' := by
    intro p q
    have hp := p.2
    have hq := q.2
    simp [rectangle] at hp hq
    simp only [boxProd_adj, pathGraph_adj, inducedGrid_adj_iff,
      manhattanDist_eq_one_iff, standardRectangleEquivFin_apply_fst,
      standardRectangleEquivFin_apply_snd, Fin.ext_iff]
    omega

/-- A standard rectangle with positive side lengths has a connected induced
grid. -/
theorem standardRectangle_connected {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    (inducedGrid (rectangle 0 0 r s)).Connected := by
  have hrPath : (pathGraph r).Connected := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
    simpa [Nat.succ_eq_add_one] using pathGraph_connected k
  have hsPath : (pathGraph s).Connected := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
    simpa [Nat.succ_eq_add_one] using pathGraph_connected k
  exact (standardRectangleGridIso r s).connected_iff.mpr
    (hrPath.boxProd hsPath)

/-- Every positive-size translated rectangle has a connected induced grid. -/
theorem rectangle_connected (a b : ℤ) {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    (inducedGrid (rectangle a b r s)).Connected :=
  (rectangleTranslationIso a b r s).connected_iff.mp
    (standardRectangle_connected hr hs)

/-- A positive-size rectangular grid has at least one spanning tree. -/
theorem tauRect_pos {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    0 < tauRect r s := by
  rw [tauRect_eq]
  exact (tau_pos_iff_connected _).mpr (standardRectangle_connected hr hs)

/-- The translated formulation of positivity for rectangular tree counts. -/
theorem tau_rectangle_pos (a b : ℤ) {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    0 < tau (rectangle a b r s) :=
  (tau_pos_iff_connected _).mpr (rectangle_connected a b hr hs)

end RectangleConnectivity

end SquareMaximality
