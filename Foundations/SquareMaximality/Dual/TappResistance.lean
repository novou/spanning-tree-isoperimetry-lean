module

public import SquareMaximality.Dual.InteriorTapp
public import SquareMaximality.Rectangle.Entropy
public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

set_option backward.privateInPublic true

/-!
# Tapp's bound reduced to one half-plane resistance estimate

Tapp's proof of his Theorem 5.1 (Theorem 9 in the version cited by
`general.tex`) exposes the vertices in words-on-a-page order.  The graph
before a vertex is exposed may be disconnected, so the correct telescoping
quantity is the product of the spanning-tree counts of its connected
components.  Equivalently, it counts maximal acyclic spanning subgraphs.

This module formalizes that finite prefix/product reduction.  The sole
analytic graph-theory input left below is `HalfPlaneResistanceBound`: the
one-step lower bound at a vertex that is the southeast/bottom-right corner
of a complete unit square.  The quantity in that
interface is the exact finite spanning-forest count ratio minus two, i.e. the
finite effective resistance appearing in Tapp's Proposition 5.2.  Its source
proof uses Rayleigh monotonicity and the bulk entropy limit.

The cited manuscript and paper are provenance only, not Lean instructions.
-/

set_option autoImplicit false

namespace SquareMaximality
namespace Dual

open scoped BigOperators

/-- The square-lattice entropy is nonnegative, independently of the Tapp
reduction.  This follows from its proved kernel-integral representation and
pointwise nonnegativity of `arcosh`. -/
theorem squareLatticeEntropy_nonneg : 0 ≤ squareLatticeEntropy := by
  rw [← Rectangle.Entropy.kernelIntegral_eq_squareLatticeEntropy]
  exact intervalIntegral.integral_nonneg (by norm_num)
    (fun x _hx ↦ Rectangle.Kernel.kernel_nonneg x)

/-! ## Maximal spanning forests -/

/-- A spanning forest is a maximal acyclic spanning subgraph.  The equality
of reachability relations says exactly that it contains one spanning tree in
each connected component of `G`. -/
def IsSpanningForest {V : Type*} (G F : SimpleGraph V) : Prop :=
  F ≤ G ∧ F.IsAcyclic ∧ F.Reachable = G.Reachable

/-- Finite type of maximal spanning forests. -/
abbrev SpanningForestType {V : Type*} (G : SimpleGraph V) :=
  {F : SimpleGraph V // IsSpanningForest G F}

/-- Product of the spanning-tree counts of the connected components, defined
without choosing or enumerating those components. -/
noncomputable def spanningForestCount {V : Type*} [Finite V]
    (G : SimpleGraph V) : ℕ :=
  Nat.card (SpanningForestType G)

theorem spanningForestCount_pos {V : Type*} [Finite V]
    (G : SimpleGraph V) : 0 < spanningForestCount G := by
  rcases G.exists_isAcyclic_reachable_eq_le with ⟨F, hFG, hFacyclic, hreach⟩
  letI : Nonempty (SpanningForestType G) :=
    ⟨⟨F, hFG, hFacyclic, hreach⟩⟩
  exact Nat.card_pos

@[simp] theorem spanningForestCount_bot {V : Type*} [Finite V] :
    spanningForestCount (⊥ : SimpleGraph V) = 1 := by
  letI : Unique (SpanningForestType (⊥ : SimpleGraph V)) :=
    { default := ⟨⊥, bot_le, SimpleGraph.isAcyclic_bot, rfl⟩
      uniq := fun F => by
        apply Subtype.ext
        exact le_antisymm F.2.1 bot_le }
  rw [spanningForestCount]
  exact Nat.card_unique

/-- On a connected graph, maximal spanning forests are precisely spanning
trees, so the forest product specializes to `treeCount`. -/
noncomputable def spanningForestEquivTree
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.Connected) :
    SpanningForestType G ≃ {T : SimpleGraph V // T ≤ G ∧ T.IsTree} where
  toFun F := by
    refine ⟨F.1, F.2.1, ?_⟩
    refine ⟨?_, F.2.2.1⟩
    letI : Nonempty V := hG.nonempty
    apply SimpleGraph.Connected.mk
    intro u v
    rw [F.2.2.2]
    exact hG u v
  invFun T := by
    refine ⟨T.1, T.2.1, T.2.2.isAcyclic, ?_⟩
    ext u v
    constructor
    · exact SimpleGraph.Reachable.mono T.2.1
    · intro _huv
      exact T.2.2.connected u v
  left_inv F := rfl
  right_inv T := rfl

theorem spanningForestCount_eq_treeCount
    {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.Connected) :
    spanningForestCount G = treeCount G := by
  rw [spanningForestCount, treeCount,
    Nat.card_congr (spanningForestEquivTree hG)]

/-! ## Monotonicity under adding edges -/

/-- A spanning forest extends to a spanning forest after edges are added. -/
private noncomputable def extendSpanningForest
    {V : Type*} [Finite V] {G G' : SimpleGraph V} (hGG' : G ≤ G') :
    SpanningForestType G → SpanningForestType G' := fun F =>
  let hex := G'.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic
    (F.2.1.trans hGG') F.2.2.1
  let K := Classical.choose hex
  ⟨K, (Classical.choose_spec hex).2.1,
    (Classical.choose_spec hex).2.2.1,
    (Classical.choose_spec hex).2.2.2⟩

private theorem le_extendSpanningForest
    {V : Type*} [Finite V] {G G' : SimpleGraph V} (hGG' : G ≤ G')
    (F : SpanningForestType G) :
    F.1 ≤ (extendSpanningForest hGG' F).1 := by
  exact (Classical.choose_spec
    (G'.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic
      (F.2.1.trans hGG') F.2.2.1)).1

private theorem extendSpanningForest_injective
    {V : Type*} [Finite V] {G G' : SimpleGraph V} (hGG' : G ≤ G') :
    Function.Injective (extendSpanningForest hGG') := by
  intro F K hFK
  have recover (T : SpanningForestType G) :
      (extendSpanningForest hGG' T).1 ⊓ G = T.1 := by
    have hTmax :
        Maximal (fun L : SimpleGraph V => L ≤ G ∧ L.IsAcyclic) T.1 :=
      (SimpleGraph.maximal_isAcyclic_iff_reachable_eq T.2.1 T.2.2.1).mpr
        T.2.2.2
    apply le_antisymm
    · exact hTmax.le_of_ge
        ⟨inf_le_right, (extendSpanningForest hGG' T).2.2.1.anti inf_le_left⟩
        (le_inf (le_extendSpanningForest hGG' T) T.2.1)
    · exact le_inf
        (le_extendSpanningForest hGG' T) T.2.1
  apply Subtype.ext
  rw [← recover F, ← recover K, hFK]

/-- Adding edges cannot decrease the product of component tree counts. -/
theorem spanningForestCount_mono
    {V : Type*} [Finite V] {G G' : SimpleGraph V} (hGG' : G ≤ G') :
    spanningForestCount G ≤ spanningForestCount G' := by
  rw [spanningForestCount, spanningForestCount]
  exact Nat.card_le_card_of_injective
    (extendSpanningForest hGG') (extendSpanningForest_injective hGG')

/-! ## Words-on-a-page prefixes -/

/-- Tapp's words-on-a-page key: higher rows first, then left-to-right. -/
def wordsOnPageKey (z : Boundary.LatticePoint) : Lex (ℤ × ℕ) :=
  toLex (-((z.2 : ℤ)), z.1)

theorem wordsOnPageKey_injective : Function.Injective wordsOnPageKey := by
  intro z w h
  have h' : (-((z.2 : ℤ)), z.1) = (-((w.2 : ℤ)), w.1) :=
    toLex_inj.mp h
  apply Prod.ext
  · exact congrArg Prod.snd h'
  · have hy : -((z.2 : ℤ)) = -((w.2 : ℤ)) := congrArg Prod.fst h'
    exact_mod_cast neg_injective hy

/-- The embedding transports the words-on-a-page order to the abstract
vertex type. -/
noncomputable abbrev wordsOnPageLinearOrder
    {V : Type*} (coord : V ↪ Boundary.LatticePoint) : LinearOrder V :=
  LinearOrder.lift' (fun v => wordsOnPageKey (coord v))
    (wordsOnPageKey_injective.comp coord.injective)

/-- Canonical increasing enumeration in words-on-a-page order. -/
noncomputable def wordsOnPageOrderIso
    {V : Type*} [Fintype V] (coord : V ↪ Boundary.LatticePoint) :
    @OrderIso (Fin (Fintype.card V)) V inferInstance
      (wordsOnPageLinearOrder coord).toLE :=
  @Fintype.orderIsoFinOfCardEq V (wordsOnPageLinearOrder coord) _ _ rfl

/-- The first `k` vertices of the canonical words-on-a-page enumeration. -/
noncomputable def wordsPrefixVertices
    {V : Type*} [Fintype V] (coord : V ↪ Boundary.LatticePoint) (k : ℕ) :
  Finset V :=
  Finset.univ.filter fun v =>
    (wordsOnPageOrderIso coord).toEquiv.symm v < k

/-- Spanning restriction: vertices outside `S` are retained as isolated
vertices.  This lets all prefix forest types share the same ambient type. -/
def spanningRestrict {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm.symm _ _ h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless.irrefl _ h := G.loopless.irrefl _ h.1

theorem spanningRestrict_mono_vertices
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {S T : Finset V} (hST : S ⊆ T) :
    spanningRestrict G S ≤ spanningRestrict G T := by
  intro u v huv
  exact ⟨huv.1, hST huv.2.1, hST huv.2.2⟩

@[simp] theorem spanningRestrict_empty
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) :
    spanningRestrict G ∅ = ⊥ := by
  ext u v
  simp [spanningRestrict]

@[simp] theorem spanningRestrict_univ
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    spanningRestrict G Finset.univ = G := by
  ext u v
  simp [spanningRestrict]

/-- The graph visible after the first `k` vertices have been exposed. -/
noncomputable def wordsPrefixGraph
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint) (k : ℕ) : SimpleGraph V := by
  classical
  exact spanningRestrict G (wordsPrefixVertices coord k)

@[simp] theorem wordsPrefixVertices_zero
    {V : Type*} [Fintype V] (coord : V ↪ Boundary.LatticePoint) :
    wordsPrefixVertices coord 0 = ∅ := by
  classical
  ext v
  simp [wordsPrefixVertices]

@[simp] theorem wordsPrefixVertices_card
    {V : Type*} [Fintype V] (coord : V ↪ Boundary.LatticePoint) :
    wordsPrefixVertices coord (Fintype.card V) = Finset.univ := by
  classical
  ext v
  simp [wordsPrefixVertices]

@[simp] theorem wordsPrefixGraph_zero
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint) :
    wordsPrefixGraph G coord 0 = ⊥ := by
  classical
  simp [wordsPrefixGraph]

@[simp] theorem wordsPrefixGraph_card
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint) :
    wordsPrefixGraph G coord (Fintype.card V) = G := by
  classical
  simp [wordsPrefixGraph]

theorem wordsPrefixVertices_mono
    {V : Type*} [Fintype V] (coord : V ↪ Boundary.LatticePoint)
    {k l : ℕ} (hkl : k ≤ l) :
    wordsPrefixVertices coord k ⊆ wordsPrefixVertices coord l := by
  classical
  intro v hv
  simp only [wordsPrefixVertices, Finset.mem_filter, Finset.mem_univ,
    true_and] at hv ⊢
  exact hv.trans_le hkl

theorem wordsPrefixGraph_mono
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint) {k l : ℕ} (hkl : k ≤ l) :
    wordsPrefixGraph G coord k ≤ wordsPrefixGraph G coord l := by
  classical
  exact spanningRestrict_mono_vertices G
    (wordsPrefixVertices_mono coord hkl)

/-! ## Prefix multipliers and the remaining resistance theorem -/

/-- Product-of-component-tree-count multiplier at the `k`th exposed
vertex. -/
noncomputable def wordsPrefixMultiplier
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint) (k : ℕ) : ℝ :=
  (spanningForestCount (wordsPrefixGraph G coord (k + 1)) : ℝ) /
    spanningForestCount (wordsPrefixGraph G coord k)

/-- The finite resistance term in the series-extension formula
`multiplier = 2 + resistance` at a complete-square step. -/
noncomputable def wordsPrefixResistance
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint) (k : ℕ) : ℝ :=
  wordsPrefixMultiplier G coord k - 2

/-- The one genuinely deep remnant of Tapp's lower-bound proof.

The added vertex is specified by the canonical enumeration.  When it is the
southeast vertex of a displayed complete square, the prefix graph contains
the other three square vertices and the two earlier incident edges.  Tapp's
finite series-extension identity identifies `wordsPrefixResistance` with the
effective resistance between the north and west neighbours.  Rayleigh
monotonicity compares it to finite exhaustions of the words-on-a-page
half-plane, whose limit is `exp κ - 2`.
-/
def HalfPlaneResistanceBound (κ : ℝ) : Prop :=
  ∀ {V : Type} [Fintype V]
    (G : SimpleGraph V) (coord : V ↪ Boundary.LatticePoint)
    (k : ℕ) (hk : k < Fintype.card V) (z : Boundary.LatticePoint),
    G ≤ Boundary.faceLattice.comap coord →
    ContainsUnitSquare G coord z →
    coord ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) =
      (z.1 + 1, z.2) →
    Real.exp κ - 2 ≤ wordsPrefixResistance G coord k

theorem wordsPrefixMultiplier_one_le
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint) (k : ℕ) :
    1 ≤ wordsPrefixMultiplier G coord k := by
  have hmono := spanningForestCount_mono
    (wordsPrefixGraph_mono G coord (Nat.le_succ k))
  have hpos : (0 : ℝ) <
      spanningForestCount (wordsPrefixGraph G coord k) := by
    exact_mod_cast spanningForestCount_pos (wordsPrefixGraph G coord k)
  rw [wordsPrefixMultiplier, one_le_div hpos]
  exact_mod_cast hmono

theorem HalfPlaneResistanceBound.square_multiplier
    { κ : ℝ} (h : HalfPlaneResistanceBound κ)
    {V : Type} [Fintype V]
    (G : SimpleGraph V) (coord : V ↪ Boundary.LatticePoint)
    (k : ℕ) (hk : k < Fintype.card V) (z : Boundary.LatticePoint)
    (hLattice : G ≤ Boundary.faceLattice.comap coord)
    (hsquare : ContainsUnitSquare G coord z)
    (hcoord : coord ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) =
      (z.1 + 1, z.2)) :
    Real.exp κ ≤ wordsPrefixMultiplier G coord k := by
  have hr := h G coord k hk z hLattice hsquare hcoord
  rw [wordsPrefixResistance] at hr
  linarith

/-! ## Telescoping and square injection -/

theorem product_prefixMultipliers
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint) :
    ∏ k ∈ Finset.range (Fintype.card V), wordsPrefixMultiplier G coord k =
      spanningForestCount G := by
  let W : ℕ → ℝ := fun k =>
    spanningForestCount (wordsPrefixGraph G coord k)
  have hWne (k : ℕ) : W k ≠ 0 := by
    have hpos : (0 : ℝ) < W k := by
      exact Nat.cast_pos.mpr
        (spanningForestCount_pos (wordsPrefixGraph G coord k))
    exact ne_of_gt hpos
  have htel :
      (∏ k ∈ Finset.range (Fintype.card V), W (k + 1) / W k) =
        W (Fintype.card V) / W 0 := by
    induction Fintype.card V with
    | zero => simp [hWne]
    | succ n ih =>
        rw [Finset.prod_range_succ, ih]
        field_simp [hWne]
  simpa [wordsPrefixMultiplier, W] using htel

/-- The unique abstract vertex at the southeast/bottom-right corner of a displayed unit
square. -/
noncomputable def unitSquareSEVertex
    {V : Type*} {G : SimpleGraph V}
    {coord : V ↪ Boundary.LatticePoint} {z : Boundary.LatticePoint}
    (h : ContainsUnitSquare G coord z) : V :=
  Classical.choose (ContainsUnitSquare.exists_vertex_of_corner
    (w := (z.1 + 1, z.2)) h ⟨by omega, by omega, by omega, by omega⟩)

theorem unitSquareSEVertex_coord
    {V : Type*} {G : SimpleGraph V}
    {coord : V ↪ Boundary.LatticePoint} {z : Boundary.LatticePoint}
    (h : ContainsUnitSquare G coord z) :
    coord (unitSquareSEVertex h) = (z.1 + 1, z.2) :=
  Classical.choose_spec (ContainsUnitSquare.exists_vertex_of_corner
    (w := (z.1 + 1, z.2)) h ⟨by omega, by omega, by omega, by omega⟩)

/-- Vertices that are southeast/bottom-right corners of complete unit squares in `G`. -/
noncomputable def completeSquareSEVertices
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint) : Finset V :=
  by
    classical
    exact Finset.univ.filter fun v =>
      ∃ z, ContainsUnitSquare G coord z ∧
        coord v = (z.1 + 1, z.2)

theorem displayedSquares_card_le_completeSquareSEVertices
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (coord : V ↪ Boundary.LatticePoint)
    (squares : Finset Boundary.LatticePoint)
    (hsquares : ∀ z ∈ squares, ContainsUnitSquare G coord z) :
    squares.card ≤ (completeSquareSEVertices G coord).card := by
  classical
  let f : ↑squares → ↑(completeSquareSEVertices G coord) := fun z => by
    let v := unitSquareSEVertex (hsquares z.1 z.2)
    refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨z.1, hsquares z.1 z.2, unitSquareSEVertex_coord _⟩
  have hf : Function.Injective f := by
    intro z w hzw
    have hcoord := congrArg (fun v => coord v.1) hzw
    simp only [f] at hcoord
    rw [unitSquareSEVertex_coord, unitSquareSEVertex_coord] at hcoord
    change (z.1.1 + 1, z.1.2) = (w.1.1 + 1, w.1.2) at hcoord
    have hx : z.1.1 = w.1.1 :=
      Nat.add_right_cancel (congrArg (fun p : ℕ × ℕ => p.1) hcoord)
    have hy' := congrArg (@Prod.snd ℕ ℕ) hcoord
    have hy : z.1.2 = w.1.2 := hy'
    exact Subtype.ext (Prod.ext hx hy)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- A complete-square vertex receives the sharp local multiplier bound. -/
theorem completeSquareSEVertex_multiplier
    {κ : ℝ} (h : HalfPlaneResistanceBound κ)
    {V : Type} [Fintype V]
    (G : SimpleGraph V) (coord : V ↪ Boundary.LatticePoint)
    (k : ℕ) (hk : k < Fintype.card V)
    (hLattice : G ≤ Boundary.faceLattice.comap coord)
    (hv : ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) ∈
      completeSquareSEVertices G coord) :
    Real.exp κ ≤ wordsPrefixMultiplier G coord k := by
  classical
  rcases (Finset.mem_filter.mp hv).2 with ⟨z, hsquare, hcoord⟩
  exact h.square_multiplier G coord k hk z hLattice hsquare hcoord

/-- The local half-plane resistance theorem implies Tapp's graph-level
square-family lower bound. -/
theorem tappSquareFamilyLowerBound_of_halfPlaneResistance
    {κ : ℝ} (hres : HalfPlaneResistanceBound κ) :
    TappSquareFamilyLowerBound κ := by
  intro V _ H coord squares hLattice hconn hsquares
  classical
  let n := Fintype.card V
  let e := (wordsOnPageOrderIso coord).toEquiv
  let index : V → ℕ := fun v => (e.symm v).1
  let squareVertex : ↑squares → V := fun z =>
    unitSquareSEVertex (hsquares z.1 z.2)
  let squareIndex : ↑squares → ℕ := fun z => index (squareVertex z)
  let marked : Finset ℕ := squares.attach.image squareIndex
  have hindex_injective : Function.Injective index := by
    intro v w hvw
    apply e.symm.injective
    apply Fin.ext
    exact hvw
  have hsquareVertex_injective : Function.Injective squareVertex := by
    intro z w hzw
    have hcoord := congrArg coord hzw
    simp only [squareVertex] at hcoord
    rw [unitSquareSEVertex_coord, unitSquareSEVertex_coord] at hcoord
    have hx' := congrArg (@Prod.fst ℕ ℕ) hcoord
    have hy' := congrArg (@Prod.snd ℕ ℕ) hcoord
    have hx : z.1.1 = w.1.1 := Nat.add_right_cancel hx'
    have hy : z.1.2 = w.1.2 := hy'
    exact Subtype.ext (Prod.ext hx hy)
  have hsquareIndex_injective : Function.Injective squareIndex :=
    hindex_injective.comp hsquareVertex_injective
  have hmarkedSubset : marked ⊆ Finset.range n := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨z, _hz, rfl⟩
    apply Finset.mem_range.mpr
    exact (e.symm (squareVertex z)).2
  have hfactor (k : ℕ) (hk : k ∈ Finset.range n) :
      (if k ∈ marked then Real.exp κ else 1) ≤
        wordsPrefixMultiplier H coord k := by
    split_ifs with hkm
    · rcases Finset.mem_image.mp hkm with ⟨z, _hz, hzIndex⟩
      apply hres.square_multiplier H coord k (Finset.mem_range.mp hk)
        z.1 hLattice (hsquares z.1 z.2)
      have hindex : index (squareVertex z) = k := by
        exact hzIndex
      have hev : e ⟨k, Finset.mem_range.mp hk⟩ = squareVertex z := by
        have hfin : (⟨k, Finset.mem_range.mp hk⟩ :
            Fin (Fintype.card V)) = e.symm (squareVertex z) := by
          apply Fin.ext
          exact hindex.symm
        exact (congrArg e hfin).trans (e.apply_symm_apply (squareVertex z))
      rw [hev]
      exact unitSquareSEVertex_coord (hsquares z.1 z.2)
    · exact wordsPrefixMultiplier_one_le H coord k
  have hprod := Finset.prod_le_prod₀ (fun k hk => by
      split_ifs <;> positivity)
    (fun k hk => hfactor k hk)
  have hmarkedCard : marked.card = squares.card := by
    change (squares.attach.image squareIndex).card = squares.card
    rw [Finset.card_image_iff.mpr hsquareIndex_injective.injOn]
    simp
  calc
    Real.exp (κ * squares.card) = (Real.exp κ) ^ squares.card := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = (Real.exp κ) ^ marked.card := by rw [hmarkedCard]
    _ = ∏ k ∈ Finset.range n,
        (if k ∈ marked then Real.exp κ else 1) := by
      rw [Finset.prod_ite_mem]
      rw [Finset.inter_eq_right.mpr hmarkedSubset]
      simp
    _ ≤ ∏ k ∈ Finset.range n, wordsPrefixMultiplier H coord k := hprod
    _ = spanningForestCount H := product_prefixMultipliers H coord
    _ = treeCount H := by
      exact_mod_cast spanningForestCount_eq_treeCount hconn

end Dual
end SquareMaximality
