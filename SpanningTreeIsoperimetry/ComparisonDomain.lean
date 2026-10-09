import SpanningTreeIsoperimetry.FoundationsBridge
import SquareMaximality.Dual.TappRayleigh
import SquareMaximality.Inputs.MatrixTreeTheorem
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-! Explicit comparison domains obtained by adjoining partial boundary rows.
The forest-prefix bridge keeps isolated unused vertices from changing the
combinatorial count. -/
namespace SpanningTreeIsoperimetry.ComparisonDomain

open SquareMaximality SquareMaximality.Dual
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A spanning restriction is its induced active graph together with isolated
vertices. -/
noncomputable def spanningRestrictSumIso
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    (G.induce (S : Set V) ⊕g (⊥ : SimpleGraph {v : V // v ∉ S})) ≃g spanningRestrict G S :=
  { Equiv.Set.sumCompl (S : Set V) with
    map_rel_iff' := by
      rintro (u | u) (v | v)
      · change (G.Adj u.1 v.1 ∧ u.1 ∈ S ∧ v.1 ∈ S) ↔ G.Adj u.1 v.1
        simp [u.property, v.property]
      · change (G.Adj u.1 v.1 ∧ u.1 ∈ S ∧ v.1 ∈ S) ↔ (false : Bool)
        simp [v.property]
      · change (G.Adj u.1 v.1 ∧ u.1 ∈ S ∧ v.1 ∈ S) ↔ (false : Bool)
        simp [u.property]
      · change (G.Adj u.1 v.1 ∧ u.1 ∈ S ∧ v.1 ∈ S) ↔ False
        simp [u.property] }

/-- The forest count of a prefix equals the tree count on its connected
active vertices. This is an equality of actual combinatorial counts. -/
theorem spanningForestCount_spanningRestrict
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    (hconn : (G.induce (S : Set V)).Connected) :
    spanningForestCount (spanningRestrict G S) = SquareMaximality.treeCount (G.induce (S : Set V)) := by
  have h := spanningForestCount_iso (spanningRestrictSumIso G S)
  rw [spanningForestCount_sum, spanningForestCount_bot, mul_one,
    spanningForestCount_eq_treeCount hconn] at h
  exact h.symm

/-- An `r` by `s` rectangle shifted up by one, followed by `k` sites of its
bottom boundary row. -/
noncomputable def rowExtension (r s k : ℕ) : Finset Point :=
  SquareMaximality.rectangle 0 1 r s ∪ SquareMaximality.rectangle 0 0 k 1

theorem mem_rowExtension {r s k : ℕ} {p : Point} : p ∈ rowExtension r s k ↔
    (0 ≤ p.1 ∧ p.1 < r ∧ 1 ≤ p.2 ∧ p.2 ≤ s) ∨
      (0 ≤ p.1 ∧ p.1 < k ∧ p.2 = 0) := by
  simp [rowExtension, SquareMaximality.rectangle]
  omega

theorem rowExtension_card (r s k : ℕ) : (rowExtension r s k).card = r * s + k := by
  have hd : Disjoint (SquareMaximality.rectangle 0 1 r s)
      (SquareMaximality.rectangle 0 0 k 1) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp [SquareMaximality.rectangle] at hp hq
    omega
  rw [rowExtension, Finset.card_union_of_disjoint hd]
  simp [SquareMaximality.rectangle, Finset.card_product, Int.card_Ico]

theorem rowExtension_zero (r s : ℕ) :
    rowExtension r s 0 = SquareMaximality.rectangle 0 1 r s := by
  ext p
  simp [mem_rowExtension, SquareMaximality.rectangle]
  omega

theorem rowExtension_full (r s : ℕ) :
    rowExtension r s r = SquareMaximality.rectangle 0 0 r (s + 1) := by
  ext p
  simp [mem_rowExtension, SquareMaximality.rectangle]
  omega

theorem rowExtension_connected {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (k : ℕ) :
    (inducedGrid (rowExtension r s k)).Connected := by
  by_cases hk : k = 0
  · rw [hk, rowExtension_zero]
    exact rectangle_connected 0 1 hr hs
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hc := SimpleGraph.connected_induce_union
    (G := squareLattice)
    (v := (0, 1)) (w := (0, 0))
    (rectangle_connected 0 1 hr hs).preconnected
    (rectangle_connected 0 0 hkpos (by omega : 0 < 1)).preconnected
    (by simp [SquareMaximality.rectangle]; omega)
    (by simp [SquareMaximality.rectangle]; omega)
    (by norm_num [squareLattice, manhattanDist] : squareLattice.Adj (0, 1) (0, 0))
  change (squareLattice.induce (rowExtension r s k : Set Point)).Connected
  rw [show (rowExtension r s k : Set Point) =
      (SquareMaximality.rectangle 0 1 r s : Set Point) ∪ SquareMaximality.rectangle 0 0 k 1 by
    ext p
    simp only [rowExtension, Finset.mem_coe, Finset.mem_union, Set.mem_union]]
  exact hc

abbrev Frame (r s : ℕ) := Fin r × Fin (s + 1)

def frameGraph (r s : ℕ) : SimpleGraph (Frame r s) :=
  SimpleGraph.pathGraph r □ SimpleGraph.pathGraph (s + 1)

def frameCoord (r s : ℕ) : Frame r s ↪ SquareMaximality.Boundary.LatticePoint where
  toFun p := (p.1.1, p.2.1)
  inj' := by
    intro p q h
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h

def rowActive (r s k : ℕ) : Finset (Frame r s) :=
  Finset.univ.filter (fun p => 0 < p.2.1 ∨ p.1.1 < k)

theorem frameGraph_le_lattice (r s : ℕ) :
    frameGraph r s ≤ SquareMaximality.Boundary.faceLattice.comap (frameCoord r s) := by
  intro p q hpq
  simp only [frameGraph, SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj, Fin.ext_iff] at hpq
  change Nat.dist p.1.1 q.1.1 + Nat.dist p.2.1 q.2.1 = 1
  unfold Nat.dist
  omega

private theorem prefixVertices_succ
    {V : Type*} [Fintype V] (coord : V ↪ SquareMaximality.Boundary.LatticePoint)
    (k : ℕ) (hk : k < Fintype.card V) :
    wordsPrefixVertices coord (k + 1) =
      insert ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) (wordsPrefixVertices coord k) := by
  let e := (wordsOnPageOrderIso coord).toEquiv
  ext v
  have he : v = e ⟨k, hk⟩ ↔ (e.symm v).1 = k := by
    constructor
    · rintro rfl
      simp
    · intro h
      apply e.symm.injective
      apply Fin.ext
      simpa using h
  simp only [wordsPrefixVertices, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  change (e.symm v).1 < k + 1 ↔ v = e ⟨k, hk⟩ ∨ (e.symm v).1 < k
  rw [he]
  omega

theorem rowActive_succ {r s : ℕ} (x : Fin r) :
    rowActive r s (x.1 + 1) = insert (x, 0) (rowActive r s x.1) := by
  ext v
  rcases v with ⟨vx, vy⟩
  simp only [rowActive, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Prod.mk.injEq]
  rw [Fin.ext_iff, Fin.ext_iff]
  simp only [Fin.val_zero]
  omega

/-- The old prefix at the bottom-row vertex `x` consists exactly of the
shifted rectangular core and the preceding bottom-row vertices. -/
theorem frame_prefix_eq_rowActive {r s : ℕ} (x : Fin r) (k : ℕ)
    (hk : k < Fintype.card (Frame r s))
    (hc : frameCoord r s ((wordsOnPageOrderIso (frameCoord r s)).toEquiv ⟨k, hk⟩) = (x.1, 0)) :
    wordsPrefixVertices (frameCoord r s) k = rowActive r s x.1 := by
  ext v
  simp only [rowActive, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hv
    have hkey := key_lt_of_mem_wordsPrefixVertices (frameCoord r s) k hk v hv
    rw [hc] at hkey
    simp [wordsOnPageKey, Prod.Lex.lt_iff, frameCoord] at hkey
    omega
  · intro hv
    have hkey : wordsOnPageKey (frameCoord r s v) < wordsOnPageKey (x.1, 0) := by
      rw [wordsOnPageKey, wordsOnPageKey, Prod.Lex.lt_iff]
      change (-(v.2.1 : ℤ) < 0 ∨ (-(v.2.1 : ℤ) = 0 ∧ v.1.1 < x.1))
      omega
    apply mem_wordsPrefixVertices_of_key_lt (frameCoord r s) k hk v
    simpa only [hc] using hkey

theorem frame_square_complete {r s : ℕ} (hs : 0 < s) (x : Fin r) (hx : 0 < x.1) :
    ContainsUnitSquare (frameGraph r s) (frameCoord r s) (x.1 - 1, 0) := by
  let xm : Fin r := ⟨x.1 - 1, by have := x.2; omega⟩
  let y1 : Fin (s + 1) := ⟨1, by omega⟩
  refine ⟨(xm, 0), (x, 0), (xm, y1), (x, y1), rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · change (x.1, 0) = ((x.1 - 1) + 1, 0)
    congr 1
    omega
  · change (x.1, 1) = ((x.1 - 1) + 1, 1)
    congr 1
    omega
  all_goals simp [frameGraph, SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj,
    Fin.ext_iff, xm, y1] <;> omega

/-- Every bottom-row insertion after its initial leaf receives the proved
Tapp multiplier, on the actual finite prefix graphs. -/
theorem rowForest_step_gain {r s x : ℕ} (hs : 0 < s) (hx : 0 < x) (hxr : x < r) :
    Real.exp squareLatticeEntropy *
      (spanningForestCount (spanningRestrict (frameGraph r s) (rowActive r s x)) : ℝ) ≤
      spanningForestCount (spanningRestrict (frameGraph r s) (rowActive r s (x + 1))) := by
  let v : Frame r s := (⟨x, hxr⟩, 0)
  let e := (wordsOnPageOrderIso (frameCoord r s)).toEquiv
  let k : ℕ := (e.symm v).1
  have hk : k < Fintype.card (Frame r s) := (e.symm v).2
  have hev : e ⟨k, hk⟩ = v := e.apply_symm_apply v
  have hc : frameCoord r s (e ⟨k, hk⟩) = (x, 0) := by rw [hev]; rfl
  have hbefore := frame_prefix_eq_rowActive (r := r) (s := s) ⟨x, hxr⟩ k hk hc
  have hafter : wordsPrefixVertices (frameCoord r s) (k + 1) = rowActive r s (x + 1) := by
    rw [prefixVertices_succ _ k hk, hbefore, hev]
    ext p
    have heq := congrArg (fun F => p ∈ F) (rowActive_succ (s := s) ⟨x, hxr⟩).symm
    apply iff_of_eq
    simpa only [v, Finset.mem_insert] using heq
  have hres : HalfPlaneResistanceBound squareLatticeEntropy :=
    HalfPlaneTwoForestResistanceBound.toHalfPlaneResistanceBound
      (halfPlaneTwoForestResistanceBound_squareLatticeEntropy labeledMultigraphCofactorInput)
  have hcoord : frameCoord r s (e ⟨k, hk⟩) = ((x - 1) + 1, 0) := by
    rw [hc]
    congr 1
    omega
  have hgain := hres.square_multiplier (frameGraph r s) (frameCoord r s) k hk
    (x - 1, 0) (frameGraph_le_lattice r s) (frame_square_complete hs ⟨x, hxr⟩ hx) hcoord
  unfold wordsPrefixMultiplier wordsPrefixGraph at hgain
  rw [hbefore, hafter] at hgain
  have hpos : (0 : ℝ) < spanningForestCount (spanningRestrict (frameGraph r s) (rowActive r s x)) :=
    Nat.cast_pos.mpr (spanningForestCount_pos _)
  exact (le_div_iff₀ hpos).mp hgain

def framePoint {r s : ℕ} (p : Frame r s) : Point := (p.1.1, p.2.1)

private theorem framePoint_mem_rowExtension {r s k : ℕ}
    (p : Frame r s) (hp : p ∈ rowActive r s k) :
    framePoint p ∈ rowExtension r s k := by
  have hv := (Finset.mem_filter.mp hp).2
  have hx := p.1.2
  have hy := p.2.2
  rw [mem_rowExtension]
  dsimp only [framePoint]
  omega

/-- The active part of the finite prefix is the actual induced lattice domain. -/
noncomputable def frameActiveIso {r s k : ℕ} (hk : k ≤ r) :
    (frameGraph r s).induce (rowActive r s k : Set (Frame r s)) ≃g
      inducedGrid (rowExtension r s k) :=
  { Equiv.ofBijective
      (fun p => ⟨framePoint p.1, framePoint_mem_rowExtension p.1 p.2⟩)
      ⟨by
        intro p q h
        have hx := congrArg (fun z : {z // z ∈ rowExtension r s k} => z.1.1) h
        have hy := congrArg (fun z : {z // z ∈ rowExtension r s k} => z.1.2) h
        dsimp only [framePoint] at hx hy
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext <;> omega,
       by
        intro z
        have hz := (mem_rowExtension.mp z.2)
        have hx0 : 0 ≤ z.1.1 := by omega
        have hy0 : 0 ≤ z.1.2 := by omega
        have hxc : (z.1.1.toNat : ℤ) = z.1.1 := Int.toNat_of_nonneg hx0
        have hyc : (z.1.2.toNat : ℤ) = z.1.2 := Int.toNat_of_nonneg hy0
        let p : Frame r s := (⟨z.1.1.toNat, by omega⟩, ⟨z.1.2.toNat, by omega⟩)
        have hp : p ∈ rowActive r s k := by
          simp only [rowActive, Finset.mem_filter, Finset.mem_univ, true_and]
          dsimp only [p]
          omega
        refine ⟨⟨p, hp⟩, ?_⟩
        apply Subtype.ext
        apply Prod.ext
        · exact hxc
        · exact hyc⟩ with
    map_rel_iff' := by
      intro p q
      change manhattanDist (framePoint p.1) (framePoint q.1) = 1 ↔ (frameGraph r s).Adj p.1 q.1
      rw [manhattanDist_eq_one_iff]
      simp only [framePoint, frameGraph, SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj, Fin.ext_iff]
      omega }

theorem rowForest_count_eq_tau {r s k : ℕ} (hr : 0 < r) (hs : 0 < s) (hk : k ≤ r) :
    spanningForestCount (spanningRestrict (frameGraph r s) (rowActive r s k)) =
      tau (rowExtension r s k) := by
  have hc := (frameActiveIso hk).connected_iff.mpr (rowExtension_connected hr hs k)
  rw [spanningForestCount_spanningRestrict _ _ hc]
  exact SquareMaximality.treeCount_congr (frameActiveIso hk)

private theorem rowActive_mono {r s a b : ℕ} (hab : a ≤ b) : rowActive r s a ⊆ rowActive r s b := by
  intro p hp
  simp only [rowActive, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  omega

/-- Telescoping the actual prefix gains leaves exactly one uncharged leaf
in every nonempty added row. -/
theorem rowForest_gain {r s : ℕ} (hs : 0 < s) (k : ℕ) (hk : k ≤ r) :
    Real.exp (squareLatticeEntropy * ((k - 1 : ℕ) : ℝ)) *
      (spanningForestCount (spanningRestrict (frameGraph r s) (rowActive r s 0)) : ℝ) ≤
      spanningForestCount (spanningRestrict (frameGraph r s) (rowActive r s k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst k
      simp only [Nat.succ_sub_one, Nat.cast_zero, mul_zero, Real.exp_zero, one_mul]
      exact_mod_cast spanningForestCount_mono
        (spanningRestrict_mono_vertices (frameGraph r s) (rowActive_mono (by omega : 0 ≤ 1)))
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have hkR : k < r := by omega
      have hi := ih (by omega : k ≤ r)
      have hg := rowForest_step_gain hs hkpos hkR
      have hexp : Real.exp squareLatticeEntropy *
          Real.exp (squareLatticeEntropy * ((k - 1 : ℕ) : ℝ)) =
          Real.exp (squareLatticeEntropy * (k : ℝ)) := by
        rw [← Real.exp_add, Nat.cast_sub hkpos]
        congr 1
        push_cast
        ring
      simpa only [Nat.succ_sub_one, ← mul_assoc, hexp] using
        (mul_le_mul_of_nonneg_left hi (Real.exp_pos squareLatticeEntropy).le).trans hg

theorem rowExtension_treeCount_gain {r s k : ℕ} (hr : 0 < r) (hs : 0 < s) (hk : k ≤ r) :
    Real.exp (squareLatticeEntropy * ((k - 1 : ℕ) : ℝ)) * (tauRect r s : ℝ) ≤
      tau (rowExtension r s k) := by
  have h := rowForest_gain hs k hk
  rw [rowForest_count_eq_tau hr hs (by omega : 0 ≤ r), rowExtension_zero,
    tau_rectangle_eq_tauRect, rowForest_count_eq_tau hr hs hk] at h
  exact h

theorem rowExtension_log_gain {r s k : ℕ} (hr : 0 < r) (hs : 0 < s) (hk : k ≤ r) :
    Real.log (tauRect r s : ℝ) + squareLatticeEntropy * ((k - 1 : ℕ) : ℝ) ≤
      Real.log (tau (rowExtension r s k) : ℝ) := by
  have hpos : (0 : ℝ) < tauRect r s := Nat.cast_pos.mpr (tauRect_pos hr hs)
  have hlog := Real.log_le_log (mul_pos (Real.exp_pos _) hpos) (rowExtension_treeCount_gain hr hs hk)
  rw [Real.log_mul (Real.exp_ne_zero _) hpos.ne', Real.log_exp] at hlog
  linarith

/-- Number of initial leaves in the two boundary additions. -/
def leafSeeds (n q : ℕ) : ℕ := if q = 0 then 0 else if q ≤ n then 1 else 2

/-- An explicit comparison domain of size `n²+q`. The second branch uses the
coordinate-swapped orientation of the completed first rectangle. -/
noncomputable def comparisonDomain (n q : ℕ) : Finset Point :=
  if q ≤ n then rowExtension n n q else rowExtension (n + 1) n (q - n)

theorem comparisonDomain_card (n q : ℕ) : (comparisonDomain n q).card = n^2 + q := by
  unfold comparisonDomain
  split_ifs with hq
  · rw [rowExtension_card]
    ring
  · rw [rowExtension_card]
    have hnq : n ≤ q := by omega
    rw [Nat.add_mul, one_mul, ← pow_two, Nat.add_assoc, Nat.add_sub_of_le hnq]

theorem comparisonDomain_connected {n : ℕ} (hn : 0 < n) (q : ℕ) :
    (inducedGrid (comparisonDomain n q)).Connected := by
  by_cases hqn : q ≤ n
  · rw [comparisonDomain, ite_eq_left hqn]
    exact rowExtension_connected hn hn q
  · rw [comparisonDomain, ite_eq_right hqn]
    exact rowExtension_connected (r := n + 1) (by omega) hn (q - n)

/-- The manuscript's comparison-domain inequality, with all insertion gains
proved for the actual induced graphs. -/
theorem comparisonDomain_log_gain {n q : ℕ} (hn : 0 < n) (hq : q ≤ 2 * n) :
    Real.log (tauRect n n : ℝ) +
      squareLatticeEntropy * ((q : ℝ) - leafSeeds n q) ≤
      Real.log (tau (comparisonDomain n q) : ℝ) := by
  by_cases hq0 : q = 0
  · subst q
    simp [comparisonDomain, leafSeeds, rowExtension_zero, tau_rectangle_eq_tauRect]
  by_cases hqn : q ≤ n
  · have h := rowExtension_log_gain hn hn hqn
    rw [Nat.cast_sub (by omega : 1 ≤ q)] at h
    simpa [comparisonDomain, leafSeeds, hq0, hqn] using h
  · have hfirst := rowExtension_log_gain hn hn (le_refl n)
    rw [rowExtension_full, ← tauRect_eq, Nat.cast_sub hn] at hfirst
    have hsecond := rowExtension_log_gain (by omega : 0 < n + 1) hn
      (by omega : q - n ≤ n + 1)
    rw [tauRect_comm (n + 1) n, Nat.cast_sub (by omega : 1 ≤ q - n),
      Nat.cast_sub (by omega : n ≤ q)] at hsecond
    simp only [Nat.cast_one] at hfirst hsecond
    simp only [comparisonDomain, hqn, ↓reduceIte, leafSeeds, hq0, Nat.cast_ofNat]
    linarith

end SpanningTreeIsoperimetry.ComparisonDomain
