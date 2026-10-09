import SquareMaximality.Dual.TappRayleigh
import SquareMaximality.Inputs.MatrixTreeTheorem

/-! Retaining the initial factor four for connected unions of unit-square boundaries.
The final product assembly is adapted from Jiechen Zhang's included
`SquareMaximality/Dual/TappResistance.lean`, revision
b1d30cdb3334aa7bff7834b22b342393cdc97df8, Apache-2.0;
see `Foundations/LICENSE-SquareMaximality`. The initial multiplier and its
Dirichlet-potential proof are new refinements. -/
namespace SpanningTreeIsoperimetry.InteriorSquareGain

open SquareMaximality SquareMaximality.Boundary SquareMaximality.Dual
open scoped BigOperators

/-- Every edge belongs to one of the displayed complete unit squares.
Isolated vertices are immaterial to this edge-cover condition. -/
def SquareBoundaryCover {V : Type*} (H : SimpleGraph V)
    (coord : V ↪ LatticePoint) (squares : Finset LatticePoint) : Prop :=
  ∀ ⦃u v⦄, H.Adj u v → ∃ z ∈ squares,
    UnitSquareCorner z (coord u) ∧ UnitSquareCorner z (coord v)

/-- A three-level potential at the first square-closing insertion. -/
def seedPotential (z p : LatticePoint) : ℝ :=
  if p.2 ≤ z.2 then 2 else if p.1 ≤ z.1 then 1 else 0

private theorem key_le_iff (z w : LatticePoint) :
    wordsOnPageKey z ≤ wordsOnPageKey w ↔
      w.2 < z.2 ∨ (w.2 = z.2 ∧ z.1 ≤ w.1) := by
  simp only [wordsOnPageKey, Prod.Lex.le_iff, ofLex_toLex]
  omega

private theorem key_lt_se_iff (z p : LatticePoint) :
    wordsOnPageKey p < wordsOnPageKey (z.1 + 1, z.2) ↔
      z.2 < p.2 ∨ (p.2 = z.2 ∧ p.1 ≤ z.1) := by
  simp only [wordsOnPageKey, Prod.Lex.lt_iff, ofLex_toLex]
  omega

set_option maxHeartbeats 2000000 in
/-- In the old prefix of the highest, leftmost square, a nonconstant
potential edge is one of the two edges of its northwest hook. -/
theorem seedPotential_edge_cases {z w p q : LatticePoint}
    (hmin : wordsOnPageKey z ≤ wordsOnPageKey w)
    (hp : UnitSquareCorner w p) (hq : UnitSquareCorner w q)
    (hpo : wordsOnPageKey p < wordsOnPageKey (z.1 + 1, z.2))
    (hqo : wordsOnPageKey q < wordsOnPageKey (z.1 + 1, z.2))
    (hadj : faceLattice.Adj p q)
    (hdiff : seedPotential z p ≠ seedPotential z q) :
    (p = z ∧ q = (z.1, z.2 + 1)) ∨
    (q = z ∧ p = (z.1, z.2 + 1)) ∨
    (p = (z.1, z.2 + 1) ∧ q = (z.1 + 1, z.2 + 1)) ∨
    (q = (z.1, z.2 + 1) ∧ p = (z.1 + 1, z.2 + 1)) := by
  rw [key_le_iff] at hmin
  rw [key_lt_se_iff] at hpo hqo
  simp only [UnitSquareCorner] at hp hq
  change Nat.dist p.1 q.1 + Nat.dist p.2 q.2 = 1 at hadj
  unfold Nat.dist at hadj
  simp only [Prod.ext_iff]
  unfold seedPotential at hdiff
  split_ifs at hdiff <;> norm_num at hdiff <;> omega

/-- Two unit drops across a northwest hook have total Dirichlet energy at
most two, including any zero-energy edges elsewhere in the graph. -/
theorem seedPotential_energy_le_two
    {V : Type} [Fintype V] (P : SimpleGraph V)
    (coord : V ↪ LatticePoint) (z : LatticePoint) (sw nw ne : V)
    (hsw : coord sw = z) (hnw : coord nw = (z.1, z.2 + 1))
    (hne : coord ne = (z.1 + 1, z.2 + 1))
    (hcases : ∀ u v, P.Adj u v → seedPotential z (coord u) ≠ seedPotential z (coord v) →
      (u = sw ∧ v = nw) ∨ (u = nw ∧ v = sw) ∨
      (u = nw ∧ v = ne) ∨ (u = ne ∧ v = nw)) :
    dirichletEnergy P (fun v => seedPotential z (coord v)) ≤ 2 := by
  classical
  have hswNW : sw ≠ nw := by
    intro h
    have hh := congrArg coord h
    rw [hsw, hnw] at hh
    have := congrArg Prod.snd hh
    omega
  have hswNE : sw ≠ ne := by
    intro h
    have hh := congrArg coord h
    rw [hsw, hne] at hh
    have := congrArg Prod.snd hh
    omega
  have hnwNE : nw ≠ ne := by
    intro h
    have hh := congrArg coord h
    rw [hnw, hne] at hh
    have := congrArg Prod.fst hh
    omega
  let F : Finset (V × V) := {(sw, nw), (nw, sw), (nw, ne), (ne, nw)}
  let f : V → ℝ := fun v => seedPotential z (coord v)
  have hs : (∑ p : V × V, if P.Adj p.1 p.2 then (f p.1 - f p.2)^2 else 0) =
      ∑ p ∈ F, if P.Adj p.1 p.2 then (f p.1 - f p.2)^2 else 0 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ F)
    intro p _ hp
    by_cases ha : P.Adj p.1 p.2
    · rw [ite_eq_left ha]
      have heq : f p.1 = f p.2 := by
        by_contra heq
        have hc := hcases p.1 p.2 ha heq
        have hpF : p ∈ F := by
          rcases p with ⟨u, v⟩
          rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            simp [F]
        exact hp hpF
      rw [heq, sub_self, zero_pow (by decide)]
    · rw [ite_eq_right ha]
  have hb : (∑ p ∈ F, if P.Adj p.1 p.2 then (f p.1 - f p.2)^2 else 0) ≤ 4 := by
    calc
      _ ≤ ∑ p ∈ F, (f p.1 - f p.2)^2 := by
        apply Finset.sum_le_sum
        intro p _
        split_ifs <;> first | exact le_rfl | exact sq_nonneg _
      _ = 4 := by
        norm_num [F, f, seedPotential, hsw, hnw, hne, hswNW, hswNE, hnwNE,
          hswNW.symm, hswNE.symm, hnwNE.symm]
  unfold dirichletEnergy adjacencyPairFinset
  rw [Finset.sum_filter]
  change (∑ p : V × V, if P.Adj p.1 p.2 then (f p.1 - f p.2)^2 else 0) / 2 ≤ 2
  rw [hs]
  linarith

/-- A concrete potential gives the lower resistance bound even if the
prefix has other connected components. -/
theorem two_le_resistance_of_potential
    {V : Type} [Fintype V] [DecidableEq V] (P : SimpleGraph V) [DecidableRel P.Adj]
    (a b : V) (hab : a ≠ b) (hnotadj : ¬P.Adj a b) (hreach : P.Reachable a b)
    (f : V → ℝ) (hf : f a - f b = 2) (henergy : dirichletEnergy P f ≤ 2) :
    2 ≤ twoForestResistance P a b := by
  classical
  let a' : ReachableVertex P a := ⟨a, SimpleGraph.Reachable.refl a⟩
  let b' : ReachableVertex P a := ⟨b, hreach⟩
  let e : InjectiveGraphHom (reachableComponentGraph P a) P :=
    { toEmbedding := Function.Embedding.subtype _
      map_adj := fun h => h }
  have hcomp := e.dirichletEnergy_pullback_le f
  have hbound := dirichletObjective_le_twoForestResistance
    (twoForestCofactorInput_of_matrixTree labeledMultigraphCofactorInput)
    (reachableComponentGraph P a) (reachableComponentGraph_connected P a)
    a' b' (fun h => hab (congrArg Subtype.val h)) hnotadj (e.pullback f)
  have hobj : 2 ≤ dirichletObjective (reachableComponentGraph P a) a' b' (e.pullback f) := by
    unfold dirichletObjective
    change 2 ≤ 2 * (f a - f b) - dirichletEnergy (reachableComponentGraph P a) (e.pullback f)
    rw [hf]
    linarith
  have hres := hobj.trans hbound
  rw [twoForestResistance_eq_reachableComponent P a b hreach]
  exact hres

/-- The first square in words-on-a-page order closes with multiplier at least
four. Its exceptional gain is proved from the square-union geometry. -/
theorem first_square_multiplier_ge_four
    {V : Type} [Fintype V] (H : SimpleGraph V) (coord : V ↪ LatticePoint)
    (squares : Finset LatticePoint) (z : LatticePoint)
    (hLattice : H ≤ faceLattice.comap coord)
    (hcover : SquareBoundaryCover H coord squares)
    (hmin : ∀ w ∈ squares, wordsOnPageKey z ≤ wordsOnPageKey w)
    (hsquare : ContainsUnitSquare H coord z)
    (k : ℕ) (hk : k < Fintype.card V)
    (hcoord : coord ((wordsOnPageOrderIso coord).toEquiv ⟨k, hk⟩) = (z.1 + 1, z.2)) :
    4 ≤ wordsPrefixMultiplier H coord k := by
  classical
  let P := wordsPrefixGraph H coord k
  let sw := unitSquareSWVertex hsquare
  let nw := unitSquareNWCornerVertex hsquare
  let ne := unitSquareNECornerVertex hsquare
  have hsw : coord sw = z := unitSquareSWVertex_coord hsquare
  have hnw : coord nw = (z.1, z.2 + 1) := unitSquareNWCornerVertex_coord hsquare
  have hne : coord ne = (z.1 + 1, z.2 + 1) := unitSquareNECornerVertex_coord hsquare
  have hcases (u v : V) (huv : P.Adj u v)
      (hdiff : seedPotential z (coord u) ≠ seedPotential z (coord v)) :
      (u = sw ∧ v = nw) ∨ (u = nw ∧ v = sw) ∨
      (u = nw ∧ v = ne) ∨ (u = ne ∧ v = nw) := by
    obtain ⟨w, hw, huw, hvw⟩ := hcover huv.1
    have huo := key_lt_of_mem_wordsPrefixVertices coord k hk u huv.2.1
    have hvo := key_lt_of_mem_wordsPrefixVertices coord k hk v huv.2.2
    rw [hcoord] at huo hvo
    have hc := seedPotential_edge_cases (hmin w hw) huw hvw huo hvo (hLattice huv.1) hdiff
    rcases hc with ⟨hu, hv⟩ | ⟨hv, hu⟩ | ⟨hu, hv⟩ | ⟨hv, hu⟩
    · exact Or.inl ⟨coord.injective (hu.trans hsw.symm), coord.injective (hv.trans hnw.symm)⟩
    · exact Or.inr (Or.inl ⟨coord.injective (hu.trans hnw.symm), coord.injective (hv.trans hsw.symm)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨coord.injective (hu.trans hnw.symm), coord.injective (hv.trans hne.symm)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨coord.injective (hu.trans hne.symm), coord.injective (hv.trans hnw.symm)⟩))
  have henergy := seedPotential_energy_le_two P coord z sw nw ne hsw hnw hne hcases
  have hswne : sw ≠ ne := by
    intro heq
    have he := congrArg coord heq
    rw [hsw, hne] at he
    have := congrArg Prod.snd he
    omega
  have hnotadj : ¬P.Adj sw ne := by
    intro h
    have hl := hLattice h.1
    change faceLattice.Adj (coord sw) (coord ne) at hl
    rw [hsw, hne] at hl
    simp [faceLattice, natManhattanDist, Nat.dist] at hl
  have hreach : P.Reachable sw ne :=
    wordsPrefixGraph_square_neighbors_reachable coord k hk z hsquare hcoord
  have hf : seedPotential z (coord sw) - seedPotential z (coord ne) = 2 := by
    simp [hsw, hne, seedPotential]
  have hr := two_le_resistance_of_potential P sw ne hswne hnotadj hreach
    (fun v => seedPotential z (coord v)) hf henergy
  rw [wordsPrefixMultiplier_eq_two_add_twoForestResistance H coord k hk z hLattice hsquare hcoord]
  change 2 ≤ twoForestResistance (wordsPrefixGraph H coord k)
    (unitSquareSWVertex hsquare) (unitSquareNECornerVertex hsquare) at hr
  linarith

/-- A connected union of complete unit-square boundaries retains the initial
factor four, while every later displayed square contributes `exp h`. -/
theorem square_union_treeCount_lower_bound
    {V : Type} [Fintype V] (H : SimpleGraph V) (coord : V ↪ LatticePoint)
    (squares : Finset LatticePoint) (hnonempty : squares.Nonempty)
    (hLattice : H ≤ faceLattice.comap coord) (hconn : H.Connected)
    (hsquares : ∀ z ∈ squares, ContainsUnitSquare H coord z)
    (hcover : SquareBoundaryCover H coord squares) :
    4 * Real.exp (squareLatticeEntropy * ((squares.card : ℝ) - 1)) ≤ treeCount H := by
  classical
  obtain ⟨z₀, hz₀, hmin⟩ := squares.exists_min_image wordsOnPageKey hnonempty
  have hres : HalfPlaneResistanceBound squareLatticeEntropy :=
    HalfPlaneTwoForestResistanceBound.toHalfPlaneResistanceBound
      (halfPlaneTwoForestResistanceBound_squareLatticeEntropy labeledMultigraphCofactorInput)
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
      (if k ∈ marked then Real.exp squareLatticeEntropy else 1) ≤
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

  let k₀ : ℕ := squareIndex ⟨z₀, hz₀⟩
  have hk₀ : k₀ ∈ marked := Finset.mem_image.mpr ⟨⟨z₀, hz₀⟩, Finset.mem_attach _ _, rfl⟩
  have hk₀n : k₀ ∈ Finset.range n := hmarkedSubset hk₀
  have hk₀lt : k₀ < Fintype.card V := Finset.mem_range.mp hk₀n
  have hcurrent : coord (e ⟨k₀, hk₀lt⟩) = (z₀.1 + 1, z₀.2) := by
    have heq : (⟨k₀, hk₀lt⟩ : Fin (Fintype.card V)) = e.symm (squareVertex ⟨z₀, hz₀⟩) := by
      apply Fin.ext
      rfl
    rw [heq, e.apply_symm_apply]
    exact unitSquareSEVertex_coord (hsquares z₀ hz₀)
  have hseed : 4 ≤ wordsPrefixMultiplier H coord k₀ :=
    first_square_multiplier_ge_four H coord squares z₀ hLattice hcover hmin
      (hsquares z₀ hz₀) k₀ hk₀lt hcurrent
  have hmarkedCard : marked.card = squares.card := by
    change (squares.attach.image squareIndex).card = squares.card
    rw [Finset.card_image_iff.mpr hsquareIndex_injective.injOn]
    simp
  have hinter : (Finset.range n).erase k₀ ∩ marked = marked.erase k₀ := by
    ext k
    simp only [Finset.mem_inter, Finset.mem_erase]
    constructor
    · exact fun ⟨⟨hkne, _⟩, hkm⟩ => ⟨hkne, hkm⟩
    · exact fun ⟨hkne, hkm⟩ => ⟨⟨hkne, hmarkedSubset hkm⟩, hkm⟩
  have hprodBase :
      (∏ k ∈ (Finset.range n).erase k₀, if k ∈ marked then Real.exp squareLatticeEntropy else 1) =
        Real.exp squareLatticeEntropy ^ (squares.card - 1) := by
    rw [Finset.prod_ite_mem, hinter]
    simp only [Finset.prod_const, Finset.card_erase_of_mem hk₀, hmarkedCard]
  have hprod := Finset.prod_le_prod₀
    (s := (Finset.range n).erase k₀)
    (fun k _ => by split_ifs <;> positivity)
    (fun k hk => hfactor k (Finset.mem_of_mem_erase hk))
  have hrestNonneg : 0 ≤ ∏ k ∈ (Finset.range n).erase k₀, wordsPrefixMultiplier H coord k :=
    Finset.prod_nonneg (fun k _ => (wordsPrefixMultiplier_one_le H coord k).trans' zero_le_one)
  have hcard : 1 ≤ squares.card := Finset.card_pos.mpr hnonempty
  calc
    4 * Real.exp (squareLatticeEntropy * ((squares.card : ℝ) - 1)) =
        4 * Real.exp squareLatticeEntropy ^ (squares.card - 1) := by
      rw [← Real.exp_nat_mul, Nat.cast_sub hcard]
      congr 2
      simp only [Nat.cast_one]
      ring
    _ = 4 * ∏ k ∈ (Finset.range n).erase k₀,
        if k ∈ marked then Real.exp squareLatticeEntropy else 1 := by rw [hprodBase]
    _ ≤ 4 * ∏ k ∈ (Finset.range n).erase k₀, wordsPrefixMultiplier H coord k :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ ≤ wordsPrefixMultiplier H coord k₀ *
        ∏ k ∈ (Finset.range n).erase k₀, wordsPrefixMultiplier H coord k :=
      mul_le_mul_of_nonneg_right hseed hrestNonneg
    _ = ∏ k ∈ Finset.range n, wordsPrefixMultiplier H coord k :=
      Finset.mul_prod_erase _ _ hk₀n
    _ = spanningForestCount H := product_prefixMultipliers H coord
    _ = treeCount H := by exact_mod_cast spanningForestCount_eq_treeCount hconn

/-- The face-star graph of an interior component is actually covered by the
complete unit squares contributed by its primal vacancy vertices. -/
theorem interiorFaceStar_squareBoundaryCover
    (R S : ℕ) (A : Finset Point)
    (i : Fin (canonicalInteriorCount R S A)) :
    SquareBoundaryCover (interiorFaceStarGraph R S A i)
      (boundedDualCoreCoord (canonicalInteriorPrimal R S A i))
      (interiorSquareStarts R S A i) := by
  classical
  intro u v huv
  change (boundedDualGraph (canonicalInteriorPrimal R S A i)).Adj u.1 v.1 at huv
  obtain ⟨e, he, hlink⟩ := huv.2
  obtain ⟨p, hp, hpinc⟩ := mem_vacancyDualEdges.mp he
  have hsingle : ∀ q ∈ ({p} : Finset (Fin (R + 1) × Fin (S + 1))),
      0 < q.1.1 ∧ q.1.1 < R ∧ 0 < q.2.1 ∧ q.2.1 < S := by
    intro q hq
    have hqp : q = p := Finset.mem_singleton.mp hq
    subst q
    exact canonicalInteriorPrimal_bounds hp
  have hadj : (boundedDualGraph ({p} : Finset (Fin (R + 1) × Fin (S + 1)))).Adj u.1 v.1 := by
    exact ⟨huv.1, e, mem_vacancyDualEdges.mpr ⟨p, by simp, hpinc⟩, hlink⟩
  obtain ⟨q, hq, hucorner⟩ := boundedDualGraph_vertex_corner_of_adj hsingle hadj
  obtain ⟨q', hq', hvcorner⟩ := boundedDualGraph_vertex_corner_of_adj hsingle hadj.symm
  have hqp : q = p := Finset.mem_singleton.mp hq
  have hq'p : q' = p := Finset.mem_singleton.mp hq'
  subst q
  subst q'
  refine ⟨faceSquareStart p, ?_, hucorner, hvcorner⟩
  exact Finset.mem_image.mpr ⟨p, hp, rfl⟩

/-- The strengthened multiplicity bound for the actual interior face-star
component, including its initial factor four. -/
theorem interiorFaceStarTreeCount_lower_bound
    (R S : ℕ) (A : Finset Point)
    (i : Fin (canonicalInteriorCount R S A)) :
    4 * Real.exp (squareLatticeEntropy * ((canonicalInterior R S A i).card - 1 : ℝ)) ≤
      interiorFaceStarTreeCount R S A i := by
  classical
  have hnonempty : (canonicalInterior R S A i).Nonempty := by
    exact (interiorComponent_nonempty R S (canonicalVacancies R S A)
      ((canonicalInteriorEquiv R S A).symm i)).image ofNatPoint
  have hsquares : (interiorSquareStarts R S A i).Nonempty := by
    apply Finset.card_pos.mp
    rw [card_interiorSquareStarts]
    exact Finset.card_pos.mpr hnonempty
  have h := square_union_treeCount_lower_bound (interiorFaceStarGraph R S A i)
    (boundedDualCoreCoord (canonicalInteriorPrimal R S A i))
    (interiorSquareStarts R S A i) hsquares (boundedDualCore_le_faceLattice _)
    (interiorFaceStarGraph_connected R S A i)
    (fun z hz => interiorSquareStarts_complete i hz)
    (interiorFaceStar_squareBoundaryCover R S A i)
  rw [card_interiorSquareStarts, ← interiorFaceStarTreeCount_eq_treeCount] at h
  exact h

end SpanningTreeIsoperimetry.InteriorSquareGain
