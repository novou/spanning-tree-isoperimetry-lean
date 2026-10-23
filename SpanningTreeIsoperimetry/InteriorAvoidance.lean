module

public import SpanningTreeIsoperimetry.InteriorSquareGain
public import SpanningTreeIsoperimetry.AvoidanceDeterminant
public import SquareMaximality.Dual.ForestEventsConstruction
public import SquareMaximality.Dual.RectangleTransferCurrent

@[expose] public section

set_option backward.privateInPublic true

/-! Extremal edge pairs and the finite event combination in the interior surcharge. -/
namespace SpanningTreeIsoperimetry.InteriorAvoidance

open SquareMaximality SquareMaximality.Boundary SquareMaximality.Dual
open InteriorSquareGain
open scoped BigOperators Classical

/-- Two separated degree-two corners, expressed in lattice coordinates. -/
structure ExtremalPairs {V : Type*} (H : SimpleGraph V) (coord : V ↪ LatticePoint) where
  low : V
  east : V
  north : V
  high : V
  west : V
  south : V
  east_coord : coord east = ((coord low).1 + 1, (coord low).2)
  north_coord : coord north = ((coord low).1, (coord low).2 + 1)
  west_coord : coord west = ((coord high).1 - 1, (coord high).2)
  south_coord : coord south = ((coord high).1, (coord high).2 - 1)
  low_neighbors : ∀ v, H.Adj low v ↔ v = east ∨ v = north
  high_neighbors : ∀ v, H.Adj high v ↔ v = west ∨ v = south
  separation : (coord low).1 + (coord low).2 + 2 ≤ (coord high).1 + (coord high).2

namespace ExtremalPairs
variable {V : Type*} {H : SimpleGraph V} {coord : V ↪ LatticePoint}

noncomputable def lowEdges (d : ExtremalPairs H coord) : Finset (Sym2 V) := by
  classical
  exact {s(d.low, d.east), s(d.low, d.north)}

noncomputable def highEdges (d : ExtremalPairs H coord) : Finset (Sym2 V) := by
  classical
  exact {s(d.high, d.west), s(d.high, d.south)}

theorem lowEdges_card (d : ExtremalPairs H coord) : d.lowEdges.card = 2 := by
  classical
  have hEN : d.east ≠ d.north := by
    intro h
    have hc := congrArg coord h
    rw [d.east_coord, d.north_coord] at hc
    have := congrArg Prod.fst hc
    omega
  have he : s(d.low, d.east) ≠ s(d.low, d.north) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨_, hEN'⟩ | ⟨hLN, hEL⟩
    · exact hEN hEN'
    · exact hEN (hEL.trans hLN)
  simp [lowEdges, he]

theorem highEdges_card (d : ExtremalPairs H coord) : d.highEdges.card = 2 := by
  classical
  have hWS : d.west ≠ d.south := by
    intro h
    have hc := congrArg coord h
    rw [d.west_coord, d.south_coord] at hc
    have hx := congrArg Prod.fst hc
    have hy := congrArg Prod.snd hc
    have hWB : coord d.west = coord d.high := by
      rw [d.west_coord]
      apply Prod.ext <;> omega
    exact ((d.high_neighbors d.west).mpr (Or.inl rfl)).ne (coord.injective hWB).symm
  have he : s(d.high, d.west) ≠ s(d.high, d.south) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨_, hWS'⟩ | ⟨hHS, hWH⟩
    · exact hWS hWS'
    · exact hWS (hWH.trans hHS)
  simp [highEdges, he]

theorem low_ne_high (d : ExtremalPairs H coord) : d.low ≠ d.high := by
  intro h
  have hs := d.separation
  rw [h] at hs
  omega

theorem edgePairs_disjoint (d : ExtremalPairs H coord) : Disjoint d.lowEdges d.highEdges := by
  classical
  rw [Finset.disjoint_left]
  intro e heL heH
  have hH : d.high ∈ e := by
    have he : e = s(d.high, d.west) ∨ e = s(d.high, d.south) := by
      simpa [highEdges] using heH
    rcases he with rfl | rfl <;> simp
  have he : e = s(d.low, d.east) ∨ e = s(d.low, d.north) := by
    simpa [lowEdges] using heL
  have hs := d.separation
  rcases he with rfl | rfl
  · rcases Sym2.mem_iff.mp hH with h | h
    · exact d.low_ne_high h.symm
    · have hc := congrArg coord h
      rw [d.east_coord] at hc
      have hx := congrArg Prod.fst hc
      have hy := congrArg Prod.snd hc
      omega
  · rcases Sym2.mem_iff.mp hH with h | h
    · exact d.low_ne_high h.symm
    · have hc := congrArg coord h
      rw [d.north_coord] at hc
      have hx := congrArg Prod.fst hc
      have hy := congrArg Prod.snd hc
      omega

theorem tree_meets_both (d : ExtremalPairs H coord)
    (T : SimpleGraph V) (hTH : T ≤ H) (hT : T.IsTree) :
    (∃ e ∈ d.lowEdges, e ∈ T.edgeSet) ∧
      (∃ e ∈ d.highEdges, e ∈ T.edgeSet) := by
  classical
  let : Nontrivial V := ⟨⟨d.low, d.high, d.low_ne_high⟩⟩
  obtain ⟨u, hu⟩ := hT.connected.preconnected.exists_adj_of_nontrivial d.low
  obtain ⟨v, hv⟩ := hT.connected.preconnected.exists_adj_of_nontrivial d.high
  constructor
  · refine ⟨s(d.low, u), ?_, hu⟩
    rcases (d.low_neighbors u).mp (hTH hu) with rfl | rfl <;> simp [lowEdges]
  · refine ⟨s(d.high, v), ?_, hv⟩
    rcases (d.high_neighbors v).mp (hTH hv) with rfl | rfl <;> simp [highEdges]

end ExtremalPairs

private theorem lattice_min_neighbors {V : Type*}
    {H : SimpleGraph V} {coord : V ↪ LatticePoint} (hLattice : H ≤ faceLattice.comap coord)
    (a east north : V)
    (he : coord east = ((coord a).1 + 1, (coord a).2))
    (hn : coord north = ((coord a).1, (coord a).2 + 1))
    (hae : H.Adj a east) (han : H.Adj a north)
    (hmin : ∀ v, (coord a).1 + (coord a).2 ≤ (coord v).1 + (coord v).2) :
    ∀ v, H.Adj a v ↔ v = east ∨ v = north := by
  intro v
  constructor
  · intro hav
    have hdist := hLattice hav
    change Nat.dist (coord a).1 (coord v).1 + Nat.dist (coord a).2 (coord v).2 = 1 at hdist
    unfold Nat.dist at hdist
    have hbound := hmin v
    have hc : coord v = ((coord a).1 + 1, (coord a).2) ∨
        coord v = ((coord a).1, (coord a).2 + 1) := by
      simp only [Prod.ext_iff]
      omega
    exact hc.imp (fun h => coord.injective (h.trans he.symm))
      (fun h => coord.injective (h.trans hn.symm))
  · rintro (rfl | rfl) <;> assumption

private theorem lattice_max_neighbors {V : Type*}
    {H : SimpleGraph V} {coord : V ↪ LatticePoint} (hLattice : H ≤ faceLattice.comap coord)
    (a west south : V)
    (hw : coord west = ((coord a).1 - 1, (coord a).2))
    (hs : coord south = ((coord a).1, (coord a).2 - 1))
    (haw : H.Adj a west) (has : H.Adj a south)
    (hmax : ∀ v, (coord v).1 + (coord v).2 ≤ (coord a).1 + (coord a).2) :
    ∀ v, H.Adj a v ↔ v = west ∨ v = south := by
  intro v
  constructor
  · intro hav
    have hdist := hLattice hav
    change Nat.dist (coord a).1 (coord v).1 + Nat.dist (coord a).2 (coord v).2 = 1 at hdist
    unfold Nat.dist at hdist
    have hbound := hmax v
    have hc : coord v = ((coord a).1 - 1, (coord a).2) ∨
        coord v = ((coord a).1, (coord a).2 - 1) := by
      simp only [Prod.ext_iff]
      omega
    exact hc.imp (fun h => coord.injective (h.trans hw.symm))
      (fun h => coord.injective (h.trans hs.symm))
  · rintro (rfl | rfl) <;> assumption

/-- Construct the two extremal corners directly from the displayed square
family. No degree-two or disjointness hypothesis is supplied by the caller. -/
theorem exists_extremalPairsOfSquareUnion
    {V : Type} [Fintype V] (H : SimpleGraph V) (coord : V ↪ LatticePoint)
    (squares : Finset LatticePoint) (hnonempty : squares.Nonempty)
    (hLattice : H ≤ faceLattice.comap coord) (hconn : H.Connected)
    (hsquares : ∀ z ∈ squares, ContainsUnitSquare H coord z)
    (hcover : SquareBoundaryCover H coord squares) : Nonempty (ExtremalPairs H coord) := by
  classical
  obtain ⟨z, hz, hzmin⟩ := squares.exists_min_image (fun z => z.1 + z.2) hnonempty
  obtain ⟨w, hw, hwmax⟩ := squares.exists_max_image (fun z => z.1 + z.2) hnonempty
  obtain ⟨a, east, north, ane, ha, he, hn, hane, hae, han, _, _⟩ := hsquares z hz
  obtain ⟨bsw, south, west, b, hbsw, hs, hw', hb, _, _, hsb, hwb⟩ := hsquares w hw
  have hae_ne : a ≠ east := by
    intro h
    have hc := congrArg coord h
    rw [ha, he] at hc
    have := congrArg Prod.fst hc
    omega
  let : Nontrivial V := ⟨⟨a, east, hae_ne⟩⟩
  have hbounds (v : V) : z.1 + z.2 ≤ (coord v).1 + (coord v).2 ∧
      (coord v).1 + (coord v).2 ≤ w.1 + w.2 + 2 := by
    obtain ⟨u, hvu⟩ := hconn.preconnected.exists_adj_of_nontrivial v
    obtain ⟨q, hq, hvq, _⟩ := hcover hvu
    have hm := hzmin q hq
    have hM := hwmax q hq
    unfold UnitSquareCorner at hvq
    omega
  have he' : coord east = ((coord a).1 + 1, (coord a).2) := by rw [ha]; exact he
  have hn' : coord north = ((coord a).1, (coord a).2 + 1) := by rw [ha]; exact hn
  have hw'' : coord west = ((coord b).1 - 1, (coord b).2) := by simp [hb, hw']
  have hs' : coord south = ((coord b).1, (coord b).2 - 1) := by simp [hb, hs]
  refine ⟨⟨a, east, north, b, west, south, he', hn', hw'', hs', ?_, ?_, ?_⟩⟩
  · apply lattice_min_neighbors hLattice a east north he' hn' hae han
    intro v
    rw [ha]
    exact (hbounds v).1
  · apply lattice_max_neighbors hLattice b west south hw'' hs' hwb.symm hsb.symm
    intro v
    rw [hb]
    have := (hbounds v).2
    omega
  · rw [ha, hb]
    have := hzmin w hw
    omega

/-- Actual extremal pairs for the interior face-star graph. -/
noncomputable def interiorExtremalPairs
    (R S : ℕ) (A : Finset Point)
    (i : Fin (canonicalInteriorCount R S A)) :
    ExtremalPairs (interiorFaceStarGraph R S A i)
      (boundedDualCoreCoord (canonicalInteriorPrimal R S A i)) := by
  classical
  have hnonempty : (canonicalInterior R S A i).Nonempty :=
    (interiorComponent_nonempty R S (canonicalVacancies R S A)
      ((canonicalInteriorEquiv R S A).symm i)).image ofNatPoint
  have hsquares : (interiorSquareStarts R S A i).Nonempty := by
    apply Finset.card_pos.mp
    rw [card_interiorSquareStarts]
    exact Finset.card_pos.mpr hnonempty
  exact Classical.choice (exists_extremalPairsOfSquareUnion
    (interiorFaceStarGraph R S A i)
    (boundedDualCoreCoord (canonicalInteriorPrimal R S A i))
    (interiorSquareStarts R S A i) hsquares (boundedDualCore_le_faceLattice _)
    (interiorFaceStarGraph_connected R S A i)
    (fun z hz => interiorSquareStarts_complete i hz)
    (interiorFaceStar_squareBoundaryCover R S A i))

theorem interiorExtremalPairs_disjoint
    (R S : ℕ) (A : Finset Point)
    (i : Fin (canonicalInteriorCount R S A)) :
    Disjoint (interiorExtremalPairs R S A i).lowEdges
      (interiorExtremalPairs R S A i).highEdges :=
  (interiorExtremalPairs R S A i).edgePairs_disjoint

/-- Every actual local spanning tree meets both separated edge pairs. -/
theorem interior_tree_meets_both
    (R S : ℕ) (A : Finset Point)
    (i : Fin (canonicalInteriorCount R S A)) (T : InteriorFaceStarTree R S A i) :
    (∃ e ∈ (interiorExtremalPairs R S A i).lowEdges, e ∈ T.1.edgeSet) ∧
      (∃ e ∈ (interiorExtremalPairs R S A i).highEdges, e ∈ T.1.edgeSet) :=
  (interiorExtremalPairs R S A i).tree_meets_both T.1 T.2.1 T.2.2

private theorem horizontalBelow_some_coords {r s : ℕ} (e : HorizontalEdge r s)
    (f : BoundedFace r s) (h : horizontalBelow e = some f) :
    f.1.1 = e.x.1 ∧ f.2.1 + 1 = e.y.1 := by
  unfold horizontalBelow at h
  split_ifs at h with h0
  have hx := congrArg (fun p : BoundedFace r s => p.1.1) (Option.some.inj h)
  have hy := congrArg (fun p : BoundedFace r s => p.2.1) (Option.some.inj h)
  dsimp at hx hy
  omega

private theorem horizontalAbove_some_coords {r s : ℕ} (e : HorizontalEdge r s)
    (f : BoundedFace r s) (h : horizontalAbove e = some f) :
    f.1.1 = e.x.1 ∧ f.2.1 = e.y.1 := by
  unfold horizontalAbove at h
  split_ifs at h with h0
  have hx := congrArg (fun p : BoundedFace r s => p.1.1) (Option.some.inj h)
  have hy := congrArg (fun p : BoundedFace r s => p.2.1) (Option.some.inj h)
  exact ⟨hx.symm, hy.symm⟩

private theorem verticalLeft_some_coords {r s : ℕ} (e : VerticalEdge r s)
    (f : BoundedFace r s) (h : verticalLeft e = some f) :
    f.1.1 + 1 = e.x.1 ∧ f.2.1 = e.y.1 := by
  unfold verticalLeft at h
  split_ifs at h with h0
  have hx := congrArg (fun p : BoundedFace r s => p.1.1) (Option.some.inj h)
  have hy := congrArg (fun p : BoundedFace r s => p.2.1) (Option.some.inj h)
  dsimp at hx hy
  omega

private theorem verticalRight_some_coords {r s : ℕ} (e : VerticalEdge r s)
    (f : BoundedFace r s) (h : verticalRight e = some f) :
    f.1.1 = e.x.1 ∧ f.2.1 = e.y.1 := by
  unfold verticalRight at h
  split_ifs at h with h0
  have hx := congrArg (fun p : BoundedFace r s => p.1.1) (Option.some.inj h)
  have hy := congrArg (fun p : BoundedFace r s => p.2.1) (Option.some.inj h)
  exact ⟨hx.symm, hy.symm⟩

private theorem horizontal_bounded_link_coords {r s : ℕ} (e : HorizontalEdge r s)
    (f g : BoundedFace r s)
    (h : (rectangleDual r s).IsLink (.horizontal e) (some f) (some g)) :
    f.1.1 = e.x.1 ∧ g.1.1 = e.x.1 ∧ f.2.1 + g.2.1 + 1 = 2 * e.y.1 := by
  change s(horizontalBelow e, horizontalAbove e) = s(some f, some g) at h
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1' := horizontalBelow_some_coords e f h1
    have h2' := horizontalAbove_some_coords e g h2
    omega
  · have h1' := horizontalBelow_some_coords e g h1
    have h2' := horizontalAbove_some_coords e f h2
    omega

private theorem vertical_bounded_link_coords {r s : ℕ} (e : VerticalEdge r s)
    (f g : BoundedFace r s)
    (h : (rectangleDual r s).IsLink (.vertical e) (some f) (some g)) :
    f.2.1 = e.y.1 ∧ g.2.1 = e.y.1 ∧ f.1.1 + g.1.1 + 1 = 2 * e.x.1 := by
  change s(verticalLeft e, verticalRight e) = s(some f, some g) at h
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1' := verticalLeft_some_coords e f h1
    have h2' := verticalRight_some_coords e g h2
    omega
  · have h1' := verticalLeft_some_coords e g h1
    have h2' := verticalRight_some_coords e f h2
    omega

/-- Parallel dual labels occur only at the exterior root: two bounded faces
have at most one connecting label. -/
theorem rectangleDual_bounded_label_unique {r s : ℕ}
    (f g : BoundedFace r s) (e e' : RectangleEdge r s)
    (he : (rectangleDual r s).IsLink e (some f) (some g))
    (he' : (rectangleDual r s).IsLink e' (some f) (some g)) : e = e' := by
  cases e with
  | horizontal e =>
    have hc := horizontal_bounded_link_coords e f g he
    cases e' with
    | horizontal e' =>
      have hc' := horizontal_bounded_link_coords e' f g he'
      congr 1
      cases e
      cases e'
      dsimp at hc hc'
      congr 1 <;> apply Fin.ext <;> omega
    | vertical e' =>
      have hc' := vertical_bounded_link_coords e' f g he'
      omega
  | vertical e =>
    have hc := vertical_bounded_link_coords e f g he
    cases e' with
    | horizontal e' =>
      have hc' := horizontal_bounded_link_coords e' f g he'
      omega
    | vertical e' =>
      have hc' := vertical_bounded_link_coords e' f g he'
      congr 1
      cases e
      cases e'
      dsimp at hc hc'
      congr 1 <;> apply Fin.ext <;> omega

private theorem exists_interiorEdgeLabel
    {R S : ℕ} {A : Finset Point} {i : Fin (canonicalInteriorCount R S A)}
    (p : (interiorFaceStarGraph R S A i).edgeSet) :
    ∃ e ∈ vacancyDualEdges (canonicalInteriorPrimal R S A i),
      (rectangleDual (R + 1) (S + 1)).ends e =
        Sym2.map (boundedDualCoreToDualVertex (canonicalInteriorPrimal R S A i)) p.1 := by
  induction hp : p.1 using Sym2.inductionOn with
  | _ u v =>
    have huv : (interiorFaceStarGraph R S A i).Adj u v := by
      rw [← SimpleGraph.mem_edgeSet, ← hp]
      exact p.2
    obtain ⟨e, he, hlink⟩ := huv.2
    refine ⟨e, he, ?_⟩
    rw [Sym2.map_mk]
    exact hlink

/-- The unique ambient rectangle label representing a bounded local edge. -/
noncomputable def interiorEdgeLabel
    {R S : ℕ} {A : Finset Point} {i : Fin (canonicalInteriorCount R S A)}
    (p : (interiorFaceStarGraph R S A i).edgeSet) : RectangleEdge (R + 1) (S + 1) :=
  Classical.choose (exists_interiorEdgeLabel p)

theorem interiorEdgeLabel_ends
    {R S : ℕ} {A : Finset Point} {i : Fin (canonicalInteriorCount R S A)}
    (p : (interiorFaceStarGraph R S A i).edgeSet) :
    (rectangleDual (R + 1) (S + 1)).ends (interiorEdgeLabel p) =
      Sym2.map (boundedDualCoreToDualVertex (canonicalInteriorPrimal R S A i)) p.1 :=
  (Classical.choose_spec (exists_interiorEdgeLabel p)).2

theorem interiorEdgeLabel_injective
    {R S : ℕ} {A : Finset Point} {i : Fin (canonicalInteriorCount R S A)} :
    Function.Injective (@interiorEdgeLabel R S A i) := by
  intro p q h
  apply Subtype.ext
  apply Sym2.map.injective (boundedDualCoreToDualVertex (canonicalInteriorPrimal R S A i)).injective
  rw [← interiorEdgeLabel_ends p, ← interiorEdgeLabel_ends q, h]

/-- The label choice is independent of which local tree contains the edge. -/
theorem interiorEdgeLabel_eq_treeLabel
    {R S : ℕ} {A : Finset Point} {i : Fin (canonicalInteriorCount R S A)}
    (T : InteriorFaceStarTree R S A i) (p : T.1.edgeSet) :
    interiorEdgeLabel ⟨p.1, SimpleGraph.edgeSet_mono T.2.1 p.2⟩ = ambientLabelOfFaceStarEdge T p := by
  rcases p with ⟨p, hp⟩
  induction p using Sym2.inductionOn with
  | _ u v =>
    apply rectangleDual_bounded_label_unique u.1 v.1
    · have h := interiorEdgeLabel_ends
        (⟨s(u, v), SimpleGraph.edgeSet_mono T.2.1 hp⟩ : (interiorFaceStarGraph R S A i).edgeSet)
      rw [Sym2.map_mk] at h
      exact h
    · have h := ambientLabelOfFaceStarEdge_ends T ⟨s(u, v), hp⟩
      rw [Sym2.map_mk] at h
      exact h

/-- Map a finite local edge set to its actual ambient labels. -/
noncomputable def interiorLabelsOf
    {R S : ℕ} {A : Finset Point} {i : Fin (canonicalInteriorCount R S A)}
    (F : Finset (Sym2 {f // f ∈ (boundedDualGraph (canonicalInteriorPrimal R S A i)).support}))
    (hF : (F : Set _) ⊆ (interiorFaceStarGraph R S A i).edgeSet) :
    Finset (RectangleEdge (R + 1) (S + 1)) := by
  classical
  exact F.attach.image (fun e => interiorEdgeLabel ⟨e.1, hF e.2⟩)

theorem interiorLabelsOf_card
    {R S : ℕ} {A : Finset Point} {i : Fin (canonicalInteriorCount R S A)}
    (F : Finset (Sym2 {f // f ∈ (boundedDualGraph (canonicalInteriorPrimal R S A i)).support}))
    (hF : (F : Set _) ⊆ (interiorFaceStarGraph R S A i).edgeSet) :
    (interiorLabelsOf F hF).card = F.card := by
  classical
  have hi : Function.Injective (fun e : ↑F => interiorEdgeLabel ⟨e.1, hF e.2⟩) := by
    intro e f h
    apply Subtype.ext
    exact congrArg (fun p : (interiorFaceStarGraph R S A i).edgeSet => p.val)
      (interiorEdgeLabel_injective h)
  rw [interiorLabelsOf, Finset.card_image_of_injective _ hi, Finset.card_attach]

private theorem lowEdges_subset {V : Type*} {H : SimpleGraph V} {coord : V ↪ LatticePoint}
    (d : ExtremalPairs H coord) : (d.lowEdges : Set (Sym2 V)) ⊆ H.edgeSet := by
  classical
  intro e he
  have h : e = s(d.low, d.east) ∨ e = s(d.low, d.north) := by
    simpa [ExtremalPairs.lowEdges] using he
  rcases h with rfl | rfl
  · exact (d.low_neighbors d.east).mpr (Or.inl rfl)
  · exact (d.low_neighbors d.north).mpr (Or.inr rfl)

private theorem highEdges_subset {V : Type*} {H : SimpleGraph V} {coord : V ↪ LatticePoint}
    (d : ExtremalPairs H coord) : (d.highEdges : Set (Sym2 V)) ⊆ H.edgeSet := by
  classical
  intro e he
  have h : e = s(d.high, d.west) ∨ e = s(d.high, d.south) := by
    simpa [ExtremalPairs.highEdges] using he
  rcases h with rfl | rfl
  · exact (d.high_neighbors d.west).mpr (Or.inl rfl)
  · exact (d.high_neighbors d.south).mpr (Or.inr rfl)

noncomputable def interiorLowLabels (R S : ℕ) (A : Finset Point)
    (i : Fin (canonicalInteriorCount R S A)) : Finset (RectangleEdge (R + 1) (S + 1)) :=
  interiorLabelsOf (interiorExtremalPairs R S A i).lowEdges
    (lowEdges_subset (interiorExtremalPairs R S A i))

noncomputable def interiorHighLabels (R S : ℕ) (A : Finset Point)
    (i : Fin (canonicalInteriorCount R S A)) : Finset (RectangleEdge (R + 1) (S + 1)) :=
  interiorLabelsOf (interiorExtremalPairs R S A i).highEdges
    (highEdges_subset (interiorExtremalPairs R S A i))

theorem interior_label_pairs_card (R S : ℕ) (A : Finset Point)
    (i : Fin (canonicalInteriorCount R S A)) :
    (interiorLowLabels R S A i).card = 2 ∧ (interiorHighLabels R S A i).card = 2 := by
  constructor
  · rw [interiorLowLabels, interiorLabelsOf_card]
    exact (interiorExtremalPairs R S A i).lowEdges_card
  · rw [interiorHighLabels, interiorLabelsOf_card]
    exact (interiorExtremalPairs R S A i).highEdges_card

theorem interior_label_pairs_disjoint (R S : ℕ) (A : Finset Point)
    (i : Fin (canonicalInteriorCount R S A)) :
    Disjoint (interiorLowLabels R S A i) (interiorHighLabels R S A i) := by
  classical
  rw [Finset.disjoint_left]
  intro e heL heH
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp heL
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp heH
  have hpq := interiorEdgeLabel_injective (hp.trans hq.symm)
  have hpq' := congrArg Subtype.val hpq
  exact Finset.disjoint_left.mp (interiorExtremalPairs_disjoint R S A i)
    p.2 (hpq' ▸ q.2)

theorem interiorLabelsOf_eq_pair
    {R S : ℕ} {A : Finset Point} {i : Fin (canonicalInteriorCount R S A)}
    (F : Finset (Sym2 {f // f ∈ (boundedDualGraph (canonicalInteriorPrimal R S A i)).support}))
    (hF : (F : Set _) ⊆ (interiorFaceStarGraph R S A i).edgeSet)
    (e f : (interiorFaceStarGraph R S A i).edgeSet) (hpair : F = {e.1, f.1}) :
    interiorLabelsOf F hF = {interiorEdgeLabel e, interiorEdgeLabel f} := by
  classical
  ext l
  constructor
  · intro hl
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hl
    have hpe : p.1 = e.1 ∨ p.1 = f.1 := by simpa [hpair] using p.2
    rcases hpe with hpe | hpf
    · have heq : (⟨p.1, hF p.2⟩ : (interiorFaceStarGraph R S A i).edgeSet) = e := Subtype.ext hpe
      rw [heq] at hp
      simp [← hp]
    · have heq : (⟨p.1, hF p.2⟩ : (interiorFaceStarGraph R S A i).edgeSet) = f := Subtype.ext hpf
      rw [heq] at hp
      simp [← hp]
  · intro hl
    have he : l = interiorEdgeLabel e ∨ l = interiorEdgeLabel f := by simpa using hl
    rcases he with rfl | rfl
    · exact Finset.mem_image.mpr ⟨⟨e.1, by simp [hpair]⟩, Finset.mem_attach _ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨⟨f.1, by simp [hpair]⟩, Finset.mem_attach _ _, rfl⟩

/-- The actual low pair consists of two specified perpendicular bounded links. -/
theorem interiorLowLabels_presentation (R S : ℕ) (A : Finset Point)
    (i : Fin (canonicalInteriorCount R S A)) :
    let d := interiorExtremalPairs R S A i
    ∃ e f : RectangleEdge (R + 1) (S + 1),
      interiorLowLabels R S A i = {e, f} ∧
      (rectangleDual (R + 1) (S + 1)).IsLink e (some d.low.1) (some d.east.1) ∧
      (rectangleDual (R + 1) (S + 1)).IsLink f (some d.low.1) (some d.north.1) := by
  classical
  let d := interiorExtremalPairs R S A i
  let e : (interiorFaceStarGraph R S A i).edgeSet :=
    ⟨s(d.low, d.east), (d.low_neighbors d.east).mpr (Or.inl rfl)⟩
  let f : (interiorFaceStarGraph R S A i).edgeSet :=
    ⟨s(d.low, d.north), (d.low_neighbors d.north).mpr (Or.inr rfl)⟩
  refine ⟨interiorEdgeLabel e, interiorEdgeLabel f, ?_, ?_, ?_⟩
  · apply interiorLabelsOf_eq_pair _ _ e f
    ext x
    simp [ExtremalPairs.lowEdges, ExtremalPairs.highEdges, d, e, f]
  · have h := interiorEdgeLabel_ends e
    change (rectangleDual (R + 1) (S + 1)).ends (interiorEdgeLabel e) =
      Sym2.map (boundedDualCoreToDualVertex (canonicalInteriorPrimal R S A i)) s(d.low, d.east) at h
    rw [Sym2.map_mk] at h
    exact h
  · have h := interiorEdgeLabel_ends f
    change (rectangleDual (R + 1) (S + 1)).ends (interiorEdgeLabel f) =
      Sym2.map (boundedDualCoreToDualVertex (canonicalInteriorPrimal R S A i)) s(d.low, d.north) at h
    rw [Sym2.map_mk] at h
    exact h

/-- The actual high pair consists of two specified perpendicular bounded links. -/
theorem interiorHighLabels_presentation (R S : ℕ) (A : Finset Point)
    (i : Fin (canonicalInteriorCount R S A)) :
    let d := interiorExtremalPairs R S A i
    ∃ e f : RectangleEdge (R + 1) (S + 1),
      interiorHighLabels R S A i = {e, f} ∧
      (rectangleDual (R + 1) (S + 1)).IsLink e (some d.high.1) (some d.west.1) ∧
      (rectangleDual (R + 1) (S + 1)).IsLink f (some d.high.1) (some d.south.1) := by
  classical
  let d := interiorExtremalPairs R S A i
  let e : (interiorFaceStarGraph R S A i).edgeSet :=
    ⟨s(d.high, d.west), (d.high_neighbors d.west).mpr (Or.inl rfl)⟩
  let f : (interiorFaceStarGraph R S A i).edgeSet :=
    ⟨s(d.high, d.south), (d.high_neighbors d.south).mpr (Or.inr rfl)⟩
  refine ⟨interiorEdgeLabel e, interiorEdgeLabel f, ?_, ?_, ?_⟩
  · apply interiorLabelsOf_eq_pair _ _ e f
    ext x
    simp [ExtremalPairs.lowEdges, ExtremalPairs.highEdges, d, e, f]
  · have h := interiorEdgeLabel_ends e
    change (rectangleDual (R + 1) (S + 1)).ends (interiorEdgeLabel e) =
      Sym2.map (boundedDualCoreToDualVertex (canonicalInteriorPrimal R S A i)) s(d.high, d.west) at h
    rw [Sym2.map_mk] at h
    exact h
  · have h := interiorEdgeLabel_ends f
    change (rectangleDual (R + 1) (S + 1)).ends (interiorEdgeLabel f) =
      Sym2.map (boundedDualCoreToDualVertex (canonicalInteriorPrimal R S A i)) s(d.high, d.south) at h
    rw [Sym2.map_mk] at h
    exact h

/-- Each ambient local-tree block meets both transported extremal pairs. -/
theorem interiorEventBlock_meets_both (R S : ℕ) (A : Finset Point)
    (i : Fin (canonicalInteriorCount R S A))
    (j : Fin (interiorFaceStarTreeCount R S A i)) :
    (∃ e ∈ interiorLowLabels R S A i, e ∈ interiorEventBlock R S A i j) ∧
    (∃ e ∈ interiorHighLabels R S A i, e ∈ interiorEventBlock R S A i j) := by
  classical
  let T := interiorFaceStarTreeAt R S A i j
  have ht := interior_tree_meets_both R S A i T
  constructor
  · obtain ⟨p, hpL, hpT⟩ := ht.1
    let pT : T.1.edgeSet := ⟨p, hpT⟩
    refine ⟨ambientLabelOfFaceStarEdge T pT, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨⟨p, hpL⟩, Finset.mem_attach _ _, ?_⟩
      exact interiorEdgeLabel_eq_treeLabel T pT
    · exact (mem_ambientBlockOfFaceStarTree T _).mpr ⟨pT, rfl⟩
  · obtain ⟨p, hpH, hpT⟩ := ht.2
    let pT : T.1.edgeSet := ⟨p, hpT⟩
    refine ⟨ambientLabelOfFaceStarEdge T pT, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨⟨p, hpH⟩, Finset.mem_attach _ _, ?_⟩
      exact interiorEdgeLabel_eq_treeLabel T pT
    · exact (mem_ambientBlockOfFaceStarTree T _).mpr ⟨pT, rfl⟩

/-- Uniform probability of a finite event. -/
noncomputable def finiteProbability {Ω : Type*} [Fintype Ω] (S : Finset Ω) : ℝ :=
  (S.card : ℝ) / Fintype.card Ω

theorem finiteProbability_nonneg {Ω : Type*} [Fintype Ω] (S : Finset Ω) :
    0 ≤ finiteProbability S := by
  unfold finiteProbability
  positivity

theorem finiteProbability_le_one {Ω : Type*} [Fintype Ω] [Nonempty Ω] (S : Finset Ω) :
    finiteProbability S ≤ 1 := by
  have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  unfold finiteProbability
  rw [div_le_one hN]
  exact_mod_cast Finset.card_le_univ S

/-- Inclusion--exclusion for meeting both complementary events. -/
theorem finiteProbability_compl_inter {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] (A B : Finset Ω) :
    finiteProbability (Aᶜ ∩ Bᶜ) =
      1 - finiteProbability A - finiteProbability B + finiteProbability (A ∩ B) := by
  have hu := Finset.card_union_add_card_inter A B
  have hc : (Aᶜ ∩ Bᶜ).card + (A ∪ B).card = Fintype.card Ω := by
    rw [← Finset.compl_union]
    exact Finset.card_compl_add_card _
  have hn : (Aᶜ ∩ Bᶜ).card + A.card + B.card =
      Fintype.card Ω + (A ∩ B).card := by omega
  have hr : ((Aᶜ ∩ Bᶜ).card : ℝ) + A.card + B.card =
      Fintype.card Ω + (A ∩ B).card := by exact_mod_cast hn
  have hN : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
  unfold finiteProbability
  field_simp
  linarith

/-- Negative correlation of avoidance events implies the corresponding
product upper bound on meeting both edge sets. This is an inclusion--exclusion
identity, not an additional probabilistic assumption. -/
theorem meeting_probability_le_product {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] (A B : Finset Ω)
    (hcorr : finiteProbability (A ∩ B) ≤ finiteProbability A * finiteProbability B) :
    finiteProbability (Aᶜ ∩ Bᶜ) ≤
      (1 - finiteProbability A) * (1 - finiteProbability B) := by
  rw [finiteProbability_compl_inter]
  nlinarith only [hcorr]

/-- Once both avoidance margins are known, meeting both pairs has probability
at most `(13/16)^2`. The correlation and local margins remain explicit inputs
to this generic finite-event assembly theorem. -/
theorem meeting_probability_le_thirteen_sixteenths_sq
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω] (A B : Finset Ω)
    (hcorr : finiteProbability (A ∩ B) ≤ finiteProbability A * finiteProbability B)
    (hA : (3 : ℝ) / 16 ≤ finiteProbability A)
    (hB : (3 : ℝ) / 16 ≤ finiteProbability B) :
    finiteProbability (Aᶜ ∩ Bᶜ) ≤ ((13 : ℝ) / 16)^2 := by
  have hpA := finiteProbability_le_one A
  have hpB := finiteProbability_le_one B
  have h1 : 1 - finiteProbability A ≤ (13 : ℝ) / 16 := by linarith
  have h2 : 1 - finiteProbability B ≤ (13 : ℝ) / 16 := by linarith
  have hm := mul_le_mul h1 h2 (by linarith : 0 ≤ 1 - finiteProbability B)
    (by norm_num : (0 : ℝ) ≤ 13 / 16)
  calc
    _ ≤ (1 - finiteProbability A) * (1 - finiteProbability B) :=
      meeting_probability_le_product A B hcorr
    _ ≤ ((13 : ℝ) / 16)^2 := by simpa only [pow_two] using hm

/-- Pairwise disjoint events contained in a common event have bounded total
probability. This will apply to the local-tree containment events. -/
theorem sum_finiteProbability_le
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq Ω]
    (events : ι → Finset Ω) (B : Finset Ω)
    (hdisj : Pairwise (fun i j => Disjoint (events i) (events j)))
    (hsub : ∀ i, events i ⊆ B) :
    (∑ i, finiteProbability (events i)) ≤ finiteProbability B := by
  classical
  have hd : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint events := by
    intro i _ j _ hij
    exact hdisj hij
  have hc : (∑ i, (events i).card) ≤ B.card := by
    rw [← Finset.card_biUnion hd]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
    exact hsub i hxi
  have hcr : (∑ i, ((events i).card : ℝ)) ≤ B.card := by exact_mod_cast hc
  unfold finiteProbability
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right hcr (by positivity)

open SquareMaximality.Multigraph

theorem finiteProbability_avoidance {V E : Type*} [Fintype V] [Fintype E]
    (G : LabeledMultigraph V E) (F : Finset E) :
    finiteProbability (G.spanningTreesAvoiding F) = G.avoidanceRatio F := by
  simp only [finiteProbability, LabeledMultigraph.avoidanceRatio,
    LabeledMultigraph.avoidanceCount, LabeledMultigraph.spanningTreeCount, Nat.card_eq_fintype_card]

theorem finiteProbability_containment {V E : Type*} [Fintype V] [Fintype E]
    (G : LabeledMultigraph V E) (F : Finset E) :
    finiteProbability (G.spanningTreesContaining F) = G.containmentRatio F := by
  simp only [finiteProbability, LabeledMultigraph.containmentRatio,
    LabeledMultigraph.containmentCount, LabeledMultigraph.spanningTreeCount, Nat.card_eq_fintype_card]

theorem avoiding_union_eq_inter {V E : Type*} [Fintype V] [Fintype E]
    (G : LabeledMultigraph V E) (A B : Finset E) :
    G.spanningTreesAvoiding (A ∪ B) = G.spanningTreesAvoiding A ∩ G.spanningTreesAvoiding B := by
  classical
  ext T
  simp [LabeledMultigraph.spanningTreesAvoiding, LabeledMultigraph.spanningTrees,
    Finset.disjoint_union_right]

/-- Actual ambient probability of meeting both designated label sets. -/
noncomputable def meetingBothRatio {V E : Type*} [Fintype V] [Fintype E]
    (G : LabeledMultigraph V E) (A B : Finset E) : ℝ := by
  classical
  exact finiteProbability ((G.spanningTreesAvoiding A)ᶜ ∩ (G.spanningTreesAvoiding B)ᶜ)

/-- The graph-theoretic correlation is discharged by the proved complementary
transfer-current determinant. Only the two local avoidance margins remain. -/
theorem meetingBothRatio_le_thirteen_sixteenths_sq
    {V E : Type*} [Fintype V] [Fintype E]
    (G : LabeledMultigraph V E) (root : V) (A B : Finset E)
    (hCount : 0 < G.spanningTreeCount) (hd : Disjoint A B)
    (hA : (3 : ℝ) / 16 ≤ G.avoidanceRatio A)
    (hB : (3 : ℝ) / 16 ≤ G.avoidanceRatio B) :
    meetingBothRatio G A B ≤ ((13 : ℝ) / 16)^2 := by
  classical
  let : Nonempty G.SpanningTree := (Nat.card_pos_iff.mp hCount).1
  unfold meetingBothRatio
  apply meeting_probability_le_thirteen_sixteenths_sq
    (G.spanningTreesAvoiding A) (G.spanningTreesAvoiding B)
  · rw [← avoiding_union_eq_inter]
    simp only [finiteProbability_avoidance]
    exact G.avoidanceRatio_union_le_mul root A B hCount hd
  · simpa only [finiteProbability_avoidance] using hA
  · simpa only [finiteProbability_avoidance] using hB

/-- A family of incompatible local-tree blocks, all meeting both pairs,
has total containment probability at most the meeting-both probability. -/
theorem sum_containmentRatio_le_meetingBothRatio
    {V E ι : Type*} [Fintype V] [Fintype E] [Fintype ι]
    (G : LabeledMultigraph V E) (A B : Finset E) (F : ι → Finset E)
    (hinc : G.PairwiseIncompatible F)
    (hmeet : ∀ i, (∃ e ∈ A, e ∈ F i) ∧ (∃ e ∈ B, e ∈ F i)) :
    (∑ i, G.containmentRatio (F i)) ≤ meetingBothRatio G A B := by
  classical
  let events := fun i => G.spanningTreesContaining (F i)
  have hdisj : Pairwise (fun i j => Disjoint (events i) (events j)) := by
    intro i j hij
    exact G.pairwiseDisjoint_spanningTreesContaining hinc (by trivial) (by trivial) hij
  have hsub : ∀ i, events i ⊆ (G.spanningTreesAvoiding A)ᶜ ∩ (G.spanningTreesAvoiding B)ᶜ := by
    intro i T hT
    have hFT := (Finset.mem_filter.mp hT).2
    rw [Finset.mem_inter, Finset.mem_compl, Finset.mem_compl]
    constructor
    · intro ha
      have hd := (Finset.mem_filter.mp ha).2
      obtain ⟨e, heA, heF⟩ := (hmeet i).1
      exact Finset.disjoint_left.mp hd (hFT heF) heA
    · intro hb
      have hd := (Finset.mem_filter.mp hb).2
      obtain ⟨e, heB, heF⟩ := (hmeet i).2
      exact Finset.disjoint_left.mp hd (hFT heF) heB
  have h := sum_finiteProbability_le events _ hdisj hsub
  simpa only [events, finiteProbability_containment, meetingBothRatio] using h

/-- The actual interior-component containment sum is bounded once the two
wired-rectangle avoidance estimates are supplied. All pair geometry,
incompatibility, and avoidance negative correlation are proved locally. -/
theorem interior_containment_sum_le_of_pair_avoidance
    (R S : ℕ) (A : Finset Point) (i : Fin (canonicalInteriorCount R S A))
    (hLow : (3 : ℝ) / 16 ≤
      (rectangleDual (R + 1) (S + 1)).avoidanceRatio (interiorLowLabels R S A i))
    (hHigh : (3 : ℝ) / 16 ≤
      (rectangleDual (R + 1) (S + 1)).avoidanceRatio (interiorHighLabels R S A i)) :
    (∑ j, (rectangleDual (R + 1) (S + 1)).containmentRatio (interiorEventBlock R S A i j)) ≤
      ((13 : ℝ) / 16)^2 := by
  have hCount : 0 < (rectangleDual (R + 1) (S + 1)).spanningTreeCount :=
    (rectangleDual (R + 1) (S + 1)).spanningTreeCount_pos_of_connected
      (rectangleDual_connected_pos (by omega) (by omega))
  exact (sum_containmentRatio_le_meetingBothRatio _ _ _ _
    (interiorEventBlock_incompatible R S A i) (interiorEventBlock_meets_both R S A i)).trans
      (meetingBothRatio_le_thirteen_sixteenths_sq _ none _ _ hCount
        (interior_label_pairs_disjoint R S A i) hLow hHigh)

end SpanningTreeIsoperimetry.InteriorAvoidance
