module

public import SpanningTreeIsoperimetry.WiredPatchGeometry
public import SpanningTreeIsoperimetry.WiredPatchSymmetry
public import SpanningTreeIsoperimetry.InteriorAvoidance

@[expose] public section

set_option backward.privateInPublic true

/-! The actual rectangle-dual perpendicular pairs inherit the free-patch
avoidance margin, including pairs arbitrarily close to a wired boundary. -/
namespace SpanningTreeIsoperimetry.WiredPairs

open SquareMaximality SquareMaximality.Dual SquareMaximality.Boundary SquareMaximality.Multigraph
open WiredRayleigh WiredPatchGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

private theorem clip_coe {R S : ℕ} (p : BoundedFace (R+1) (S+1)) :
    clip R S (p.1 : ℤ) (p.2 : ℤ) = some p := by
  have hx : (p.1 : ℤ) < R := by exact_mod_cast p.1.isLt
  have hy : (p.2 : ℤ) < S := by exact_mod_cast p.2.isLt
  have hi : Inside R S (p.1 : ℤ) (p.2 : ℤ) := ⟨by positivity,hx,by positivity,hy⟩
  simp [clip,hi]

private theorem centered_vertex {R S : ℕ} (p q : BoundedFace (R+1) (S+1))
    (u : Fin 5 × Fin 5)
    (hx : (p.1 : ℤ) - 2 + u.1 = q.1) (hy : (p.2 : ℤ) - 2 + u.2 = q.2) :
    (clippingWiring R S ((p.1 : ℤ)-2) ((p.2 : ℤ)-2)).vertexMap u = some q := by
  change clip R S ((p.1 : ℤ)-2+u.1) ((p.2 : ℤ)-2+u.2) = some q
  rw [hx,hy]
  exact clip_coe q

/-- A selected two-edge event is transported by its actual bounded endpoints.
All matrix/probability comparisons are supplied by the proved wiring theorem. -/
private theorem pair_margin_of_wiring {R S : ℕ}
    (d : Wiring (rectanglePrimal 5 5) (rectangleDual (R+1) (S+1)))
    (a b c : Fin 5 × Fin 5) (se sf : RectangleEdge 5 5)
    (hse : (rectanglePrimal 5 5).IsLink se a b)
    (hsf : (rectanglePrimal 5 5).IsLink sf a c)
    (hMargin : (3 : ℝ)/16 < (rectanglePrimal 5 5).avoidanceRatio {se,sf})
    (p q t : BoundedFace (R+1) (S+1))
    (ha : d.vertexMap a = some p) (hb : d.vertexMap b = some q) (hc : d.vertexMap c = some t)
    (hpq : p ≠ q) (hpt : p ≠ t)
    (e f : RectangleEdge (R+1) (S+1))
    (he : (rectangleDual (R+1) (S+1)).IsLink e (some p) (some q))
    (hf : (rectangleDual (R+1) (S+1)).IsLink f (some p) (some t)) :
    (3 : ℝ)/16 < (rectangleDual (R+1) (S+1)).avoidanceRatio {e,f} := by
  classical
  let A : Finset (RectangleEdge 5 5) := {se,sf}
  have hActive : ∀ z ∈ A, ¬(Sym2.map d.vertexMap ((rectanglePrimal 5 5).ends z)).IsDiag := by
    intro z hz
    have hz' : z = se ∨ z = sf := by simpa [A] using hz
    rcases hz' with hz | hz
    · change (rectanglePrimal 5 5).ends se = s(a,b) at hse
      rw [hz,hse,Sym2.map_mk,ha,hb]
      simpa using hpq
    · change (rectanglePrimal 5 5).ends sf = s(a,c) at hsf
      rw [hz,hsf,Sym2.map_mk,ha,hc]
      simpa using hpt
  have heA : se ∈ A := by simp [A]
  have hfA : sf ∈ A := by simp [A]
  have hmapE : d.selectedLabelMap A hActive ⟨se,heA⟩ = e := by
    apply InteriorAvoidance.rectangleDual_bounded_label_unique p q _ _ _ he
    change (rectangleDual (R+1) (S+1)).ends (d.edgeMap ⟨se,hActive se heA⟩) = s(some p,some q)
    have h := d.map_ends ⟨se,hActive se heA⟩
    change (rectanglePrimal 5 5).ends se = s(a,b) at hse
    rwa [hse,Sym2.map_mk,ha,hb] at h
  have hmapF : d.selectedLabelMap A hActive ⟨sf,hfA⟩ = f := by
    apply InteriorAvoidance.rectangleDual_bounded_label_unique p t _ _ _ hf
    change (rectangleDual (R+1) (S+1)).ends (d.edgeMap ⟨sf,hActive sf hfA⟩) = s(some p,some t)
    have h := d.map_ends ⟨sf,hActive sf hfA⟩
    change (rectanglePrimal 5 5).ends sf = s(a,c) at hsf
    rwa [hsf,Sym2.map_mk,ha,hc] at h
  have hlabels : d.selectedLabels A hActive = {e,f} := by
    ext z
    constructor
    · intro hz
      obtain ⟨u,hu⟩ := (WiredPatchSymmetry.mem_selectedLabels_iff d A hActive z).mp hz
      have huA : u.1 = se ∨ u.1 = sf := by simpa only [A,Finset.mem_insert,Finset.mem_singleton] using u.2
      rcases huA with hus | huf
      · have hu' : u = ⟨se,heA⟩ := Subtype.ext hus
        rw [hu',hmapE] at hu
        simp [← hu]
      · have hu' : u = ⟨sf,hfA⟩ := Subtype.ext huf
        rw [hu',hmapF] at hu
        simp [← hu]
    · intro hz
      have hz' : z = e ∨ z = f := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hz
      rcases hz' with rfl | rfl
      · exact (WiredPatchSymmetry.mem_selectedLabels_iff d A hActive _).mpr ⟨⟨se,heA⟩,hmapE⟩
      · exact (WiredPatchSymmetry.mem_selectedLabels_iff d A hActive _).mpr ⟨⟨sf,hfA⟩,hmapF⟩
  have hG : 0 < (rectanglePrimal 5 5).spanningTreeCount := by
    rw [FreePatchBridge.labelledPatch_treeCount]
    norm_num
  have hH : 0 < (rectangleDual (R+1) (S+1)).spanningTreeCount :=
    (rectangleDual (R+1) (S+1)).spanningTreeCount_pos_of_connected
      (rectangleDual_connected_pos (by omega) (by omega))
  have h := d.avoidanceRatio_le (0,0) none A hActive hG hH
  rw [hlabels] at h
  exact hMargin.trans_le h

/-- A bounded north/east pair has strictly more than `3/16` avoidance probability. -/
theorem northEast_avoidance_gt {R S : ℕ}
    (p q t : BoundedFace (R+1) (S+1))
    (hq : boundedFaceCoord q = (p.1.val+1,p.2.val))
    (ht : boundedFaceCoord t = (p.1.val,p.2.val+1))
    (e f : RectangleEdge (R+1) (S+1))
    (he : (rectangleDual (R+1) (S+1)).IsLink e (some p) (some q))
    (hf : (rectangleDual (R+1) (S+1)).IsLink f (some p) (some t)) :
    (3 : ℝ)/16 < (rectangleDual (R+1) (S+1)).avoidanceRatio {e,f} := by
  let d := clippingWiring R S ((p.1 : ℤ)-2) ((p.2 : ℤ)-2)
  have hxq : (q.1 : ℤ) = (p.1 : ℤ)+1 := by exact_mod_cast congrArg Prod.fst hq
  have hyq : (q.2 : ℤ) = p.2 := by exact_mod_cast congrArg Prod.snd hq
  have hxt : (t.1 : ℤ) = p.1 := by exact_mod_cast congrArg Prod.fst ht
  have hyt : (t.2 : ℤ) = (p.2 : ℤ)+1 := by exact_mod_cast congrArg Prod.snd ht
  have hpq : p ≠ q := by intro hh; subst q; omega
  have hpt : p ≠ t := by intro hh; subst t; omega
  apply pair_margin_of_wiring d (2,2) (3,2) (2,3)
    (.horizontal ⟨2,2⟩) (.vertical ⟨2,2⟩) (by rfl) (by rfl)
    FreePatchBridge.labelledPatch_avoidanceRatio_gt p q t
    (centered_vertex p p (2,2) (by norm_num) (by norm_num))
    (centered_vertex p q (3,2) (by norm_num; omega) (by norm_num; omega))
    (centered_vertex p t (2,3) (by norm_num; omega) (by norm_num; omega)) hpq hpt e f he hf

/-- A bounded south/west pair has the same strict universal avoidance margin. -/
theorem southWest_avoidance_gt {R S : ℕ}
    (p q t : BoundedFace (R+1) (S+1))
    (hq : boundedFaceCoord p = (q.1.val+1,q.2.val))
    (ht : boundedFaceCoord p = (t.1.val,t.2.val+1))
    (e f : RectangleEdge (R+1) (S+1))
    (he : (rectangleDual (R+1) (S+1)).IsLink e (some p) (some q))
    (hf : (rectangleDual (R+1) (S+1)).IsLink f (some p) (some t)) :
    (3 : ℝ)/16 < (rectangleDual (R+1) (S+1)).avoidanceRatio {e,f} := by
  let d := clippingWiring R S ((p.1 : ℤ)-2) ((p.2 : ℤ)-2)
  have hxq : (p.1 : ℤ) = (q.1 : ℤ)+1 := by exact_mod_cast congrArg Prod.fst hq
  have hyq : (p.2 : ℤ) = q.2 := by exact_mod_cast congrArg Prod.snd hq
  have hxt : (p.1 : ℤ) = t.1 := by exact_mod_cast congrArg Prod.fst ht
  have hyt : (p.2 : ℤ) = (t.2 : ℤ)+1 := by exact_mod_cast congrArg Prod.snd ht
  have hpq : p ≠ q := by intro hh; subst q; omega
  have hpt : p ≠ t := by intro hh; subst t; omega
  apply pair_margin_of_wiring d (2,2) (1,2) (2,1)
    (.horizontal ⟨1,2⟩) (.vertical ⟨2,1⟩)
    (by change s((1,2),(2,2)) = s((2,2),(1,2)); exact Sym2.eq_swap)
    (by change s((2,1),(2,2)) = s((2,2),(2,1)); exact Sym2.eq_swap)
    WiredPatchSymmetry.southWest_avoidanceRatio_gt p q t
    (centered_vertex p p (2,2) (by norm_num) (by norm_num))
    (centered_vertex p q (1,2) (by norm_num; omega) (by norm_num; omega))
    (centered_vertex p t (2,1) (by norm_num; omega) (by norm_num; omega)) hpq hpt e f he hf

/-- The low extremal pair of every actual interior component has the local margin. -/
theorem interiorLow_avoidance_gt (R S : ℕ) (A : Finset Point)
    (i : Fin (canonicalInteriorCount R S A)) :
    (3 : ℝ)/16 < (rectangleDual (R+1) (S+1)).avoidanceRatio
      (InteriorAvoidance.interiorLowLabels R S A i) := by
  let d := InteriorAvoidance.interiorExtremalPairs R S A i
  obtain ⟨e,f,hset,he,hf⟩ := InteriorAvoidance.interiorLowLabels_presentation R S A i
  rw [hset]
  exact northEast_avoidance_gt d.low.1 d.east.1 d.north.1 d.east_coord d.north_coord e f he hf

/-- The high extremal pair of every actual interior component has the local margin. -/
theorem interiorHigh_avoidance_gt (R S : ℕ) (A : Finset Point)
    (i : Fin (canonicalInteriorCount R S A)) :
    (3 : ℝ)/16 < (rectangleDual (R+1) (S+1)).avoidanceRatio
      (InteriorAvoidance.interiorHighLabels R S A i) := by
  let d := InteriorAvoidance.interiorExtremalPairs R S A i
  have hxpos : 0 < (boundedDualCoreCoord (canonicalInteriorPrimal R S A i) d.high).1 := by
    by_contra hno
    have hz := Nat.eq_zero_of_not_pos hno
    have ha := (d.high_neighbors d.west).mpr (Or.inl rfl)
    apply ha.ne
    apply (boundedDualCoreCoord (canonicalInteriorPrimal R S A i)).injective
    rw [d.west_coord]
    exact Prod.ext (by simp [hz]) rfl
  have hypos : 0 < (boundedDualCoreCoord (canonicalInteriorPrimal R S A i) d.high).2 := by
    by_contra hno
    have hz := Nat.eq_zero_of_not_pos hno
    have ha := (d.high_neighbors d.south).mpr (Or.inr rfl)
    apply ha.ne
    apply (boundedDualCoreCoord (canonicalInteriorPrimal R S A i)).injective
    rw [d.south_coord]
    exact Prod.ext rfl (by simp [hz])
  have hq : boundedFaceCoord d.high.1 = (d.west.1.1.val+1,d.west.1.2.val) := by
    have hx := congrArg Prod.fst d.west_coord
    have hy := congrArg Prod.snd d.west_coord
    apply Prod.ext
    · dsimp [boundedDualCoreCoord,boundedFaceCoord] at hx hxpos ⊢
      omega
    · exact hy.symm
  have ht : boundedFaceCoord d.high.1 = (d.south.1.1.val,d.south.1.2.val+1) := by
    have hx := congrArg Prod.fst d.south_coord
    have hy := congrArg Prod.snd d.south_coord
    apply Prod.ext
    · exact hx.symm
    · dsimp [boundedDualCoreCoord,boundedFaceCoord] at hy hypos ⊢
      omega
  obtain ⟨e,f,hset,he,hf⟩ := InteriorAvoidance.interiorHighLabels_presentation R S A i
  rw [hset]
  exact southWest_avoidance_gt d.high.1 d.west.1 d.south.1 hq ht e f he hf

end
end SpanningTreeIsoperimetry.WiredPairs
