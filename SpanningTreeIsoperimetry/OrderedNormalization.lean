module

public import SpanningTreeIsoperimetry.LatticeCongruence
public import SpanningTreeIsoperimetry.Isoperimetry

@[expose] public section

/-! Every actual maximizer admits an ordered origin-based minimal hull.
Translations and coordinate exchange preserve the literal congruence relation. -/
namespace SpanningTreeIsoperimetry.OrderedNormalization
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem standardHull_of_foundation {A : Domain} {r s : ℕ}
    (h : SquareMaximality.IsRectHull A 0 0 r s) : IsStandardHull A r s := by
  rcases h with ⟨hr,hs,hsub,hl,hrr,hb,ht⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [rectangle_eq_foundation] using hsub
  · obtain ⟨p,hp,hx⟩ := hl
    refine ⟨p.2,?_⟩
    simpa only [← hx,Prod.mk.eta] using hp
  · obtain ⟨p,hp,hx⟩ := hrr
    simp only [zero_add] at hx
    refine ⟨p.2,?_⟩
    simpa only [← hx,Prod.mk.eta] using hp
  · obtain ⟨p,hp,hy⟩ := hb
    refine ⟨p.1,?_⟩
    simpa only [← hy,Prod.mk.eta] using hp
  · obtain ⟨p,hp,hy⟩ := ht
    simp only [zero_add] at hy
    refine ⟨p.1,?_⟩
    simpa only [← hy,Prod.mk.eta] using hp

theorem standardHull_transpose {A : Domain} {r s : ℕ} (h : IsStandardHull A r s) :
    IsStandardHull (transposeDomain A) s r := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro p hp
    have hb := mem_rectangle.mp (h.subset (mem_transposeDomain.mp hp))
    rw [mem_rectangle]
    exact ⟨hb.2.2.1,hb.2.2.2,hb.1,hb.2.1⟩
  · obtain ⟨x,hx⟩ := h.bottom
    exact ⟨x,mem_transposeDomain.mpr hx⟩
  · obtain ⟨x,hx⟩ := h.top
    exact ⟨x,mem_transposeDomain.mpr hx⟩
  · obtain ⟨y,hy⟩ := h.left
    exact ⟨y,mem_transposeDomain.mpr hy⟩
  · obtain ⟨y,hy⟩ := h.right
    exact ⟨y,mem_transposeDomain.mpr hy⟩

theorem translate_congruent (A : Domain) (a b : ℤ) :
    Congruent A (SquareMaximality.translateFinset a b A) := by
  refine ⟨(a,b),false,1,1,Or.inl rfl,Or.inl rfl,?_⟩
  have he : rigidMotion (a,b) false 1 1=SquareMaximality.pointTranslation a b := by
    funext p
    simp [rigidMotion,SquareMaximality.pointTranslation,add_comm]
  rw [he,SquareMaximality.translateFinset,Finset.map_eq_image]
  rfl

theorem transpose_congruent (A : Domain) : Congruent A (transposeDomain A) := by
  refine ⟨(0,0),true,1,1,Or.inl rfl,Or.inl rfl,?_⟩
  have he : rigidMotion (0,0) true 1 1=Prod.swap := by funext ⟨x,y⟩; simp [rigidMotion]
  rw [he]
  rfl

theorem exists_ordered_standard_maximizer {A : Domain} (hmax : IsMaximizer A) :
    ∃ B : Domain, ∃ R S : ℕ, Congruent A B ∧ IsMaximizer B ∧
      IsStandardHull B (R+1) (S+1) ∧ R≤S := by
  obtain ⟨a,b,r,s,hh⟩ := SquareMaximality.exists_isRectHull_of_nonempty A
    (connected_domain_nonempty hmax.1)
  obtain ⟨R,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh.1.ne'
  obtain ⟨S,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hh.2.1.ne'
  let B := SquareMaximality.translateFinset (-a) (-b) A
  have hc : Congruent A B := translate_congruent A (-a) (-b)
  have hs : IsStandardHull B (R+1) (S+1) := standardHull_of_foundation hh.translate_to_origin
  by_cases hRS : R≤S
  · exact ⟨B,R,S,hc,hc.isMaximizer_iff.mp hmax,hs,hRS⟩
  · have hct := hc.trans (transpose_congruent B)
    exact ⟨transposeDomain B,S,R,hct,hct.isMaximizer_iff.mp hmax,standardHull_transpose hs,by omega⟩

end
end SpanningTreeIsoperimetry.OrderedNormalization
