module

public import SpanningTreeIsoperimetry.BoundaryGreenBounds

@[expose] public section

/-! A union bound for actual finite Green matrices, proved at each walk length.
It supplies the two-boundary loss comparison before taking infinite limits. -/
namespace SpanningTreeIsoperimetry.GreenUnionBound
open Ferrers CornerEnergy FaceWalkWords BoundaryGreenLoss
open SquareMaximality.Boundary SquareMaximality.ClosedWalk
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def stays {n : ℕ} (U : Diagram) (p : Ferrers.Point) (ω : SquareMaximality.ClosedWalk.Word n) : Prop :=
  ∀ t≤n, ∃ x∈U, latticePointToPoint x=latticePointToPoint p+position ω t

theorem stays_subtype_iff {n : ℕ} {U : Diagram} {p : Ferrers.Point} (hp : p∈U)
    (ω : SquareMaximality.ClosedWalk.Word n) : StaysIn U ⟨p,hp⟩ ω ↔ stays U p ω := by
  constructor
  · intro h t ht
    obtain ⟨x,hx⟩ := h t ht
    exact ⟨x.val,x.property,hx⟩
  · intro h t ht
    obtain ⟨x,hx,he⟩ := h t ht
    exact ⟨⟨x,hx⟩,he⟩

theorem stays_mono {n : ℕ} {U V : Diagram} (hUV : U⊆V) (p : Ferrers.Point)
    (ω : SquareMaximality.ClosedWalk.Word n) (h : stays U p ω) : stays V p ω := by
  intro t ht
  obtain ⟨x,hx,he⟩ := h t ht
  exact ⟨x,hUV hx,he⟩

theorem stays_inter {n : ℕ} (U V : Diagram) (p : Ferrers.Point)
    (ω : SquareMaximality.ClosedWalk.Word n) :
    stays (U∩V) p ω ↔ stays U p ω ∧ stays V p ω := by
  constructor
  · intro h
    exact ⟨stays_mono Finset.inter_subset_left p ω h,
      stays_mono Finset.inter_subset_right p ω h⟩
  · rintro ⟨hU,hV⟩ t ht
    obtain ⟨x,hx,he⟩ := hU t ht
    obtain ⟨y,hy,hye⟩ := hV t ht
    have hxy : x=y := latticePointToPoint_injective (he.trans hye.symm)
    exact ⟨x,Finset.mem_inter.mpr ⟨hx,hxy.symm ▸ hy⟩,he⟩

def words (U : Diagram) (p q : Ferrers.Point) (n : ℕ) :
    Finset (SquareMaximality.ClosedWalk.Word n) :=
  Finset.univ.filter (fun ω => total ω=latticePointToPoint q-latticePointToPoint p ∧ stays U p ω)

theorem mem_words {n : ℕ} (U : Diagram) (p q : Ferrers.Point)
    (ω : SquareMaximality.ClosedWalk.Word n) :
    ω∈words U p q n ↔ total ω=latticePointToPoint q-latticePointToPoint p ∧ stays U p ω := by
  simp only [words,Finset.mem_filter,Finset.mem_univ,true_and]

theorem words_mono {U V : Diagram} (hUV : U⊆V) (p q : Ferrers.Point) (n : ℕ) :
    words U p q n⊆words V p q n := by
  intro ω hω
  rw [mem_words] at hω ⊢
  exact ⟨hω.1,stays_mono hUV p ω hω.2⟩

theorem words_inter (U V : Diagram) (p q : Ferrers.Point) (n : ℕ) :
    words (U∩V) p q n=words U p q n∩words V p q n := by
  ext ω
  simp only [mem_words,Finset.mem_inter,stays_inter]
  tauto

theorem word_count_union_bound {U V W : Diagram} (hUW : U⊆W) (hVW : V⊆W)
    (p q : Ferrers.Point) (n : ℕ) :
    (words U p q n).card+(words V p q n).card≤
      (words W p q n).card+(words (U∩V) p q n).card := by
  have hsub : words U p q n∪words V p q n⊆words W p q n :=
    Finset.union_subset (words_mono hUW p q n) (words_mono hVW p q n)
  have hc := Finset.card_le_card hsub
  have hi := Finset.card_union_add_card_inter (words U p q n) (words V p q n)
  rw [← words_inter U V p q n] at hi
  omega

def endpointWordsEquiv {U : Diagram} {p q : Ferrers.Point} (hp : p∈U) (hq : q∈U) (n : ℕ) :
    EndpointWord U ⟨p,hp⟩ ⟨q,hq⟩ n ≃ {ω // ω∈words U p q n} where
  toFun ω := ⟨ω.val,(mem_words U p q ω.val).mpr
    ⟨ω.property.1,(stays_subtype_iff hp ω.val).mp ω.property.2⟩⟩
  invFun ω := ⟨ω.val,((mem_words U p q ω.val).mp ω.property).1,
    (stays_subtype_iff hp ω.val).mpr ((mem_words U p q ω.val).mp ω.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem green_words_hasSum {R S : ℕ} {U : Diagram} (hU : U⊆faceRectangle R S)
    {p q : Ferrers.Point} (hp : p∈U) (hq : q∈U) :
    HasSum (fun n => ((words U p q n).card : ℝ)/4^(n+1)) (green U p q) := by
  have h := MatrixGreenSeries.face_inverse_walk_hasSum
    ((foundation_faceIndices R S).symm ▸ hU) ⟨p,hp⟩ ⟨q,hq⟩
  rw [← green_mem hp hq] at h
  refine h.congr_fun (fun n => ?_)
  rw [Fintype.card_congr (endpointWordEquiv U ⟨p,hp⟩ ⟨q,hq⟩ n),
    Fintype.card_congr (endpointWordsEquiv hp hq n),Fintype.card_coe]

theorem green_union_bound {R S : ℕ} {U V W : Diagram}
    (hW : W⊆faceRectangle R S) (hUW : U⊆W) (hVW : V⊆W)
    {p q : Ferrers.Point} (hp : p∈U∩V) (hq : q∈U∩V) :
    green U p q+green V p q≤green W p q+green (U∩V) p q := by
  have hpU := (Finset.mem_inter.mp hp).1
  have hpV := (Finset.mem_inter.mp hp).2
  have hqU := (Finset.mem_inter.mp hq).1
  have hqV := (Finset.mem_inter.mp hq).2
  have hleft := (green_words_hasSum (hUW.trans hW) hpU hqU).add
    (green_words_hasSum (hVW.trans hW) hpV hqV)
  have hright := (green_words_hasSum hW (hUW hpU) (hUW hqU)).add
    (green_words_hasSum (Finset.inter_subset_left.trans (hUW.trans hW)) hp hq)
  apply hasSum_le _ hleft hright
  intro n
  rw [← add_div,← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast word_count_union_bound hUW hVW p q n

end
end SpanningTreeIsoperimetry.GreenUnionBound
