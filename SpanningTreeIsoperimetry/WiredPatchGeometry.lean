module

public import SpanningTreeIsoperimetry.WiredRayleigh
public import SpanningTreeIsoperimetry.FreePatchBridge

@[expose] public section

/-! Exact clipping of a translated free patch into the wired rectangle.
Every surviving source edge retains a distinct target label, including
parallel edges incident with the exterior vertex. -/
namespace SpanningTreeIsoperimetry.WiredPatchGeometry

open SquareMaximality.Dual SquareMaximality.Multigraph
open WiredRayleigh

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def Inside (R S : ℕ) (x y : ℤ) : Prop := 0≤x ∧ x<R ∧ 0≤y ∧ y<S
instance (R S : ℕ) (x y : ℤ) : Decidable (Inside R S x y) :=
  inferInstanceAs (Decidable (0≤x ∧ x<R ∧ 0≤y ∧ y<S))

def clip (R S : ℕ) (x y : ℤ) : RectangleDualVertex (R+1) (S+1) :=
  if h : Inside R S x y then
    some (⟨x.toNat,by have := h.2.1; have := h.1; omega⟩,
      ⟨y.toNat,by have := h.2.2.2; have := h.2.2.1; omega⟩)
  else none

theorem clip_ne_none_iff (R S : ℕ) (x y : ℤ) :
    clip R S x y ≠ none ↔ Inside R S x y := by
  unfold clip
  split_ifs <;> simp_all

theorem horizontal_active_bounds {R S : ℕ} {x y : ℤ}
    (hne : clip R S x y ≠ clip R S (x+1) y) :
    0≤x+1 ∧ x+1≤R ∧ 0≤y ∧ y<S := by
  by_cases hx : Inside R S x y
  · unfold Inside at hx
    omega
  · have hr : Inside R S (x+1) y := by
      apply (clip_ne_none_iff R S (x+1) y).mp
      intro hr
      apply hne
      simpa [clip,hx] using hr.symm
    unfold Inside at hr
    omega

theorem vertical_active_bounds {R S : ℕ} {x y : ℤ}
    (hne : clip R S x y ≠ clip R S x (y+1)) :
    0≤x ∧ x<R ∧ 0≤y+1 ∧ y+1≤S := by
  by_cases hy : Inside R S x y
  · unfold Inside at hy
    omega
  · have hr : Inside R S x (y+1) := by
      apply (clip_ne_none_iff R S x (y+1)).mp
      intro hr
      apply hne
      simpa [clip,hy] using hr.symm
    unfold Inside at hr
    omega

def vertexMap (R S : ℕ) (a b : ℤ) (p : Fin 5 × Fin 5) :
    RectangleDualVertex (R+1) (S+1) := clip R S (a+p.1) (b+p.2)

theorem horizontal_source_active {R S : ℕ} {a b : ℤ} (e : HorizontalEdge 5 5)
    (h : ¬(Sym2.map (vertexMap R S a b)
      ((rectanglePrimal 5 5).ends (.horizontal e))).IsDiag) :
    0≤a+e.x+1 ∧ a+e.x+1≤R ∧ 0≤b+e.y ∧ b+e.y<S := by
  have hn : clip R S (a+e.x) (b+e.y) ≠ clip R S (a+e.x+1) (b+e.y) := by
    simpa [rectanglePrimal,vertexMap,horizontalPrimalLeft,horizontalPrimalRight,
      Nat.cast_add,add_assoc] using h
  exact horizontal_active_bounds hn

theorem vertical_source_active {R S : ℕ} {a b : ℤ} (e : VerticalEdge 5 5)
    (h : ¬(Sym2.map (vertexMap R S a b)
      ((rectanglePrimal 5 5).ends (.vertical e))).IsDiag) :
    0≤a+e.x ∧ a+e.x<R ∧ 0≤b+e.y+1 ∧ b+e.y+1≤S := by
  have hn : clip R S (a+e.x) (b+e.y) ≠ clip R S (a+e.x) (b+e.y+1) := by
    simpa [rectanglePrimal,vertexMap,verticalPrimalBottom,verticalPrimalTop,
      Nat.cast_add,add_assoc] using h
  exact vertical_active_bounds hn

def activeEdgeMap (R S : ℕ) (a b : ℤ)
    (e : {e : RectangleEdge 5 5 //
      ¬(Sym2.map (vertexMap R S a b) ((rectanglePrimal 5 5).ends e)).IsDiag}) :
    RectangleEdge (R+1) (S+1) :=
  match e with
  | ⟨.horizontal q,hq⟩ =>
    let h := horizontal_source_active q hq
    .vertical ⟨⟨(a+q.x+1).toNat,by omega⟩,⟨(b+q.y).toNat,by omega⟩⟩
  | ⟨.vertical q,hq⟩ =>
    let h := vertical_source_active q hq
    .horizontal ⟨⟨(a+q.x).toNat,by omega⟩,⟨(b+q.y+1).toNat,by omega⟩⟩

theorem verticalLeft_eq_clip {R S : ℕ} {x y : ℤ}
    (hx : 0≤x+1 ∧ x+1≤R) (hy : 0≤y ∧ y<S) :
    verticalLeft (r:=R+1) (s:=S+1)
      ⟨⟨(x+1).toNat,by omega⟩,⟨y.toNat,by omega⟩⟩ = clip R S x y := by
  unfold verticalLeft clip Inside
  split_ifs <;> simp_all
  all_goals try omega
  all_goals congr 1 <;> ext <;> simp_all <;> omega

theorem verticalRight_eq_clip {R S : ℕ} {x y : ℤ}
    (hx : 0≤x ∧ x≤R) (hy : 0≤y ∧ y<S) :
    verticalRight (r:=R+1) (s:=S+1)
      ⟨⟨x.toNat,by omega⟩,⟨y.toNat,by omega⟩⟩ = clip R S x y := by
  unfold verticalRight clip Inside
  split_ifs <;> simp_all
  all_goals try omega
  all_goals congr 1 <;> ext <;> simp_all <;> omega

theorem horizontalBelow_eq_clip {R S : ℕ} {x y : ℤ}
    (hx : 0≤x ∧ x<R) (hy : 0≤y+1 ∧ y+1≤S) :
    horizontalBelow (r:=R+1) (s:=S+1)
      ⟨⟨x.toNat,by omega⟩,⟨(y+1).toNat,by omega⟩⟩ = clip R S x y := by
  unfold horizontalBelow clip Inside
  split_ifs <;> simp_all
  all_goals try omega
  all_goals congr 1 <;> ext <;> simp_all <;> omega

theorem horizontalAbove_eq_clip {R S : ℕ} {x y : ℤ}
    (hx : 0≤x ∧ x<R) (hy : 0≤y ∧ y≤S) :
    horizontalAbove (r:=R+1) (s:=S+1)
      ⟨⟨x.toNat,by omega⟩,⟨y.toNat,by omega⟩⟩ = clip R S x y := by
  unfold horizontalAbove clip Inside
  split_ifs <;> simp_all
  all_goals try omega
  all_goals congr 1 <;> ext <;> simp_all <;> omega

theorem activeEdgeMap_ends (R S : ℕ) (a b : ℤ)
    (e : {e : RectangleEdge 5 5 //
      ¬(Sym2.map (vertexMap R S a b) ((rectanglePrimal 5 5).ends e)).IsDiag}) :
    (rectangleDual (R+1) (S+1)).ends (activeEdgeMap R S a b e) =
      Sym2.map (vertexMap R S a b) ((rectanglePrimal 5 5).ends e.val) := by
  obtain ⟨e,he⟩ := e
  cases e with
  | horizontal q =>
    have h := horizontal_source_active q he
    simp only [activeEdgeMap,rectangleDual_vertical_ends]
    rw [verticalLeft_eq_clip ⟨h.1,h.2.1⟩ ⟨h.2.2.1,h.2.2.2⟩,
      verticalRight_eq_clip ⟨h.1,h.2.1⟩ ⟨h.2.2.1,h.2.2.2⟩]
    simp [rectanglePrimal,vertexMap,horizontalPrimalLeft,horizontalPrimalRight,add_assoc]
  | vertical q =>
    have h := vertical_source_active q he
    simp only [activeEdgeMap,rectangleDual_horizontal_ends]
    rw [horizontalBelow_eq_clip ⟨h.1,h.2.1⟩ ⟨h.2.2.1,h.2.2.2⟩,
      horizontalAbove_eq_clip ⟨h.1,h.2.1⟩ ⟨h.2.2.1,h.2.2.2⟩]
    simp [rectanglePrimal,vertexMap,verticalPrimalBottom,verticalPrimalTop,add_assoc]

theorem activeEdgeMap_injective (R S : ℕ) (a b : ℤ) :
    Function.Injective (activeEdgeMap R S a b) := by
  rintro ⟨e,he⟩ ⟨f,hf⟩ hmap
  apply Subtype.ext
  cases e with
  | horizontal q =>
    cases f with
    | horizontal t =>
      have hq := horizontal_source_active q he
      have ht := horizontal_source_active t hf
      have hp := RectangleEdge.vertical.inj hmap
      have hx := congrArg (fun z : VerticalEdge (R+1) (S+1) => z.x.val) hp
      have hy := congrArg (fun z : VerticalEdge (R+1) (S+1) => z.y.val) hp
      simp only [activeEdgeMap] at hx hy
      have hqx : q.x=t.x := Fin.ext (by omega)
      have hqy : q.y=t.y := Fin.ext (by omega)
      cases q
      cases t
      simp_all
    | vertical t => cases hmap
  | vertical q =>
    cases f with
    | horizontal t => cases hmap
    | vertical t =>
      have hq := vertical_source_active q he
      have ht := vertical_source_active t hf
      have hp := RectangleEdge.horizontal.inj hmap
      have hx := congrArg (fun z : HorizontalEdge (R+1) (S+1) => z.x.val) hp
      have hy := congrArg (fun z : HorizontalEdge (R+1) (S+1) => z.y.val) hp
      simp only [activeEdgeMap] at hx hy
      have hqx : q.x=t.x := Fin.ext (by omega)
      have hqy : q.y=t.y := Fin.ext (by omega)
      cases q
      cases t
      simp_all

def clippingWiring (R S : ℕ) (a b : ℤ) :
    Wiring (rectanglePrimal 5 5) (rectangleDual (R+1) (S+1)) where
  vertexMap := vertexMap R S a b
  edgeMap := ⟨activeEdgeMap R S a b,activeEdgeMap_injective R S a b⟩
  map_ends := activeEdgeMap_ends R S a b

end SpanningTreeIsoperimetry.WiredPatchGeometry
