import SquareMaximality.Multigraph.All

set_option autoImplicit false

/-!
# The edge-labelled geometric dual of a lattice rectangle

Each primal edge is retained as its own label.  The dual vertex type consists
of the bounded unit faces together with one exterior face.  Consequently the
construction retains the parallel boundary dual edges required by
`general.tex`; degenerate rectangles may also produce exterior loops.
-/

namespace SquareMaximality

namespace Dual

open Multigraph

/-- A bounded unit face of an `r × s` vertex rectangle. -/
abbrev BoundedFace (r s : ℕ) := Fin (r - 1) × Fin (s - 1)

/-- Bounded faces plus the exterior face (`none`). -/
abbrev RectangleDualVertex (r s : ℕ) := Option (BoundedFace r s)

/-- A horizontal primal edge, indexed by its left endpoint. -/
structure HorizontalEdge (r s : ℕ) where
  x : Fin (r - 1)
  y : Fin s
deriving DecidableEq

def horizontalEdgeEquiv (r s : ℕ) :
    (Fin (r - 1) × Fin s) ≃ HorizontalEdge r s where
  toFun e := ⟨e.1, e.2⟩
  invFun e := (e.x, e.y)
  left_inv _ := rfl
  right_inv _ := rfl

instance (r s : ℕ) : Fintype (HorizontalEdge r s) :=
  Fintype.ofEquiv (Fin (r - 1) × Fin s) (horizontalEdgeEquiv r s)

/-- A vertical primal edge, indexed by its bottom endpoint. -/
structure VerticalEdge (r s : ℕ) where
  x : Fin r
  y : Fin (s - 1)
deriving DecidableEq

def verticalEdgeEquiv (r s : ℕ) :
    (Fin r × Fin (s - 1)) ≃ VerticalEdge r s where
  toFun e := ⟨e.1, e.2⟩
  invFun e := (e.x, e.y)
  left_inv _ := rfl
  right_inv _ := rfl

instance (r s : ℕ) : Fintype (VerticalEdge r s) :=
  Fintype.ofEquiv (Fin r × Fin (s - 1)) (verticalEdgeEquiv r s)

/-- All labelled primal edges; these become the edge labels of the dual. -/
inductive RectangleEdge (r s : ℕ)
  | horizontal : HorizontalEdge r s → RectangleEdge r s
  | vertical : VerticalEdge r s → RectangleEdge r s
deriving DecidableEq

def rectangleEdgeEquiv (r s : ℕ) :
    HorizontalEdge r s ⊕ VerticalEdge r s ≃ RectangleEdge r s where
  toFun
    | .inl e => .horizontal e
    | .inr e => .vertical e
  invFun
    | .horizontal e => .inl e
    | .vertical e => .inr e
  left_inv e := by cases e <;> rfl
  right_inv e := by cases e <;> rfl

instance (r s : ℕ) : Fintype (RectangleEdge r s) :=
  Fintype.ofEquiv (HorizontalEdge r s ⊕ VerticalEdge r s) (rectangleEdgeEquiv r s)

/-- Left endpoint of a horizontal primal edge. -/
def horizontalPrimalLeft {r s : ℕ} (e : HorizontalEdge r s) : Fin r × Fin s :=
  (⟨e.x.1, by have := e.x.2; omega⟩, e.y)

/-- Right endpoint of a horizontal primal edge. -/
def horizontalPrimalRight {r s : ℕ} (e : HorizontalEdge r s) : Fin r × Fin s :=
  (⟨e.x.1 + 1, by have := e.x.2; omega⟩, e.y)

/-- Bottom endpoint of a vertical primal edge. -/
def verticalPrimalBottom {r s : ℕ} (e : VerticalEdge r s) : Fin r × Fin s :=
  (e.x, ⟨e.y.1, by have := e.y.2; omega⟩)

/-- Top endpoint of a vertical primal edge. -/
def verticalPrimalTop {r s : ℕ} (e : VerticalEdge r s) : Fin r × Fin s :=
  (e.x, ⟨e.y.1 + 1, by have := e.y.2; omega⟩)

/-- The labelled primal rectangular grid using the same label type as its dual. -/
def rectanglePrimal (r s : ℕ) :
    LabeledMultigraph (Fin r × Fin s) (RectangleEdge r s) where
  ends
    | .horizontal e => s(horizontalPrimalLeft e, horizontalPrimalRight e)
    | .vertical e => s(verticalPrimalBottom e, verticalPrimalTop e)

/-- Forgetting edge labels recovers the usual box product of two paths. -/
theorem rectanglePrimal_toSimpleGraph (r s : ℕ) :
    (rectanglePrimal r s).toSimpleGraph =
      SimpleGraph.pathGraph r □ SimpleGraph.pathGraph s := by
  ext p q
  constructor
  · rintro ⟨_hpq, e, he⟩
    cases e with
    | horizontal e =>
        change s(horizontalPrimalLeft e, horizontalPrimalRight e) = s(p, q) at he
        rcases Sym2.eq_iff.mp he with he | he
        · rcases he with ⟨rfl, rfl⟩
          exact Or.inl ⟨SimpleGraph.pathGraph_adj.mpr (Or.inl rfl), rfl⟩
        · rcases he with ⟨rfl, rfl⟩
          exact Or.inl ⟨SimpleGraph.pathGraph_adj.mpr (Or.inr rfl), rfl⟩
    | vertical e =>
        change s(verticalPrimalBottom e, verticalPrimalTop e) = s(p, q) at he
        rcases Sym2.eq_iff.mp he with he | he
        · rcases he with ⟨rfl, rfl⟩
          exact Or.inr ⟨SimpleGraph.pathGraph_adj.mpr (Or.inl rfl), rfl⟩
        · rcases he with ⟨rfl, rfl⟩
          exact Or.inr ⟨SimpleGraph.pathGraph_adj.mpr (Or.inr rfl), rfl⟩
  · intro hpq
    have hpqne : p ≠ q := hpq.ne
    refine ⟨hpqne, ?_⟩
    rcases hpq with hpq | hpq
    · rcases hpq with ⟨horiz, hsecond⟩
      rcases SimpleGraph.pathGraph_adj.mp horiz with hright | hleft
      · let e : HorizontalEdge r s :=
          ⟨⟨p.1.1, by have := q.1.2; omega⟩, p.2⟩
        refine ⟨.horizontal e, ?_⟩
        change s(horizontalPrimalLeft e, horizontalPrimalRight e) = s(p, q)
        have hpLeft : horizontalPrimalLeft e = p := by
          apply Prod.ext
          · apply Fin.ext
            rfl
          · rfl
        have hqRight : horizontalPrimalRight e = q := by
          apply Prod.ext
          · apply Fin.ext
            exact hright
          · exact hsecond
        rw [hpLeft, hqRight]
      · let e : HorizontalEdge r s :=
          ⟨⟨q.1.1, by have := p.1.2; omega⟩, q.2⟩
        refine ⟨.horizontal e, ?_⟩
        change s(horizontalPrimalLeft e, horizontalPrimalRight e) = s(p, q)
        have hqLeft : horizontalPrimalLeft e = q := by
          apply Prod.ext
          · apply Fin.ext
            rfl
          · rfl
        have hpRight : horizontalPrimalRight e = p := by
          apply Prod.ext
          · apply Fin.ext
            exact hleft
          · exact hsecond.symm
        rw [hqLeft, hpRight, Sym2.eq_swap]
    · rcases hpq with ⟨vert, hfirst⟩
      rcases SimpleGraph.pathGraph_adj.mp vert with hup | hdown
      · let e : VerticalEdge r s :=
          ⟨p.1, ⟨p.2.1, by have := q.2.2; omega⟩⟩
        refine ⟨.vertical e, ?_⟩
        change s(verticalPrimalBottom e, verticalPrimalTop e) = s(p, q)
        have hpBottom : verticalPrimalBottom e = p := by
          apply Prod.ext
          · rfl
          · apply Fin.ext
            rfl
        have hqTop : verticalPrimalTop e = q := by
          apply Prod.ext
          · exact hfirst
          · apply Fin.ext
            exact hup
        rw [hpBottom, hqTop]
      · let e : VerticalEdge r s :=
          ⟨q.1, ⟨q.2.1, by have := p.2.2; omega⟩⟩
        refine ⟨.vertical e, ?_⟩
        change s(verticalPrimalBottom e, verticalPrimalTop e) = s(p, q)
        have hqBottom : verticalPrimalBottom e = q := by
          apply Prod.ext
          · rfl
          · apply Fin.ext
            rfl
        have hpTop : verticalPrimalTop e = p := by
          apply Prod.ext
          · exact hfirst.symm
          · apply Fin.ext
            exact hdown
        rw [hqBottom, hpTop, Sym2.eq_swap]

/-- Positive rectangular primal grids are connected. -/
theorem rectanglePrimal_connected
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s) :
    (rectanglePrimal r s).Connected := by
  rw [LabeledMultigraph.connected_iff_toSimpleGraph_connected,
    rectanglePrimal_toSimpleGraph]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  exact (SimpleGraph.pathGraph_connected r).boxProd
    (SimpleGraph.pathGraph_connected s)

/-- The bounded face immediately below a horizontal edge, if one exists. -/
def horizontalBelow {r s : ℕ} (e : HorizontalEdge r s) : RectangleDualVertex r s :=
  if hy : e.y.1 = 0 then none
  else some (e.x, ⟨e.y.1 - 1, by
    have hypos : 0 < e.y.1 := Nat.pos_of_ne_zero hy
    have hys := e.y.2
    omega⟩)

/-- The bounded face immediately above a horizontal edge, if one exists. -/
def horizontalAbove {r s : ℕ} (e : HorizontalEdge r s) : RectangleDualVertex r s :=
  if hy : e.y.1 + 1 < s then
    some (e.x, ⟨e.y.1, by omega⟩)
  else none

/-- The bounded face immediately left of a vertical edge, if one exists. -/
def verticalLeft {r s : ℕ} (e : VerticalEdge r s) : RectangleDualVertex r s :=
  if hx : e.x.1 = 0 then none
  else some (⟨e.x.1 - 1, by
    have hxpos : 0 < e.x.1 := Nat.pos_of_ne_zero hx
    have hxr := e.x.2
    omega⟩, e.y)

/-- The bounded face immediately right of a vertical edge, if one exists. -/
def verticalRight {r s : ℕ} (e : VerticalEdge r s) : RectangleDualVertex r s :=
  if hx : e.x.1 + 1 < r then
    some (⟨e.x.1, by omega⟩, e.y)
  else none

/-- The geometric dual, including its exterior vertex. -/
def rectangleDual (r s : ℕ) :
    LabeledMultigraph (RectangleDualVertex r s) (RectangleEdge r s) where
  ends
    | .horizontal e => s(horizontalBelow e, horizontalAbove e)
    | .vertical e => s(verticalLeft e, verticalRight e)

@[simp] theorem rectangleDual_horizontal_ends {r s : ℕ} (e : HorizontalEdge r s) :
    (rectangleDual r s).ends (.horizontal e) =
      s(horizontalBelow e, horizontalAbove e) :=
  rfl

@[simp] theorem rectangleDual_vertical_ends {r s : ℕ} (e : VerticalEdge r s) :
    (rectangleDual r s).ends (.vertical e) =
      s(verticalLeft e, verticalRight e) :=
  rfl

@[simp] theorem card_boundedFace (r s : ℕ) :
    Fintype.card (BoundedFace r s) = (r - 1) * (s - 1) := by
  simp [BoundedFace]

@[simp] theorem card_rectangleDualVertex (r s : ℕ) :
    Fintype.card (RectangleDualVertex r s) = (r - 1) * (s - 1) + 1 := by
  simp [RectangleDualVertex]

@[simp] theorem card_horizontalEdge (r s : ℕ) :
    Fintype.card (HorizontalEdge r s) = (r - 1) * s := by
  rw [← Fintype.card_congr (horizontalEdgeEquiv r s)]
  simp

@[simp] theorem card_verticalEdge (r s : ℕ) :
    Fintype.card (VerticalEdge r s) = r * (s - 1) := by
  rw [← Fintype.card_congr (verticalEdgeEquiv r s)]
  simp

@[simp] theorem card_rectangleEdge (r s : ℕ) :
    Fintype.card (RectangleEdge r s) = (r - 1) * s + r * (s - 1) := by
  rw [← Fintype.card_congr (rectangleEdgeEquiv r s)]
  simp

/-- Bottom horizontal boundary edges meet the exterior face below. -/
@[simp] theorem horizontalBelow_eq_none_iff {r s : ℕ} (e : HorizontalEdge r s) :
    horizontalBelow e = none ↔ e.y.1 = 0 := by
  simp [horizontalBelow]

/-- Top horizontal boundary edges meet the exterior face above. -/
@[simp] theorem horizontalAbove_eq_none_iff {r s : ℕ} (e : HorizontalEdge r s) :
    horizontalAbove e = none ↔ ¬e.y.1 + 1 < s := by
  simp [horizontalAbove]

/-- Left vertical boundary edges meet the exterior face on the left. -/
@[simp] theorem verticalLeft_eq_none_iff {r s : ℕ} (e : VerticalEdge r s) :
    verticalLeft e = none ↔ e.x.1 = 0 := by
  simp [verticalLeft]

/-- Right vertical boundary edges meet the exterior face on the right. -/
@[simp] theorem verticalRight_eq_none_iff {r s : ℕ} (e : VerticalEdge r s) :
    verticalRight e = none ↔ ¬e.x.1 + 1 < r := by
  simp [verticalRight]

theorem horizontalBelow_ne_horizontalAbove
    {r s : ℕ} (hs : 2 ≤ s) (e : HorizontalEdge r s) :
    horizontalBelow e ≠ horizontalAbove e := by
  intro heq
  by_cases hy0 : e.y.1 = 0
  · have hytop : e.y.1 + 1 < s := by omega
    rw [horizontalBelow, dif_pos hy0, horizontalAbove, dif_pos hytop] at heq
    cases heq
  · by_cases hytop : e.y.1 + 1 < s
    · rw [horizontalBelow, dif_neg hy0, horizontalAbove, dif_pos hytop] at heq
      have hval := congrArg (fun o => o.map (fun p => p.2.1)) heq
      simp only [Option.map_some, Option.some.injEq] at hval
      have hypos : 0 < e.y.1 := Nat.pos_of_ne_zero hy0
      omega
    · rw [horizontalBelow, dif_neg hy0, horizontalAbove, dif_neg hytop] at heq
      cases heq

theorem verticalLeft_ne_verticalRight
    {r s : ℕ} (hr : 2 ≤ r) (e : VerticalEdge r s) :
    verticalLeft e ≠ verticalRight e := by
  intro heq
  by_cases hx0 : e.x.1 = 0
  · have hxtop : e.x.1 + 1 < r := by omega
    rw [verticalLeft, dif_pos hx0, verticalRight, dif_pos hxtop] at heq
    cases heq
  · by_cases hxtop : e.x.1 + 1 < r
    · rw [verticalLeft, dif_neg hx0, verticalRight, dif_pos hxtop] at heq
      have hval := congrArg (fun o => o.map (fun p => p.1.1)) heq
      simp only [Option.map_some, Option.some.injEq] at hval
      have hxpos : 0 < e.x.1 := Nat.pos_of_ne_zero hx0
      omega
    · rw [verticalLeft, dif_neg hx0, verticalRight, dif_neg hxtop] at heq
      cases heq

/-- Nondegenerate rectangular duals have no loops.  Parallel boundary labels
are still retained. -/
theorem rectangleDual_not_isLoop
    {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (e : RectangleEdge r s) :
    ¬(rectangleDual r s).IsLoop e := by
  cases e with
  | horizontal e =>
      apply (rectangleDual r s).not_isLoop_of_isLink_of_ne
        (u := horizontalBelow e) (v := horizontalAbove e)
      · rfl
      · exact horizontalBelow_ne_horizontalAbove hs e
  | vertical e =>
      apply (rectangleDual r s).not_isLoop_of_isLink_of_ne
        (u := verticalLeft e) (v := verticalRight e)
      · rfl
      · exact verticalLeft_ne_verticalRight hr e

/-- The bounded face in the bottom row with horizontal coordinate `x`. -/
def bottomFace {r s : ℕ} (hs : 2 ≤ s) (x : Fin (r - 1)) : BoundedFace r s :=
  (x, ⟨0, by omega⟩)

/-- The exterior face is adjacent to every bottom-row bounded face. -/
theorem rectangleDual_adj_exterior_bottom
    {r s : ℕ} (hs : 2 ≤ s) (x : Fin (r - 1)) :
    (rectangleDual r s).toSimpleGraph.Adj none (some (bottomFace hs x)) := by
  refine ⟨by simp, ?_⟩
  let e : HorizontalEdge r s := ⟨x, ⟨0, by omega⟩⟩
  refine ⟨.horizontal e, ?_⟩
  change (rectangleDual r s).ends (.horizontal e) = s(none, some (bottomFace hs x))
  have hs1 : 1 < s := by omega
  simp [e, rectangleDual, horizontalBelow, horizontalAbove, bottomFace, hs1]

/-- A bounded face at natural coordinates `(x,y)`. -/
def boundedFaceAt {r s : ℕ} (x : Fin (r - 1)) (y : ℕ) (hy : y < s - 1) :
    BoundedFace r s :=
  (x, ⟨y, hy⟩)

/-- Consecutive bounded faces in a column are dual-adjacent. -/
theorem rectangleDual_adj_face_succ
    {r s y : ℕ} (x : Fin (r - 1)) (hy : y + 1 < s - 1) :
    (rectangleDual r s).toSimpleGraph.Adj
      (some (boundedFaceAt x y (by omega)))
      (some (boundedFaceAt x (y + 1) hy)) := by
  refine ⟨?_, ?_⟩
  · intro h
    have hval := congrArg (fun o => o.map (fun p => p.2.1)) h
    simp [boundedFaceAt] at hval
  · let e : HorizontalEdge r s := ⟨x, ⟨y + 1, by omega⟩⟩
    refine ⟨.horizontal e, ?_⟩
    change (rectangleDual r s).ends (.horizontal e) =
      s(some (boundedFaceAt x y (by omega)), some (boundedFaceAt x (y + 1) hy))
    have hys : y + 1 + 1 < s := by omega
    simp [e, rectangleDual, horizontalBelow, horizontalAbove, boundedFaceAt, hys]

/-- Every bounded face reaches the exterior by moving down its column. -/
theorem rectangleDual_boundedFace_reachable_exterior
    {r s : ℕ} (hs : 2 ≤ s) (f : BoundedFace r s) :
    (rectangleDual r s).toSimpleGraph.Reachable (some f) none := by
  by_cases hzero : f.2.1 = 0
  · have hf : f = bottomFace hs f.1 := by
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simpa [bottomFace] using hzero
    rw [hf]
    exact (rectangleDual_adj_exterior_bottom hs f.1).reachable.symm
  · have hypos : 0 < f.2.1 := Nat.pos_of_ne_zero hzero
    let lower : BoundedFace r s :=
      (f.1, ⟨f.2.1 - 1, by have := f.2.2; omega⟩)
    have hstep : f.2.1 - 1 + 1 < s - 1 := by
      have := f.2.2
      omega
    have hadj := rectangleDual_adj_face_succ (r := r) (s := s)
      f.1 (y := f.2.1 - 1) hstep
    have hlower : boundedFaceAt f.1 (f.2.1 - 1) (by omega) = lower := by
      rfl
    have hupper : boundedFaceAt f.1 (f.2.1 - 1 + 1) hstep = f := by
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simp [boundedFaceAt]
        omega
    rw [hlower, hupper] at hadj
    exact hadj.reachable.symm.trans
      (rectangleDual_boundedFace_reachable_exterior hs lower)
termination_by f.2.1

/-- The explicit geometric dual of every nondegenerate rectangle is connected. -/
theorem rectangleDual_connected
    {r s : ℕ} (_hr : 2 ≤ r) (hs : 2 ≤ s) :
    (rectangleDual r s).Connected := by
  rw [LabeledMultigraph.connected_iff_toSimpleGraph_connected,
    SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨none, ?_⟩
  intro w
  cases w with
  | none => exact SimpleGraph.Reachable.refl none
  | some f => exact (rectangleDual_boundedFace_reachable_exterior hs f).symm

end Dual

end SquareMaximality
