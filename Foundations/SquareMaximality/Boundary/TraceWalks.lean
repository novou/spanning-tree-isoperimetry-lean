import SquareMaximality.Boundary.SeriesCharging

/-!
# The finite trace--walk bridge

This module proves the finite combinatorial identity behind
`general.tex`, equation `trace-walks`.  No determinant or infinite-series
argument is used here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SquareMaximality
namespace Boundary

open ClosedWalk

/-- Coerce a natural-coordinate lattice point to integer coordinates. -/
def latticePointToPoint (z : LatticePoint) : Point := (z.1, z.2)

theorem faceLattice_adj_iff_step (z w : LatticePoint) :
    faceLattice.Adj z w ↔
      latticePointToPoint w - latticePointToPoint z = Step.east.vector ∨
      latticePointToPoint w - latticePointToPoint z = Step.west.vector ∨
      latticePointToPoint w - latticePointToPoint z = Step.north.vector ∨
      latticePointToPoint w - latticePointToPoint z = Step.south.vector := by
  simp only [faceLattice, natManhattanDist, latticePointToPoint,
    Step.vector_east, Step.vector_west, Step.vector_north, Step.vector_south,
    Prod.mk_sub_mk, Prod.mk.injEq]
  unfold Nat.dist
  omega

theorem exists_step_of_faceLattice_adj (z w : LatticePoint)
    (h : faceLattice.Adj z w) :
    ∃ d : Step,
      latticePointToPoint w - latticePointToPoint z = d.vector := by
  rcases (faceLattice_adj_iff_step z w).mp h with h | h | h | h
  · exact ⟨.east, h⟩
  · exact ⟨.west, h⟩
  · exact ⟨.north, h⟩
  · exact ⟨.south, h⟩

/-- The unique square-lattice step from one adjacent natural lattice point
to the next. -/
noncomputable def stepOfAdjacent (z w : LatticePoint)
    (h : faceLattice.Adj z w) : Step :=
  Classical.choose (exists_step_of_faceLattice_adj z w h)

theorem stepOfAdjacent_vector (z w : LatticePoint)
    (h : faceLattice.Adj z w) :
    (stepOfAdjacent z w h).vector =
      latticePointToPoint w - latticePointToPoint z := by
  have hc := Classical.choose_spec (exists_step_of_faceLattice_adj z w h)
  exact hc.symm

/-- Read the successive directions of a finite face-graph walk. -/
noncomputable def wordOfFaceWalk {U : Finset LatticePoint}
    {z w : {p // p ∈ U}} (p : (faceGraph U).Walk z w) : Word p.length :=
  fun i => stepOfAdjacent (p.getVert i).1 (p.getVert (i.1 + 1)).1
    (p.adj_getVert_succ i.2)

theorem wordOfFaceWalk_vector {U : Finset LatticePoint}
    {z w : {p // p ∈ U}} (p : (faceGraph U).Walk z w)
    (i : Fin p.length) :
    (wordOfFaceWalk p i).vector =
      latticePointToPoint (p.getVert (i.1 + 1)).1 -
        latticePointToPoint (p.getVert i).1 := by
  exact stepOfAdjacent_vector _ _ _

theorem position_wordOfFaceWalk {U : Finset LatticePoint}
    {z w : {p // p ∈ U}} (p : (faceGraph U).Walk z w)
    {t : ℕ} (ht : t ≤ p.length) :
    position (wordOfFaceWalk p) t =
      latticePointToPoint (p.getVert t).1 - latticePointToPoint z.1 := by
  induction t with
  | zero => simp [latticePointToPoint]
  | succ t ih =>
      have hlt : t < p.length := by omega
      rw [position_succ (wordOfFaceWalk p) hlt, ih (by omega)]
      rw [wordOfFaceWalk_vector]
      abel

theorem isClosed_wordOfFaceWalk {U : Finset LatticePoint}
    {z : {p // p ∈ U}} (p : (faceGraph U).Walk z z) :
    IsClosed (wordOfFaceWalk p) := by
  change total (wordOfFaceWalk p) = (0, 0)
  rw [← position_length]
  rw [position_wordOfFaceWalk p (le_refl _), p.getVert_length]
  exact sub_self _

theorem position_mem_partialSums {n t : ℕ} (omega : Word n) (ht : t ≤ n) :
    position omega t ∈ partialSums omega := by
  exact Finset.mem_image.mpr ⟨t, by simp; omega, rfl⟩

theorem normalizedWalkPoint_toPoint {n : ℕ} (omega : Word n)
    {p : Point} (hp : p ∈ partialSums omega) :
    latticePointToPoint (normalizedWalkPoint omega p) =
      p - (walkMinX omega, walkMinY omega) := by
  have hpX : p.1 ∈ visitedX omega := Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hpY : p.2 ∈ visitedY omega := Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hx : walkMinX omega ≤ p.1 := Finset.min'_le _ _ hpX
  have hy : walkMinY omega ≤ p.2 := Finset.min'_le _ _ hpY
  apply Prod.ext
  · simp [latticePointToPoint, normalizedWalkPoint, Int.toNat_of_nonneg (sub_nonneg.mpr hx)]
  · simp [latticePointToPoint, normalizedWalkPoint, Int.toNat_of_nonneg (sub_nonneg.mpr hy)]

/-- The `t`-th vertex of the normalized word placed with lower-left corner
`(x,y)`. -/
def placedWalkVertex {n : ℕ} (omega : Word n) (x y t : ℕ) : LatticePoint :=
  let q := normalizedWalkPoint omega (position omega t)
  (x + q.1, y + q.2)

theorem placedWalkVertex_toPoint {n t : ℕ} (omega : Word n)
    (x y : ℕ) (ht : t ≤ n) :
    latticePointToPoint (placedWalkVertex omega x y t) =
      ((x : ℤ), (y : ℤ)) + position omega t -
        (walkMinX omega, walkMinY omega) := by
  have hp := normalizedWalkPoint_toPoint omega (position_mem_partialSums omega ht)
  calc
    latticePointToPoint (placedWalkVertex omega x y t) =
        ((x : ℤ), (y : ℤ)) +
          latticePointToPoint (normalizedWalkPoint omega (position omega t)) := by
      apply Prod.ext <;> simp [placedWalkVertex, latticePointToPoint]
    _ = ((x : ℤ), (y : ℤ)) + position omega t -
          (walkMinX omega, walkMinY omega) := by
      rw [hp]
      abel

theorem placedWalkVertex_step {n t : ℕ} (omega : Word n)
    (x y : ℕ) (ht : t < n) :
    latticePointToPoint (placedWalkVertex omega x y (t + 1)) -
        latticePointToPoint (placedWalkVertex omega x y t) =
      (omega ⟨t, ht⟩).vector := by
  rw [placedWalkVertex_toPoint omega x y (by omega),
    placedWalkVertex_toPoint omega x y (by omega),
    position_succ omega ht]
  abel

theorem placedWalkVertex_adj {n t : ℕ} (omega : Word n)
    (x y : ℕ) (ht : t < n) :
    faceLattice.Adj (placedWalkVertex omega x y t)
      (placedWalkVertex omega x y (t + 1)) := by
  rw [faceLattice_adj_iff_step]
  have hstep := placedWalkVertex_step omega x y ht
  cases h : omega ⟨t, ht⟩ <;> simp_all

theorem placedWalkVertex_mem_faceIndices {n t R S : ℕ} (omega : Word n)
    (x y : ℕ) (ht : t ≤ n)
    (hx : x + (spanX omega + 1) ≤ R)
    (hy : y + (spanY omega + 1) ≤ S) :
    placedWalkVertex omega x y t ∈ faceIndices R S := by
  rw [mem_faceIndices]
  have hp := position_mem_partialSums omega ht
  have hnx := normalizedWalkPoint_fst_le_spanX omega hp
  have hny := normalizedWalkPoint_snd_le_spanY omega hp
  simp only [placedWalkVertex]
  constructor <;> omega

theorem placedWalkVertex_length_eq_zero {n : ℕ} (omega : Word n)
    (x y : ℕ) (hclosed : IsClosed omega) :
    placedWalkVertex omega x y n = placedWalkVertex omega x y 0 := by
  simp only [placedWalkVertex, position_length, position_zero]
  rw [hclosed]

/-- A placed normalized word, viewed as a vertex of the full rectangular
face graph. -/
def placedFaceVertex {n R S : ℕ} (omega : Word n) (x y : ℕ)
    (hx : x + (spanX omega + 1) ≤ R)
    (hy : y + (spanY omega + 1) ≤ S) (t : Fin (n + 1)) :
    {p // p ∈ faceIndices R S} :=
  ⟨placedWalkVertex omega x y t.1,
    placedWalkVertex_mem_faceIndices omega x y (by omega) hx hy⟩

def placedFaceSupport {n R S : ℕ} (omega : Word n) (x y : ℕ)
    (hx : x + (spanX omega + 1) ≤ R)
    (hy : y + (spanY omega + 1) ≤ S) :
    List {p // p ∈ faceIndices R S} :=
  List.ofFn (placedFaceVertex omega x y hx hy)

theorem placedFaceSupport_ne_nil {n R S : ℕ} (omega : Word n) (x y : ℕ)
    (hx : x + (spanX omega + 1) ≤ R)
    (hy : y + (spanY omega + 1) ≤ S) :
    placedFaceSupport omega x y hx hy ≠ [] := by
  simp [placedFaceSupport]

theorem placedFaceSupport_isChain {n R S : ℕ} (omega : Word n) (x y : ℕ)
    (hx : x + (spanX omega + 1) ≤ R)
    (hy : y + (spanY omega + 1) ≤ S) :
    (placedFaceSupport omega x y hx hy).IsChain (faceGraph (faceIndices R S)).Adj := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hit : i < n := by
    simpa [placedFaceSupport] using hi
  unfold placedFaceSupport
  rw [List.getElem_ofFn, List.getElem_ofFn]
  exact placedWalkVertex_adj omega x y hit

/-- The rooted closed face walk represented by a normalized closed word and
one valid lower-left placement. -/
noncomputable def placedFaceWalk {n R S : ℕ} (omega : Word n) (x y : ℕ)
    (hx : x + (spanX omega + 1) ≤ R)
    (hy : y + (spanY omega + 1) ≤ S)
    (hclosed : IsClosed omega) :
    (faceGraph (faceIndices R S)).Walk
      (placedFaceVertex omega x y hx hy ⟨0, by omega⟩)
      (placedFaceVertex omega x y hx hy ⟨0, by omega⟩) := by
  let l := placedFaceSupport omega x y hx hy
  have hn : l ≠ [] := placedFaceSupport_ne_nil omega x y hx hy
  have hc : l.IsChain (faceGraph (faceIndices R S)).Adj :=
    placedFaceSupport_isChain omega x y hx hy
  let p := SimpleGraph.Walk.ofSupport l hn hc
  apply p.copy
  · simp [l, placedFaceSupport]
  · apply Subtype.ext
    simp only [l]
    rw [List.getLast_eq_getElem]
    simp only [placedFaceSupport, List.length_ofFn, Nat.add_sub_cancel,
      List.getElem_ofFn]
    simpa [placedFaceVertex] using
      placedWalkVertex_length_eq_zero omega x y hclosed

@[simp] theorem length_placedFaceWalk {n R S : ℕ} (omega : Word n) (x y : ℕ)
    (hx : x + (spanX omega + 1) ≤ R)
    (hy : y + (spanY omega + 1) ≤ S)
    (hclosed : IsClosed omega) :
    (placedFaceWalk omega x y hx hy hclosed).length = n := by
  simp [placedFaceWalk, placedFaceSupport]

@[simp] theorem support_placedFaceWalk {n R S : ℕ} (omega : Word n) (x y : ℕ)
    (hx : x + (spanX omega + 1) ≤ R)
    (hy : y + (spanY omega + 1) ≤ S)
    (hclosed : IsClosed omega) :
    (placedFaceWalk omega x y hx hy hclosed).support =
      placedFaceSupport omega x y hx hy := by
  simp [placedFaceWalk]

theorem exists_position_fst_eq_walkMinX {n : ℕ} (omega : Word n) :
    ∃ t ≤ n, (position omega t).1 = walkMinX omega := by
  have hm := Finset.min'_mem (visitedX omega) (visitedX_nonempty omega)
  rcases Finset.mem_image.mp hm with ⟨p, hp, hpx⟩
  rcases Finset.mem_image.mp hp with ⟨t, ht, htp⟩
  refine ⟨t, by simpa using ht, ?_⟩
  simpa [htp, walkMinX] using hpx

theorem exists_position_fst_eq_walkMaxX {n : ℕ} (omega : Word n) :
    ∃ t ≤ n, (position omega t).1 = walkMaxX omega := by
  have hm := Finset.max'_mem (visitedX omega) (visitedX_nonempty omega)
  rcases Finset.mem_image.mp hm with ⟨p, hp, hpx⟩
  rcases Finset.mem_image.mp hp with ⟨t, ht, htp⟩
  refine ⟨t, by simpa using ht, ?_⟩
  simpa [htp, walkMaxX] using hpx

theorem exists_position_snd_eq_walkMinY {n : ℕ} (omega : Word n) :
    ∃ t ≤ n, (position omega t).2 = walkMinY omega := by
  have hm := Finset.min'_mem (visitedY omega) (visitedY_nonempty omega)
  rcases Finset.mem_image.mp hm with ⟨p, hp, hpy⟩
  rcases Finset.mem_image.mp hp with ⟨t, ht, htp⟩
  refine ⟨t, by simpa using ht, ?_⟩
  simpa [htp, walkMinY] using hpy

theorem exists_position_snd_eq_walkMaxY {n : ℕ} (omega : Word n) :
    ∃ t ≤ n, (position omega t).2 = walkMaxY omega := by
  have hm := Finset.max'_mem (visitedY omega) (visitedY_nonempty omega)
  rcases Finset.mem_image.mp hm with ⟨p, hp, hpy⟩
  rcases Finset.mem_image.mp hp with ⟨t, ht, htp⟩
  refine ⟨t, by simpa using ht, ?_⟩
  simpa [htp, walkMaxY] using hpy

/-- Lower-left start recovered from a rooted face walk. -/
noncomputable def faceWalkStartX {U : Finset LatticePoint}
    {z : {p // p ∈ U}} (p : (faceGraph U).Walk z z) : ℕ :=
  ((z.1.1 : ℤ) + walkMinX (wordOfFaceWalk p)).toNat

noncomputable def faceWalkStartY {U : Finset LatticePoint}
    {z : {p // p ∈ U}} (p : (faceGraph U).Walk z z) : ℕ :=
  ((z.1.2 : ℤ) + walkMinY (wordOfFaceWalk p)).toNat

theorem faceWalk_lowerX_nonneg {R S : ℕ}
    {z : {q // q ∈ faceIndices R S}}
    (p : (faceGraph (faceIndices R S)).Walk z z) :
    0 ≤ (z.1.1 : ℤ) + walkMinX (wordOfFaceWalk p) := by
  rcases exists_position_fst_eq_walkMinX (wordOfFaceWalk p) with ⟨t, ht, hmin⟩
  have hpos := congrArg Prod.fst (position_wordOfFaceWalk p ht)
  have hv : 0 ≤ ((p.getVert t).1.1 : ℤ) := Int.natCast_nonneg _
  simp only [latticePointToPoint, Prod.fst_sub] at hpos
  omega

theorem faceWalk_lowerY_nonneg {R S : ℕ}
    {z : {q // q ∈ faceIndices R S}}
    (p : (faceGraph (faceIndices R S)).Walk z z) :
    0 ≤ (z.1.2 : ℤ) + walkMinY (wordOfFaceWalk p) := by
  rcases exists_position_snd_eq_walkMinY (wordOfFaceWalk p) with ⟨t, ht, hmin⟩
  have hpos := congrArg Prod.snd (position_wordOfFaceWalk p ht)
  have hv : 0 ≤ ((p.getVert t).1.2 : ℤ) := Int.natCast_nonneg _
  simp only [latticePointToPoint, Prod.snd_sub] at hpos
  omega

theorem faceWalkStartX_span_le {R S : ℕ}
    {z : {q // q ∈ faceIndices R S}}
    (p : (faceGraph (faceIndices R S)).Walk z z) :
    faceWalkStartX p + (spanX (wordOfFaceWalk p) + 1) ≤ R := by
  let omega := wordOfFaceWalk p
  rcases exists_position_fst_eq_walkMaxX omega with ⟨t, ht, hmax⟩
  have hpos := congrArg Prod.fst (position_wordOfFaceWalk p ht)
  have hv := (mem_faceIndices.mp (p.getVert t).2).1
  have hminmax := walkMinX_le_walkMaxX omega
  have hlower := faceWalk_lowerX_nonneg p
  have hdiff : 0 ≤ walkMaxX omega - walkMinX omega := sub_nonneg.mpr hminmax
  have hstartCast : ((faceWalkStartX p : ℕ) : ℤ) =
      (z.1.1 : ℤ) + walkMinX omega := by
    exact Int.toNat_of_nonneg hlower
  have hspanCast : ((spanX omega : ℕ) : ℤ) =
      walkMaxX omega - walkMinX omega := by
    exact Int.toNat_of_nonneg hdiff
  simp only [latticePointToPoint, Prod.fst_sub] at hpos
  dsimp only [omega] at *
  have hint : ((faceWalkStartX p : ℕ) : ℤ) +
      (spanX (wordOfFaceWalk p) : ℤ) + 1 ≤ (R : ℤ) := by
    rw [hstartCast, hspanCast]
    omega
  exact_mod_cast hint

theorem faceWalkStartY_span_le {R S : ℕ}
    {z : {q // q ∈ faceIndices R S}}
    (p : (faceGraph (faceIndices R S)).Walk z z) :
    faceWalkStartY p + (spanY (wordOfFaceWalk p) + 1) ≤ S := by
  let omega := wordOfFaceWalk p
  rcases exists_position_snd_eq_walkMaxY omega with ⟨t, ht, hmax⟩
  have hpos := congrArg Prod.snd (position_wordOfFaceWalk p ht)
  have hv := (mem_faceIndices.mp (p.getVert t).2).2
  have hminmax := walkMinY_le_walkMaxY omega
  have hlower := faceWalk_lowerY_nonneg p
  have hdiff : 0 ≤ walkMaxY omega - walkMinY omega := sub_nonneg.mpr hminmax
  have hstartCast : ((faceWalkStartY p : ℕ) : ℤ) =
      (z.1.2 : ℤ) + walkMinY omega := by
    exact Int.toNat_of_nonneg hlower
  have hspanCast : ((spanY omega : ℕ) : ℤ) =
      walkMaxY omega - walkMinY omega := by
    exact Int.toNat_of_nonneg hdiff
  simp only [latticePointToPoint, Prod.snd_sub] at hpos
  dsimp only [omega] at *
  have hint : ((faceWalkStartY p : ℕ) : ℤ) +
      (spanY (wordOfFaceWalk p) : ℤ) + 1 ≤ (S : ℤ) := by
    rw [hstartCast, hspanCast]
    omega
  exact_mod_cast hint

theorem latticePointToPoint_injective : Function.Injective latticePointToPoint := by
  intro z w h
  apply Prod.ext
  · have hx := congrArg Prod.fst h
    change (z.1 : ℤ) = (w.1 : ℤ) at hx
    exact_mod_cast hx
  · have hy := congrArg Prod.snd h
    change (z.2 : ℤ) = (w.2 : ℤ) at hy
    exact_mod_cast hy

/-- Normalizing the word extracted from a rectangular face walk and placing
it at its recovered lower-left start reconstructs every visited vertex. -/
theorem placedWalkVertex_wordOfFaceWalk {R S t : ℕ}
    {z : {q // q ∈ faceIndices R S}}
    (p : (faceGraph (faceIndices R S)).Walk z z) (ht : t ≤ p.length) :
    placedWalkVertex (wordOfFaceWalk p) (faceWalkStartX p)
        (faceWalkStartY p) t = (p.getVert t).1 := by
  apply latticePointToPoint_injective
  rw [placedWalkVertex_toPoint (wordOfFaceWalk p)
    (faceWalkStartX p) (faceWalkStartY p) ht]
  rw [position_wordOfFaceWalk p ht]
  have hx : ((faceWalkStartX p : ℕ) : ℤ) =
      (z.1.1 : ℤ) + walkMinX (wordOfFaceWalk p) := by
    exact Int.toNat_of_nonneg (faceWalk_lowerX_nonneg p)
  have hy : ((faceWalkStartY p : ℕ) : ℤ) =
      (z.1.2 : ℤ) + walkMinY (wordOfFaceWalk p) := by
    exact Int.toNat_of_nonneg (faceWalk_lowerY_nonneg p)
  apply Prod.ext
  · simp only [latticePointToPoint, Prod.fst_sub, Prod.fst_add]
    omega
  · simp only [latticePointToPoint, Prod.snd_sub, Prod.snd_add]
    omega

theorem Step.vector_injective : Function.Injective Step.vector := by
  intro d e h
  cases d <;> cases e <;> simp_all

theorem getVert_placedFaceWalk {n R S t : ℕ} (omega : Word n) (x y : ℕ)
    (hx : x + (spanX omega + 1) ≤ R)
    (hy : y + (spanY omega + 1) ≤ S)
    (hclosed : IsClosed omega) (ht : t ≤ n) :
    (placedFaceWalk omega x y hx hy hclosed).getVert t =
      placedFaceVertex omega x y hx hy ⟨t, by omega⟩ := by
  rw [SimpleGraph.Walk.getVert_eq_getD_support]
  rw [support_placedFaceWalk]
  unfold placedFaceSupport
  rw [List.getD_eq_getElem?_getD]
  rw [List.getElem?_ofFn, dif_pos (show t < n + 1 by omega)]
  rfl

/-- Extract a word of a prescribed length from a walk carrying a proof of
that length.  Defining this pointwise keeps later transports proof-irrelevant. -/
noncomputable def wordOfFaceWalkN {U : Finset LatticePoint} {n : ℕ}
    {z : {q // q ∈ U}} (p : (faceGraph U).Walk z z)
    (hlen : p.length = n) : Word n :=
  fun i => stepOfAdjacent (p.getVert i).1 (p.getVert (i.1 + 1)).1
    (p.adj_getVert_succ (by omega))

theorem wordOfFaceWalkN_vector {U : Finset LatticePoint} {n : ℕ}
    {z : {q // q ∈ U}} (p : (faceGraph U).Walk z z)
    (hlen : p.length = n) (i : Fin n) :
    (wordOfFaceWalkN p hlen i).vector =
      latticePointToPoint (p.getVert (i.1 + 1)).1 -
        latticePointToPoint (p.getVert i).1 := by
  exact stepOfAdjacent_vector _ _ _

theorem position_wordOfFaceWalkN {U : Finset LatticePoint} {n t : ℕ}
    {z : {q // q ∈ U}} (p : (faceGraph U).Walk z z)
    (hlen : p.length = n) (ht : t ≤ n) :
    position (wordOfFaceWalkN p hlen) t =
      latticePointToPoint (p.getVert t).1 - latticePointToPoint z.1 := by
  induction t with
  | zero => simp [latticePointToPoint]
  | succ t ih =>
      have hlt : t < n := by omega
      rw [position_succ (wordOfFaceWalkN p hlen) hlt, ih (by omega)]
      rw [wordOfFaceWalkN_vector]
      abel

theorem isClosed_wordOfFaceWalkN {U : Finset LatticePoint} {n : ℕ}
    {z : {q // q ∈ U}} (p : (faceGraph U).Walk z z)
    (hlen : p.length = n) : IsClosed (wordOfFaceWalkN p hlen) := by
  change total (wordOfFaceWalkN p hlen) = (0, 0)
  rw [← position_length, position_wordOfFaceWalkN p hlen (le_refl _)]
  rw [← hlen, p.getVert_length]
  exact sub_self _

theorem wordOfFaceWalkN_placedFaceWalk {n R S : ℕ} (omega : Word n)
    (x y : ℕ) (hx : x + (spanX omega + 1) ≤ R)
    (hy : y + (spanY omega + 1) ≤ S)
    (hclosed : IsClosed omega) :
    wordOfFaceWalkN (placedFaceWalk omega x y hx hy hclosed)
      (length_placedFaceWalk omega x y hx hy hclosed) = omega := by
  funext i
  apply Step.vector_injective
  rw [wordOfFaceWalkN_vector]
  rw [getVert_placedFaceWalk omega x y hx hy hclosed (by omega),
    getVert_placedFaceWalk omega x y hx hy hclosed (by omega)]
  exact placedWalkVertex_step omega x y i.2

theorem mem_placedPartialSums_iff_exists_position {n : ℕ} (omega : Word n)
    (x y : ℕ) (q : LatticePoint) :
    q ∈ placedPartialSums omega x y ↔
      ∃ t ≤ n, q = placedWalkVertex omega x y t := by
  constructor
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨u, hu, rfl⟩
    rcases Finset.mem_image.mp hu with ⟨p, hp, rfl⟩
    rcases Finset.mem_image.mp hp with ⟨t, ht, rfl⟩
    refine ⟨t, by simpa using ht, ?_⟩
    rfl
  · rintro ⟨t, ht, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨normalizedWalkPoint omega (position omega t), ?_, rfl⟩
    exact Finset.mem_image.mpr ⟨position omega t,
      position_mem_partialSums omega ht, rfl⟩

/-- Rooted closed walks of exactly `n` steps in an induced face graph. -/
def RootedFaceWalks (U : Finset LatticePoint) (n : ℕ) :=
  Σ z : {q // q ∈ U},
    {p : (faceGraph U).Walk z z // p.length = n}

/-- Rooted full-rectangle walks which visit at least one marked face. -/
def MarkedMeetingFaceWalks (R S : ℕ) (V : Finset LatticePoint) (n : ℕ) :=
  {q : RootedFaceWalks (faceIndices R S) n //
    ∃ u ∈ q.2.1.support, u.1 ∈ markedFaces R S V}

/-- Closed normalized words together with a lower-left placement that meets a
marked face. -/
def ClosedWordPlacements (R S : ℕ) (V : Finset LatticePoint) (n : ℕ) :=
  Σ omega : {w : Word n // w ∈ closedWords n},
    {s : Σ _x : ℕ, ℕ // s ∈ walkMeetingStarts R S V omega.1}

noncomputable def placementToMarkedWalk {R S n : ℕ}
    {V : Finset LatticePoint} :
    ClosedWordPlacements R S V n → MarkedMeetingFaceWalks R S V n := by
  intro a
  let omega := a.1.1
  let x := a.2.1.1
  let y := a.2.1.2
  have hs := mem_walkMeetingStarts.mp a.2.2
  have hclosed : IsClosed omega := mem_closedWords.mp a.1.2
  let root := placedFaceVertex omega x y hs.1 hs.2.1 ⟨0, by omega⟩
  let p := placedFaceWalk omega x y hs.1 hs.2.1 hclosed
  refine ⟨⟨root, ⟨p, length_placedFaceWalk omega x y hs.1 hs.2.1 hclosed⟩⟩, ?_⟩
  rcases hs.2.2 with ⟨q, hq⟩
  have hqParts := Finset.mem_inter.mp hq
  rcases (mem_placedPartialSums_iff_exists_position omega x y q).mp hqParts.1 with
    ⟨t, ht, rfl⟩
  refine ⟨placedFaceVertex omega x y hs.1 hs.2.1 ⟨t, by omega⟩, ?_, hqParts.2⟩
  rw [support_placedFaceWalk]
  unfold placedFaceSupport
  rw [List.mem_ofFn]
  exact ⟨⟨t, by omega⟩, rfl⟩

noncomputable def faceWalkStartXN {U : Finset LatticePoint} {n : ℕ}
    {z : {q // q ∈ U}} (p : (faceGraph U).Walk z z)
    (hlen : p.length = n) : ℕ :=
  ((z.1.1 : ℤ) + walkMinX (wordOfFaceWalkN p hlen)).toNat

noncomputable def faceWalkStartYN {U : Finset LatticePoint} {n : ℕ}
    {z : {q // q ∈ U}} (p : (faceGraph U).Walk z z)
    (hlen : p.length = n) : ℕ :=
  ((z.1.2 : ℤ) + walkMinY (wordOfFaceWalkN p hlen)).toNat

theorem faceWalkN_lowerX_nonneg {R S n : ℕ}
    {z : {q // q ∈ faceIndices R S}}
    (p : (faceGraph (faceIndices R S)).Walk z z) (hlen : p.length = n) :
    0 ≤ (z.1.1 : ℤ) + walkMinX (wordOfFaceWalkN p hlen) := by
  rcases exists_position_fst_eq_walkMinX (wordOfFaceWalkN p hlen) with
    ⟨t, ht, hmin⟩
  have hpos := congrArg Prod.fst (position_wordOfFaceWalkN p hlen ht)
  have hv : 0 ≤ ((p.getVert t).1.1 : ℤ) := Int.natCast_nonneg _
  simp only [latticePointToPoint, Prod.fst_sub] at hpos
  omega

theorem faceWalkN_lowerY_nonneg {R S n : ℕ}
    {z : {q // q ∈ faceIndices R S}}
    (p : (faceGraph (faceIndices R S)).Walk z z) (hlen : p.length = n) :
    0 ≤ (z.1.2 : ℤ) + walkMinY (wordOfFaceWalkN p hlen) := by
  rcases exists_position_snd_eq_walkMinY (wordOfFaceWalkN p hlen) with
    ⟨t, ht, hmin⟩
  have hpos := congrArg Prod.snd (position_wordOfFaceWalkN p hlen ht)
  have hv : 0 ≤ ((p.getVert t).1.2 : ℤ) := Int.natCast_nonneg _
  simp only [latticePointToPoint, Prod.snd_sub] at hpos
  omega

theorem faceWalkStartXN_span_le {R S n : ℕ}
    {z : {q // q ∈ faceIndices R S}}
    (p : (faceGraph (faceIndices R S)).Walk z z) (hlen : p.length = n) :
    faceWalkStartXN p hlen + (spanX (wordOfFaceWalkN p hlen) + 1) ≤ R := by
  let omega := wordOfFaceWalkN p hlen
  rcases exists_position_fst_eq_walkMaxX omega with ⟨t, ht, hmax⟩
  have hpos := congrArg Prod.fst (position_wordOfFaceWalkN p hlen ht)
  have hv := (mem_faceIndices.mp (p.getVert t).2).1
  have hminmax := walkMinX_le_walkMaxX omega
  have hlower := faceWalkN_lowerX_nonneg p hlen
  have hdiff : 0 ≤ walkMaxX omega - walkMinX omega := sub_nonneg.mpr hminmax
  have hstartCast : ((faceWalkStartXN p hlen : ℕ) : ℤ) =
      (z.1.1 : ℤ) + walkMinX omega := by
    exact Int.toNat_of_nonneg hlower
  have hspanCast : ((spanX omega : ℕ) : ℤ) =
      walkMaxX omega - walkMinX omega := Int.toNat_of_nonneg hdiff
  simp only [latticePointToPoint, Prod.fst_sub] at hpos
  dsimp only [omega] at *
  have hint : ((faceWalkStartXN p hlen : ℕ) : ℤ) +
      (spanX (wordOfFaceWalkN p hlen) : ℤ) + 1 ≤ (R : ℤ) := by
    rw [hstartCast, hspanCast]
    omega
  exact_mod_cast hint

theorem faceWalkStartYN_span_le {R S n : ℕ}
    {z : {q // q ∈ faceIndices R S}}
    (p : (faceGraph (faceIndices R S)).Walk z z) (hlen : p.length = n) :
    faceWalkStartYN p hlen + (spanY (wordOfFaceWalkN p hlen) + 1) ≤ S := by
  let omega := wordOfFaceWalkN p hlen
  rcases exists_position_snd_eq_walkMaxY omega with ⟨t, ht, hmax⟩
  have hpos := congrArg Prod.snd (position_wordOfFaceWalkN p hlen ht)
  have hv := (mem_faceIndices.mp (p.getVert t).2).2
  have hminmax := walkMinY_le_walkMaxY omega
  have hlower := faceWalkN_lowerY_nonneg p hlen
  have hdiff : 0 ≤ walkMaxY omega - walkMinY omega := sub_nonneg.mpr hminmax
  have hstartCast : ((faceWalkStartYN p hlen : ℕ) : ℤ) =
      (z.1.2 : ℤ) + walkMinY omega := by
    exact Int.toNat_of_nonneg hlower
  have hspanCast : ((spanY omega : ℕ) : ℤ) =
      walkMaxY omega - walkMinY omega := Int.toNat_of_nonneg hdiff
  simp only [latticePointToPoint, Prod.snd_sub] at hpos
  dsimp only [omega] at *
  have hint : ((faceWalkStartYN p hlen : ℕ) : ℤ) +
      (spanY (wordOfFaceWalkN p hlen) : ℤ) + 1 ≤ (S : ℤ) := by
    rw [hstartCast, hspanCast]
    omega
  exact_mod_cast hint

theorem placedWalkVertex_wordOfFaceWalkN {R S n t : ℕ}
    {z : {q // q ∈ faceIndices R S}}
    (p : (faceGraph (faceIndices R S)).Walk z z) (hlen : p.length = n)
    (ht : t ≤ n) :
    placedWalkVertex (wordOfFaceWalkN p hlen) (faceWalkStartXN p hlen)
        (faceWalkStartYN p hlen) t = (p.getVert t).1 := by
  apply latticePointToPoint_injective
  rw [placedWalkVertex_toPoint (wordOfFaceWalkN p hlen)
    (faceWalkStartXN p hlen) (faceWalkStartYN p hlen) ht]
  rw [position_wordOfFaceWalkN p hlen ht]
  have hx : ((faceWalkStartXN p hlen : ℕ) : ℤ) =
      (z.1.1 : ℤ) + walkMinX (wordOfFaceWalkN p hlen) := by
    exact Int.toNat_of_nonneg (faceWalkN_lowerX_nonneg p hlen)
  have hy : ((faceWalkStartYN p hlen : ℕ) : ℤ) =
      (z.1.2 : ℤ) + walkMinY (wordOfFaceWalkN p hlen) := by
    exact Int.toNat_of_nonneg (faceWalkN_lowerY_nonneg p hlen)
  apply Prod.ext
  · simp only [latticePointToPoint, Prod.fst_sub, Prod.fst_add]
    omega
  · simp only [latticePointToPoint, Prod.snd_sub, Prod.snd_add]
    omega

theorem placedFaceSupport_wordOfFaceWalkN {R S n : ℕ}
    {z : {q // q ∈ faceIndices R S}}
    (p : (faceGraph (faceIndices R S)).Walk z z) (hlen : p.length = n) :
    placedFaceSupport (wordOfFaceWalkN p hlen)
        (faceWalkStartXN p hlen) (faceWalkStartYN p hlen)
        (faceWalkStartXN_span_le p hlen) (faceWalkStartYN_span_le p hlen) =
      p.support := by
  apply List.ext_getElem
  · simp [placedFaceSupport, hlen]
  · intro i hi₁ hi₂
    have hi : i ≤ n := by
      simpa [placedFaceSupport] using hi₁
    rw [SimpleGraph.Walk.support_getElem_eq_getVert p]
    unfold placedFaceSupport
    rw [List.getElem_ofFn]
    apply Subtype.ext
    exact placedWalkVertex_wordOfFaceWalkN p hlen hi

theorem placedFaceWalk_wordOfFaceWalkN {R S n : ℕ}
    {z : {q // q ∈ faceIndices R S}}
    (p : (faceGraph (faceIndices R S)).Walk z z) (hlen : p.length = n) :
    (placedFaceWalk (wordOfFaceWalkN p hlen)
      (faceWalkStartXN p hlen) (faceWalkStartYN p hlen)
      (faceWalkStartXN_span_le p hlen) (faceWalkStartYN_span_le p hlen)
      (isClosed_wordOfFaceWalkN p hlen)).copy
        (by
          apply Subtype.ext
          simpa [placedFaceVertex] using
            placedWalkVertex_wordOfFaceWalkN p hlen (Nat.zero_le _))
        (by
          apply Subtype.ext
          simpa [placedFaceVertex] using
            placedWalkVertex_wordOfFaceWalkN p hlen (Nat.zero_le _)) = p := by
  apply SimpleGraph.Walk.support_injective
  rw [SimpleGraph.Walk.support_copy, support_placedFaceWalk]
  exact placedFaceSupport_wordOfFaceWalkN p hlen

theorem faceWalkStartXN_placedFaceWalk {n R S : ℕ} (omega : Word n)
    (x y : ℕ) (hx : x + (spanX omega + 1) ≤ R)
    (hy : y + (spanY omega + 1) ≤ S)
    (hclosed : IsClosed omega) :
    faceWalkStartXN (placedFaceWalk omega x y hx hy hclosed)
      (length_placedFaceWalk omega x y hx hy hclosed) = x := by
  have hword := wordOfFaceWalkN_placedFaceWalk omega x y hx hy hclosed
  have hz := congrArg Prod.fst
    (normalizedWalkPoint_toPoint omega (zero_mem_partialSums omega))
  simp only [latticePointToPoint, Prod.fst_sub] at hz
  unfold faceWalkStartXN
  rw [hword]
  simp only [placedFaceVertex, placedWalkVertex]
  have heq : ((x + (normalizedWalkPoint omega (position omega 0)).1 : ℕ) : ℤ) +
      walkMinX omega = (x : ℤ) := by
    rw [position_zero]
    simp only [Nat.cast_add]
    omega
  rw [heq]
  simp

theorem faceWalkStartYN_placedFaceWalk {n R S : ℕ} (omega : Word n)
    (x y : ℕ) (hx : x + (spanX omega + 1) ≤ R)
    (hy : y + (spanY omega + 1) ≤ S)
    (hclosed : IsClosed omega) :
    faceWalkStartYN (placedFaceWalk omega x y hx hy hclosed)
      (length_placedFaceWalk omega x y hx hy hclosed) = y := by
  have hword := wordOfFaceWalkN_placedFaceWalk omega x y hx hy hclosed
  have hz := congrArg Prod.snd
    (normalizedWalkPoint_toPoint omega (zero_mem_partialSums omega))
  simp only [latticePointToPoint, Prod.snd_sub] at hz
  unfold faceWalkStartYN
  rw [hword]
  simp only [placedFaceVertex, placedWalkVertex]
  have heq : ((y + (normalizedWalkPoint omega (position omega 0)).2 : ℕ) : ℤ) +
      walkMinY omega = (y : ℤ) := by
    rw [position_zero]
    simp only [Nat.cast_add]
    omega
  rw [heq]
  simp

noncomputable def markedWalkToPlacement {R S n : ℕ}
    {V : Finset LatticePoint} :
    MarkedMeetingFaceWalks R S V n → ClosedWordPlacements R S V n := by
  intro a
  let p := a.1.2.1
  let hlen := a.1.2.2
  let omega := wordOfFaceWalkN p hlen
  let x := faceWalkStartXN p hlen
  let y := faceWalkStartYN p hlen
  have hx : x + (spanX omega + 1) ≤ R := faceWalkStartXN_span_le p hlen
  have hy : y + (spanY omega + 1) ≤ S := faceWalkStartYN_span_le p hlen
  refine ⟨⟨omega, mem_closedWords.mpr (isClosed_wordOfFaceWalkN p hlen)⟩,
    ⟨⟨x, y⟩, mem_walkMeetingStarts.mpr ⟨hx, hy, ?_⟩⟩⟩
  rcases a.2 with ⟨u, hu, huM⟩
  rcases (SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hu) with
    ⟨t, htu, ht⟩
  have htn : t ≤ n := by omega
  refine ⟨u.1, Finset.mem_inter.mpr ⟨?_, huM⟩⟩
  rw [mem_placedPartialSums_iff_exists_position]
  refine ⟨t, htn, ?_⟩
  rw [placedWalkVertex_wordOfFaceWalkN p hlen htn, htu]

theorem markedWalkToPlacement_placementToMarkedWalk {R S n : ℕ}
    {V : Finset LatticePoint} (a : ClosedWordPlacements R S V n) :
    markedWalkToPlacement (placementToMarkedWalk a) = a := by
  rcases a with ⟨⟨omega, homega⟩, ⟨⟨x, y⟩, hs⟩⟩
  have hs' := mem_walkMeetingStarts.mp hs
  have hclosed := mem_closedWords.mp homega
  let b := markedWalkToPlacement
    (placementToMarkedWalk ⟨⟨omega, homega⟩, ⟨⟨x, y⟩, hs⟩⟩)
  change b = ⟨⟨omega, homega⟩, ⟨⟨x, y⟩, hs⟩⟩
  have hw : b.1 = ⟨omega, homega⟩ := by
    apply Subtype.ext
    exact wordOfFaceWalkN_placedFaceWalk omega x y hs'.1 hs'.2.1 hclosed
  apply Sigma.ext hw
  apply (Subtype.heq_iff_coe_eq (fun s => by
    have hwval := congrArg Subtype.val hw
    rw [hwval])).mpr
  apply Sigma.ext
  · exact faceWalkStartXN_placedFaceWalk omega x y hs'.1 hs'.2.1 hclosed
  · rw [heq_iff_eq]
    exact faceWalkStartYN_placedFaceWalk omega x y hs'.1 hs'.2.1 hclosed

theorem walk_heq_of_copy_eq {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u u) (q : G.Walk v v) (h : u = v)
    (hc : p.copy h h = q) : p ≍ q := by
  subst v
  rw [heq_iff_eq]
  simpa using hc

theorem walkLengthSubtype_heq_of_copy_eq {V : Type*} {G : SimpleGraph V}
    {u v : V} {n : ℕ}
    (a : {p : G.Walk u u // p.length = n})
    (b : {p : G.Walk v v // p.length = n}) (h : u = v)
    (hc : a.1.copy h h = b.1) : a ≍ b := by
  subst v
  rw [heq_iff_eq]
  apply Subtype.ext
  simpa using hc

theorem placementToMarkedWalk_markedWalkToPlacement {R S n : ℕ}
    {V : Finset LatticePoint} (a : MarkedMeetingFaceWalks R S V n) :
    placementToMarkedWalk (markedWalkToPlacement a) = a := by
  rcases a with ⟨⟨z, ⟨p, hlen⟩⟩, hmeet⟩
  apply Subtype.ext
  have hroot :
      placedFaceVertex (wordOfFaceWalkN p hlen)
          (faceWalkStartXN p hlen) (faceWalkStartYN p hlen)
          (faceWalkStartXN_span_le p hlen) (faceWalkStartYN_span_le p hlen)
          ⟨0, by omega⟩ = z := by
    apply Subtype.ext
    simpa [placedFaceVertex] using
      placedWalkVertex_wordOfFaceWalkN p hlen (Nat.zero_le _)
  apply Sigma.ext hroot
  apply walkLengthSubtype_heq_of_copy_eq _ _ hroot
  exact placedFaceWalk_wordOfFaceWalkN p hlen

/-- Inclusion of an unmarked face into the full rectangular face set. -/
def unmarkedFaceInclusion (R S : ℕ) (V : Finset LatticePoint) :
    {q // q ∈ unmarkedFaces R S V} → {q // q ∈ faceIndices R S} :=
  fun q => ⟨q.1, (mem_unmarkedFaces.mp q.2).1⟩

def unmarkedFaceHom (R S : ℕ) (V : Finset LatticePoint) :
    faceGraph (unmarkedFaces R S V) →g faceGraph (faceIndices R S) where
  toFun := unmarkedFaceInclusion R S V
  map_rel' h := h

/-- Restrict a full-rectangle walk whose support is unmarked to the induced
unmarked face graph. -/
noncomputable def restrictToUnmarked {R S : ℕ} {V : Finset LatticePoint}
    {z w : {q // q ∈ faceIndices R S}}
    (p : (faceGraph (faceIndices R S)).Walk z w)
    (hall : ∀ u ∈ p.support, u.1 ∈ unmarkedFaces R S V) :
    (faceGraph (unmarkedFaces R S V)).Walk
      ⟨z.1, hall z p.start_mem_support⟩
      ⟨w.1, hall w p.end_mem_support⟩ := by
  induction p with
  | nil => exact .nil
  | @cons u v w huv p ih =>
      have huv' : (faceGraph (unmarkedFaces R S V)).Adj
          ⟨u.1, hall u (by simp)⟩ ⟨v.1, hall v (by simp)⟩ := huv
      apply SimpleGraph.Walk.cons huv'
      exact ih (fun q hq => hall q (by simp [hq]))

theorem support_map_restrictToUnmarked {R S : ℕ} {V : Finset LatticePoint}
    {z w : {q // q ∈ faceIndices R S}}
    (p : (faceGraph (faceIndices R S)).Walk z w)
    (hall : ∀ u ∈ p.support, u.1 ∈ unmarkedFaces R S V) :
    ((restrictToUnmarked p hall).map (unmarkedFaceHom R S V)).support = p.support := by
  induction p with
  | nil => simp [restrictToUnmarked, unmarkedFaceHom, unmarkedFaceInclusion]
  | @cons u v w huv p ih =>
      simp only [restrictToUnmarked, SimpleGraph.Walk.map_cons,
        SimpleGraph.Walk.support_cons]
      congr 1
      exact ih (fun q hq => hall q (by simp [hq]))

@[simp] theorem length_restrictToUnmarked {R S : ℕ}
    {V : Finset LatticePoint} {z w : {q // q ∈ faceIndices R S}}
    (p : (faceGraph (faceIndices R S)).Walk z w)
    (hall : ∀ u ∈ p.support, u.1 ∈ unmarkedFaces R S V) :
    (restrictToUnmarked p hall).length = p.length := by
  have h := congrArg List.length (support_map_restrictToUnmarked p hall)
  simpa using h

theorem map_restrictToUnmarked_copy {R S : ℕ} {V : Finset LatticePoint}
    {z w : {q // q ∈ faceIndices R S}}
    (p : (faceGraph (faceIndices R S)).Walk z w)
    (hall : ∀ u ∈ p.support, u.1 ∈ unmarkedFaces R S V) :
    ((restrictToUnmarked p hall).map (unmarkedFaceHom R S V)).copy
      (by apply Subtype.ext; rfl) (by apply Subtype.ext; rfl) = p := by
  apply SimpleGraph.Walk.support_injective
  rw [SimpleGraph.Walk.support_copy]
  exact support_map_restrictToUnmarked p hall

def AllUnmarkedFaceWalks (R S : ℕ) (V : Finset LatticePoint) (n : ℕ) :=
  {q : RootedFaceWalks (faceIndices R S) n //
    ∀ u ∈ q.2.1.support, u.1 ∈ unmarkedFaces R S V}

noncomputable def liftUnmarkedRootedWalk {R S n : ℕ}
    {V : Finset LatticePoint} :
    RootedFaceWalks (unmarkedFaces R S V) n → AllUnmarkedFaceWalks R S V n := by
  rintro ⟨z, ⟨p, hlen⟩⟩
  have hl : (p.map (unmarkedFaceHom R S V)).length = n := by
    rw [SimpleGraph.Walk.length_map]
    exact hlen
  refine ⟨⟨(unmarkedFaceHom R S V) z,
    ⟨p.map (unmarkedFaceHom R S V), hl⟩⟩, ?_⟩
  intro u hu
  rw [SimpleGraph.Walk.support_map] at hu
  rcases List.mem_map.mp hu with ⟨v, hv, rfl⟩
  exact v.2

noncomputable def restrictUnmarkedRootedWalk {R S n : ℕ}
    {V : Finset LatticePoint} :
    AllUnmarkedFaceWalks R S V n → RootedFaceWalks (unmarkedFaces R S V) n := by
  intro a
  let p := a.1.2.1
  let hall := a.2
  exact ⟨⟨a.1.1.1, hall a.1.1 p.start_mem_support⟩,
    ⟨restrictToUnmarked p hall, by simpa using a.1.2.2⟩⟩

theorem liftUnmarkedRootedWalk_restrictUnmarkedRootedWalk {R S n : ℕ}
    {V : Finset LatticePoint} (a : AllUnmarkedFaceWalks R S V n) :
    liftUnmarkedRootedWalk (restrictUnmarkedRootedWalk a) = a := by
  rcases a with ⟨⟨z, ⟨p, hlen⟩⟩, hall⟩
  dsimp only [liftUnmarkedRootedWalk, restrictUnmarkedRootedWalk]
  apply Subtype.ext
  have hroot : unmarkedFaceInclusion R S V
      ⟨z.1, hall z p.start_mem_support⟩ = z := by
    apply Subtype.ext
    rfl
  apply Sigma.ext hroot
  apply walkLengthSubtype_heq_of_copy_eq _ _ hroot
  exact map_restrictToUnmarked_copy p hall

theorem unmarkedFaceInclusion_injective (R S : ℕ) (V : Finset LatticePoint) :
    Function.Injective (unmarkedFaceInclusion R S V) := by
  intro a b h
  exact Subtype.ext (congrArg
    (fun x : {q // q ∈ faceIndices R S} => x.1) h)

theorem liftUnmarkedRootedWalk_injective {R S n : ℕ}
    {V : Finset LatticePoint} :
    Function.Injective
      (liftUnmarkedRootedWalk : RootedFaceWalks (unmarkedFaces R S V) n →
        AllUnmarkedFaceWalks R S V n) := by
  rintro ⟨z, ⟨p, hp⟩⟩ ⟨w, ⟨q, hq⟩⟩ h
  have hval := congrArg Subtype.val h
  have hparts := Sigma.ext_iff.mp hval
  dsimp only [liftUnmarkedRootedWalk] at hparts
  have hzw : z = w := unmarkedFaceInclusion_injective R S V hparts.1
  subst w
  have hwalk := congrArg Subtype.val (eq_of_heq hparts.2)
  refine Sigma.ext
    (x := (⟨z, ⟨p, hp⟩⟩ : RootedFaceWalks (unmarkedFaces R S V) n))
    (y := (⟨z, ⟨q, hq⟩⟩ : RootedFaceWalks (unmarkedFaces R S V) n)) rfl ?_
  rw [heq_iff_eq]
  apply Subtype.ext
  exact SimpleGraph.Walk.map_injective_of_injective
    (f := unmarkedFaceHom R S V)
    (unmarkedFaceInclusion_injective R S V) z z hwalk

noncomputable instance rootedFaceWalksFintype (U : Finset LatticePoint) (n : ℕ) :
    Fintype (RootedFaceWalks U n) := by
  unfold RootedFaceWalks
  infer_instance

noncomputable instance allUnmarkedFaceWalksFintype (R S : ℕ)
    (V : Finset LatticePoint) (n : ℕ) :
    Fintype (AllUnmarkedFaceWalks R S V n) := by
  unfold AllUnmarkedFaceWalks
  infer_instance

theorem card_allUnmarkedFaceWalks_eq_rootedUnmarked {R S n : ℕ}
    (V : Finset LatticePoint) :
    Fintype.card (AllUnmarkedFaceWalks R S V n) =
      Fintype.card (RootedFaceWalks (unmarkedFaces R S V) n) := by
  classical
  apply Nat.le_antisymm
  · apply Fintype.card_le_of_injective restrictUnmarkedRootedWalk
    intro a b h
    rw [← liftUnmarkedRootedWalk_restrictUnmarkedRootedWalk a,
      ← liftUnmarkedRootedWalk_restrictUnmarkedRootedWalk b, h]
  · exact Fintype.card_le_of_injective liftUnmarkedRootedWalk
      liftUnmarkedRootedWalk_injective

theorem mem_unmarkedFaces_iff_not_mem_markedFaces {R S : ℕ}
    {V : Finset LatticePoint} {u : LatticePoint}
    (hu : u ∈ faceIndices R S) :
    u ∈ unmarkedFaces R S V ↔ u ∉ markedFaces R S V := by
  simp [unmarkedFaces, hu]

theorem allUnmarked_iff_not_meetsMarked {R S n : ℕ}
    {V : Finset LatticePoint} (q : RootedFaceWalks (faceIndices R S) n) :
    (∀ u ∈ q.2.1.support, u.1 ∈ unmarkedFaces R S V) ↔
      ¬ ∃ u ∈ q.2.1.support, u.1 ∈ markedFaces R S V := by
  constructor
  · intro hall ⟨u, hu, huM⟩
    exact (mem_unmarkedFaces_iff_not_mem_markedFaces u.2).mp (hall u hu) huM
  · intro hnone u hu
    apply (mem_unmarkedFaces_iff_not_mem_markedFaces u.2).mpr
    exact fun huM => hnone ⟨u, hu, huM⟩

def notMeetingEquivAllUnmarked (R S : ℕ) (V : Finset LatticePoint) (n : ℕ) :
    {q : RootedFaceWalks (faceIndices R S) n //
      ¬ ∃ u ∈ q.2.1.support, u.1 ∈ markedFaces R S V} ≃
      AllUnmarkedFaceWalks R S V n where
  toFun q := ⟨q.1, (allUnmarked_iff_not_meetsMarked q.1).mpr q.2⟩
  invFun q := ⟨q.1, (allUnmarked_iff_not_meetsMarked q.1).mp q.2⟩
  left_inv q := by apply Subtype.ext; rfl
  right_inv q := by apply Subtype.ext; rfl

noncomputable instance markedMeetingFaceWalksFintype (R S : ℕ)
    (V : Finset LatticePoint) (n : ℕ) :
    Fintype (MarkedMeetingFaceWalks R S V n) := by
  unfold MarkedMeetingFaceWalks
  infer_instance

noncomputable instance closedWordPlacementsFintype (R S : ℕ)
    (V : Finset LatticePoint) (n : ℕ) :
    Fintype (ClosedWordPlacements R S V n) := by
  unfold ClosedWordPlacements
  infer_instance

noncomputable def closedWordPlacementsEquivMarkedMeeting
    (R S : ℕ) (V : Finset LatticePoint) (n : ℕ) :
    ClosedWordPlacements R S V n ≃ MarkedMeetingFaceWalks R S V n where
  toFun := placementToMarkedWalk
  invFun := markedWalkToPlacement
  left_inv := markedWalkToPlacement_placementToMarkedWalk
  right_inv := placementToMarkedWalk_markedWalkToPlacement

theorem card_rootedFaceWalks_eq_closedFaceWalkCount
    (U : Finset LatticePoint) (n : ℕ) :
    Fintype.card (RootedFaceWalks U n) = closedFaceWalkCount U n := by
  classical
  change Fintype.card (Σ z : {q // q ∈ U},
    {p : (faceGraph U).Walk z z // p.length = n}) = closedFaceWalkCount U n
  rw [closedFaceWalkCount, Fintype.card_sigma]

theorem card_closedWordPlacements_eq_closedPlacementCount
    (R S : ℕ) (V : Finset LatticePoint) (n : ℕ) :
    Fintype.card (ClosedWordPlacements R S V n) =
      closedPlacementCount R S V n := by
  classical
  change Fintype.card (Σ omega : {w : Word n // w ∈ closedWords n},
    {s : Σ _x : ℕ, ℕ // s ∈ walkMeetingStarts R S V omega.1}) =
      closedPlacementCount R S V n
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe]
  exact Finset.sum_coe_sort (closedWords n)
    (fun omega => (walkMeetingStarts R S V omega).card)

theorem card_fullFaceWalks_eq_unmarked_add_meeting
    (R S : ℕ) (V : Finset LatticePoint) (n : ℕ) :
    Fintype.card (RootedFaceWalks (faceIndices R S) n) =
      Fintype.card (RootedFaceWalks (unmarkedFaces R S V) n) +
        Fintype.card (MarkedMeetingFaceWalks R S V n) := by
  classical
  let P : RootedFaceWalks (faceIndices R S) n → Prop :=
    fun q => ∃ u ∈ q.2.1.support, u.1 ∈ markedFaces R S V
  have hpartition := Fintype.card_congr (Equiv.sumCompl P)
  have hnot : Fintype.card {q // ¬ P q} =
      Fintype.card (RootedFaceWalks (unmarkedFaces R S V) n) := by
    rw [Fintype.card_congr (notMeetingEquivAllUnmarked R S V n),
      card_allUnmarkedFaceWalks_eq_rootedUnmarked]
  have hmeet : Fintype.card {q // P q} =
      Fintype.card (MarkedMeetingFaceWalks R S V n) := rfl
  simp only [Fintype.card_sum] at hpartition
  rw [hmeet, hnot] at hpartition
  omega

/-- Exact finite partition form of equation `trace-walks`: every rooted
closed walk in the full face rectangle either stays in the unmarked induced
graph or has one unique closed-word/lower-left-placement representation that
meets a marked face. -/
theorem closedFaceWalkCount_eq_unmarked_add_closedPlacementCount
    (R S : ℕ) (V : Finset LatticePoint) (n : ℕ) :
    closedFaceWalkCount (faceIndices R S) n =
      closedFaceWalkCount (unmarkedFaces R S V) n +
        closedPlacementCount R S V n := by
  have hpart := card_fullFaceWalks_eq_unmarked_add_meeting R S V n
  rw [card_rootedFaceWalks_eq_closedFaceWalkCount,
    card_rootedFaceWalks_eq_closedFaceWalkCount] at hpart
  have hequiv := Fintype.card_congr
    (closedWordPlacementsEquivMarkedMeeting R S V n)
  rw [card_closedWordPlacements_eq_closedPlacementCount] at hequiv
  omega

/-- Natural-number subtraction form, matching the manuscript's displayed
trace difference. -/
theorem closedFaceWalkCount_sub_unmarked_eq_closedPlacementCount
    (R S : ℕ) (V : Finset LatticePoint) (n : ℕ) :
    closedFaceWalkCount (faceIndices R S) n -
      closedFaceWalkCount (unmarkedFaces R S V) n =
        closedPlacementCount R S V n := by
  have h := closedFaceWalkCount_eq_unmarked_add_closedPlacementCount R S V n
  omega

/-- Trace form over the natural adjacency matrices. -/
theorem trace_walks_nat (R S : ℕ) (V : Finset LatticePoint) (n : ℕ) :
    Matrix.trace ((faceGraph (faceIndices R S)).adjMatrix ℕ ^ n) -
      Matrix.trace ((faceGraph (unmarkedFaces R S V)).adjMatrix ℕ ^ n) =
        closedPlacementCount R S V n := by
  rw [trace_adjMatrix_pow_eq_closedFaceWalkCount,
    trace_adjMatrix_pow_eq_closedFaceWalkCount]
  exact closedFaceWalkCount_sub_unmarked_eq_closedPlacementCount R S V n

/-- Real trace form used directly in the logarithmic determinant series. -/
theorem trace_walks_real (R S : ℕ) (V : Finset LatticePoint) (n : ℕ) :
    Matrix.trace ((faceGraph (faceIndices R S)).adjMatrix ℝ ^ n) -
      Matrix.trace ((faceGraph (unmarkedFaces R S V)).adjMatrix ℝ ^ n) =
        (closedPlacementCount R S V n : ℝ) := by
  rw [trace_adjMatrix_pow_real_eq_closedFaceWalkCount,
    trace_adjMatrix_pow_real_eq_closedFaceWalkCount]
  have h := closedFaceWalkCount_eq_unmarked_add_closedPlacementCount R S V n
  have hr : (closedFaceWalkCount (faceIndices R S) n : ℝ) =
      (closedFaceWalkCount (unmarkedFaces R S V) n : ℝ) +
        (closedPlacementCount R S V n : ℝ) := by
    exact_mod_cast h
  linarith

end Boundary
end SquareMaximality
