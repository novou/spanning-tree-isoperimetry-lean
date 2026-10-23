module

public import SquareMaximality.Boundary.DeterminantSeries
public import SquareMaximality.Dual.Components
public import SquareMaximality.Inputs.MatrixTree
public import SquareMaximality.Multigraph.Contraction

@[expose] public section

set_option backward.privateInPublic true

/-!
# Boundary determinants from the explicit rectangular dual

This file isolates the genuinely planar part of the boundary determinant
argument from its finite algebra.  The planar residual is stated as an
explicit equivalence of spanning-tree types (induced by complementing edge
labels), rather than as either of the determinant identities that it is used
to prove.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SquareMaximality
namespace Dual

open Multigraph
open Multigraph.LabeledMultigraph

/-- Bounded faces of the explicit `(R+1) × (S+1)` dual are exactly the
natural-coordinate indices in `faceIndices R S`. -/
def boundedFaceEquivFaceIndices (R S : ℕ) :
    BoundedFace (R + 1) (S + 1) ≃
      {z // z ∈ Boundary.faceIndices R S} where
  toFun f := ⟨(f.1.1, f.2.1), by
    rw [Boundary.mem_faceIndices]
    constructor <;> omega⟩
  invFun z :=
    (⟨z.1.1, by
      have hz := Boundary.mem_faceIndices.mp z.2
      omega⟩,
     ⟨z.1.2, by
      have hz := Boundary.mem_faceIndices.mp z.2
      omega⟩)
  left_inv f := by
    apply Prod.ext <;> apply Fin.ext <;> rfl
  right_inv z := by
    apply Subtype.ext
    rfl

@[simp] theorem boundedFaceEquivFaceIndices_apply_val
    (R S : ℕ) (f : BoundedFace (R + 1) (S + 1)) :
    (boundedFaceEquivFaceIndices R S f).1 = (f.1.1, f.2.1) :=
  rfl

/-- Removing the exterior vertex `none` from an option type leaves the
underlying type. -/
noncomputable def awayNoneEquiv (α : Type*) :
    {v : Option α // v ≠ none} ≃ α := by
  classical
  exact ((Equiv.optionSubtype (none : Option α))
    ⟨Equiv.refl (Option α), rfl⟩).symm

@[simp] theorem some_awayNoneEquiv (α : Type*)
    (v : {v : Option α // v ≠ none}) :
    some (awayNoneEquiv α v) = v.1 := by
  classical
  exact Equiv.optionSubtype_apply_symm_apply
    (none : Option α) ⟨Equiv.refl (Option α), rfl⟩ v

/-- The row/column indices of the exterior-rooted dual cofactor are precisely
the bounded face indices. -/
noncomputable def dualAwayExteriorEquivFaceIndices (R S : ℕ) :
    LabeledMultigraph.AwayFrom
        (none : RectangleDualVertex (R + 1) (S + 1)) ≃
      {z // z ∈ Boundary.faceIndices R S} :=
  (awayNoneEquiv (BoundedFace (R + 1) (S + 1))).trans
    (boundedFaceEquivFaceIndices R S)

@[simp] theorem dualAwayExteriorEquivFaceIndices_apply_val
    (R S : ℕ)
    (v : LabeledMultigraph.AwayFrom
      (none : RectangleDualVertex (R + 1) (S + 1))) :
    (dualAwayExteriorEquivFaceIndices R S v).1 =
      ((awayNoneEquiv (BoundedFace (R + 1) (S + 1)) v).1.1,
       (awayNoneEquiv (BoundedFace (R + 1) (S + 1)) v).2.1) :=
  rfl

/-- Coordinate classification of a horizontal dual label between two bounded
faces.  The two disjuncts are the two orientations of the unordered ends. -/
theorem rectangleDual_horizontal_isLink_some_some_iff
    {r s : ℕ} (e : HorizontalEdge r s) (f g : BoundedFace r s) :
    (rectangleDual r s).IsLink (.horizontal e) (some f) (some g) ↔
      (e.x = f.1 ∧ e.x = g.1 ∧
        e.y.1 = f.2.1 + 1 ∧ e.y.1 = g.2.1) ∨
      (e.x = g.1 ∧ e.x = f.1 ∧
        e.y.1 = g.2.1 + 1 ∧ e.y.1 = f.2.1) := by
  change s(horizontalBelow e, horizontalAbove e) = s(some f, some g) ↔ _
  rw [Sym2.eq_iff]
  by_cases hy0 : e.y.1 = 0
  · simp [horizontalBelow, horizontalAbove, hy0]
  · by_cases hytop : e.y.1 + 1 < s
    · simp only [horizontalBelow, horizontalAbove, dif_neg hy0, dif_pos hytop,
        Option.some.injEq]
      constructor
      · rintro (⟨hbelowf, haboveg⟩ | ⟨hbelowg, habovef⟩)
        · left
          refine ⟨congrArg Prod.fst hbelowf, congrArg Prod.fst haboveg, ?_, ?_⟩
          · have h := congrArg (fun p => p.2.1) hbelowf
            dsimp only at h
            omega
          · exact congrArg (fun p => p.2.1) haboveg
        · right
          refine ⟨congrArg Prod.fst hbelowg, congrArg Prod.fst habovef, ?_, ?_⟩
          · have h := congrArg (fun p => p.2.1) hbelowg
            dsimp only at h
            omega
          · exact congrArg (fun p => p.2.1) habovef
      · rintro (⟨hxf, hxg, hyf, hyg⟩ | ⟨hxg, hxf, hyg, hyf⟩)
        · left
          constructor
          · apply Prod.ext
            · exact hxf
            · apply Fin.ext
              dsimp only
              omega
          · apply Prod.ext
            · exact hxg
            · apply Fin.ext
              exact hyg
        · right
          constructor
          · apply Prod.ext
            · exact hxg
            · apply Fin.ext
              dsimp only
              omega
          · apply Prod.ext
            · exact hxf
            · apply Fin.ext
              exact hyf
    · rw [horizontalBelow, dif_neg hy0, horizontalAbove, dif_neg hytop]
      constructor
      · rintro (⟨_, hnone⟩ | ⟨_, hnone⟩) <;> cases hnone
      · rintro (⟨_, _, _, hyg⟩ | ⟨_, _, _, hyf⟩)
        · have hglt := g.2.2
          omega
        · have hflt := f.2.2
          omega

/-- Coordinate classification of a vertical dual label between two bounded
faces. -/
theorem rectangleDual_vertical_isLink_some_some_iff
    {r s : ℕ} (e : VerticalEdge r s) (f g : BoundedFace r s) :
    (rectangleDual r s).IsLink (.vertical e) (some f) (some g) ↔
      (e.y = f.2 ∧ e.y = g.2 ∧
        e.x.1 = f.1.1 + 1 ∧ e.x.1 = g.1.1) ∨
      (e.y = g.2 ∧ e.y = f.2 ∧
        e.x.1 = g.1.1 + 1 ∧ e.x.1 = f.1.1) := by
  change s(verticalLeft e, verticalRight e) = s(some f, some g) ↔ _
  rw [Sym2.eq_iff]
  by_cases hx0 : e.x.1 = 0
  · simp [verticalLeft, verticalRight, hx0]
  · by_cases hxright : e.x.1 + 1 < r
    · simp only [verticalLeft, verticalRight, dif_neg hx0, dif_pos hxright,
        Option.some.injEq]
      constructor
      · rintro (⟨hleftf, hrightg⟩ | ⟨hleftg, hrightf⟩)
        · left
          refine ⟨congrArg Prod.snd hleftf, congrArg Prod.snd hrightg, ?_, ?_⟩
          · have h := congrArg (fun p => p.1.1) hleftf
            dsimp only at h
            omega
          · exact congrArg (fun p => p.1.1) hrightg
        · right
          refine ⟨congrArg Prod.snd hleftg, congrArg Prod.snd hrightf, ?_, ?_⟩
          · have h := congrArg (fun p => p.1.1) hleftg
            dsimp only at h
            omega
          · exact congrArg (fun p => p.1.1) hrightf
      · rintro (⟨hyf, hyg, hxf, hxg⟩ | ⟨hyg, hyf, hxg, hxf⟩)
        · left
          constructor
          · apply Prod.ext
            · apply Fin.ext
              dsimp only
              omega
            · exact hyf
          · apply Prod.ext
            · apply Fin.ext
              exact hxg
            · exact hyg
        · right
          constructor
          · apply Prod.ext
            · apply Fin.ext
              dsimp only
              omega
            · exact hyg
          · apply Prod.ext
            · apply Fin.ext
              exact hxf
            · exact hyf
    · rw [verticalLeft, dif_neg hx0, verticalRight, dif_neg hxright]
      constructor
      · rintro (⟨_, hnone⟩ | ⟨_, hnone⟩) <;> cases hnone
      · rintro (⟨_, _, _, hxg⟩ | ⟨_, _, _, hxf⟩)
        · have hglt := g.1.2
          omega
        · have hflt := f.1.2
          omega

/-- Two bounded dual faces share a labelled edge exactly when their natural
coordinates have Manhattan distance one. -/
theorem rectangleDual_exists_isLink_some_some_iff
    {r s : ℕ} (f g : BoundedFace r s) :
    (∃ e : RectangleEdge r s,
      (rectangleDual r s).IsLink e (some f) (some g)) ↔
      Boundary.natManhattanDist (f.1.1, f.2.1) (g.1.1, g.2.1) = 1 := by
  constructor
  · rintro ⟨e, he⟩
    cases e with
    | horizontal e =>
        rw [rectangleDual_horizontal_isLink_some_some_iff] at he
        rcases he with ⟨hxf, hxg, hyf, hyg⟩ | ⟨hxg, hxf, hyg, hyf⟩
        · unfold Boundary.natManhattanDist Nat.dist
          have hxx : f.1.1 = g.1.1 := by
            rw [← hxf, ← hxg]
          omega
        · unfold Boundary.natManhattanDist Nat.dist
          have hxx : f.1.1 = g.1.1 := by
            rw [← hxf, ← hxg]
          omega
    | vertical e =>
        rw [rectangleDual_vertical_isLink_some_some_iff] at he
        rcases he with ⟨hyf, hyg, hxf, hxg⟩ | ⟨hyg, hyf, hxg, hxf⟩
        · unfold Boundary.natManhattanDist Nat.dist
          have hyy : f.2.1 = g.2.1 := by
            rw [← hyf, ← hyg]
          omega
        · unfold Boundary.natManhattanDist Nat.dist
          have hyy : f.2.1 = g.2.1 := by
            rw [← hyf, ← hyg]
          omega
  · intro hdist
    have hcases :
        (f.1.1 = g.1.1 ∧
          (f.2.1 + 1 = g.2.1 ∨ g.2.1 + 1 = f.2.1)) ∨
        (f.2.1 = g.2.1 ∧
          (f.1.1 + 1 = g.1.1 ∨ g.1.1 + 1 = f.1.1)) := by
      unfold Boundary.natManhattanDist Nat.dist at hdist
      omega
    rcases hcases with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · rcases hy with hfg | hgf
      · let e : HorizontalEdge r s :=
          ⟨f.1, ⟨g.2.1, by have := g.2.2; omega⟩⟩
        refine ⟨.horizontal e,
          (rectangleDual_horizontal_isLink_some_some_iff e f g).2 ?_⟩
        left
        refine ⟨rfl, ?_, ?_, rfl⟩
        · apply Fin.ext
          exact hx
        · exact hfg.symm
      · let e : HorizontalEdge r s :=
          ⟨g.1, ⟨f.2.1, by have := f.2.2; omega⟩⟩
        refine ⟨.horizontal e,
          (rectangleDual_horizontal_isLink_some_some_iff e f g).2 ?_⟩
        right
        refine ⟨rfl, ?_, ?_, rfl⟩
        · apply Fin.ext
          exact hx.symm
        · exact hgf.symm
    · rcases hx with hfg | hgf
      · let e : VerticalEdge r s :=
          ⟨⟨g.1.1, by have := g.1.2; omega⟩, f.2⟩
        refine ⟨.vertical e,
          (rectangleDual_vertical_isLink_some_some_iff e f g).2 ?_⟩
        left
        refine ⟨rfl, ?_, ?_, rfl⟩
        · apply Fin.ext
          exact hy
        · exact hfg.symm
      · let e : VerticalEdge r s :=
          ⟨⟨f.1.1, by have := f.1.2; omega⟩, g.2⟩
        refine ⟨.vertical e,
          (rectangleDual_vertical_isLink_some_some_iff e f g).2 ?_⟩
        right
        refine ⟨rfl, ?_, ?_, rfl⟩
        · apply Fin.ext
          exact hy.symm
        · exact hgf.symm

private theorem horizontalEdge_ext {r s : ℕ} {e e' : HorizontalEdge r s}
    (hx : e.x = e'.x) (hy : e.y = e'.y) : e = e' := by
  cases e with
  | mk ex ey =>
      cases e' with
      | mk ex' ey' =>
          cases hx
          cases hy
          rfl

private theorem verticalEdge_ext {r s : ℕ} {e e' : VerticalEdge r s}
    (hx : e.x = e'.x) (hy : e.y = e'.y) : e = e' := by
  cases e with
  | mk ex ey =>
      cases e' with
      | mk ex' ey' =>
          cases hx
          cases hy
          rfl

/-- There is at most one rectangular primal label between two bounded dual
faces.  (Parallel labels occur only between a boundary face and the exterior.) -/
theorem rectangleDual_linkEdge_some_some_subsingleton
    {r s : ℕ} (f g : BoundedFace r s) :
    Subsingleton ((rectangleDual r s).LinkEdge (some f) (some g)) := by
  constructor
  rintro ⟨e, he⟩ ⟨e', he'⟩
  cases e with
  | horizontal e =>
      rw [rectangleDual_horizontal_isLink_some_some_iff] at he
      cases e' with
      | horizontal e' =>
          rw [rectangleDual_horizontal_isLink_some_some_iff] at he'
          rcases he with he | he <;> rcases he' with he' | he'
          · apply Subtype.ext
            apply congrArg RectangleEdge.horizontal
            apply horizontalEdge_ext
            · exact he.1.trans he'.1.symm
            · apply Fin.ext
              exact he.2.2.2.trans he'.2.2.2.symm
          · exfalso
            have hfg : f.2.1 + 1 = g.2.1 := he.2.2.1.symm.trans he.2.2.2
            have hgf : g.2.1 + 1 = f.2.1 := he'.2.2.1.symm.trans he'.2.2.2
            omega
          · exfalso
            have hgf : g.2.1 + 1 = f.2.1 := he.2.2.1.symm.trans he.2.2.2
            have hfg : f.2.1 + 1 = g.2.1 := he'.2.2.1.symm.trans he'.2.2.2
            omega
          · apply Subtype.ext
            apply congrArg RectangleEdge.horizontal
            apply horizontalEdge_ext
            · exact he.1.trans he'.1.symm
            · apply Fin.ext
              exact he.2.2.2.trans he'.2.2.2.symm
      | vertical e' =>
          rw [rectangleDual_vertical_isLink_some_some_iff] at he'
          exfalso
          rcases he with ⟨hxf, hxg, hyf, hyg⟩ | ⟨hxg, hxf, hyg, hyf⟩ <;>
            rcases he' with ⟨hyf', hyg', hxf', hxg'⟩ |
              ⟨hyg', hyf', hxg', hxf'⟩
          all_goals
            have hxx : f.1.1 = g.1.1 := by rw [← hxf, ← hxg]
            have hyy : f.2.1 = g.2.1 := by rw [← hyf', ← hyg']
            omega
  | vertical e =>
      rw [rectangleDual_vertical_isLink_some_some_iff] at he
      cases e' with
      | horizontal e' =>
          rw [rectangleDual_horizontal_isLink_some_some_iff] at he'
          exfalso
          rcases he with ⟨hyf, hyg, hxf, hxg⟩ | ⟨hyg, hyf, hxg, hxf⟩ <;>
            rcases he' with ⟨hxf', hxg', hyf', hyg'⟩ |
              ⟨hxg', hxf', hyg', hyf'⟩
          all_goals
            have hxx : f.1.1 = g.1.1 := by rw [← hxf', ← hxg']
            have hyy : f.2.1 = g.2.1 := by rw [← hyf, ← hyg]
            omega
      | vertical e' =>
          rw [rectangleDual_vertical_isLink_some_some_iff] at he'
          rcases he with he | he <;> rcases he' with he' | he'
          · apply Subtype.ext
            apply congrArg RectangleEdge.vertical
            apply verticalEdge_ext
            · apply Fin.ext
              exact he.2.2.2.trans he'.2.2.2.symm
            · exact he.1.trans he'.1.symm
          · exfalso
            have hfg : f.1.1 + 1 = g.1.1 := he.2.2.1.symm.trans he.2.2.2
            have hgf : g.1.1 + 1 = f.1.1 := he'.2.2.1.symm.trans he'.2.2.2
            omega
          · exfalso
            have hgf : g.1.1 + 1 = f.1.1 := he.2.2.1.symm.trans he.2.2.2
            have hfg : f.1.1 + 1 = g.1.1 := he'.2.2.1.symm.trans he'.2.2.2
            omega
          · apply Subtype.ext
            apply congrArg RectangleEdge.vertical
            apply verticalEdge_ext
            · apply Fin.ext
              exact he.2.2.2.trans he'.2.2.2.symm
            · exact he.1.trans he'.1.symm

/-- Exact multiplicity of an edge between two bounded dual faces. -/
theorem rectangleDual_edgeMultiplicity_some_some
    {r s : ℕ} (f g : BoundedFace r s) :
    (rectangleDual r s).edgeMultiplicity (some f) (some g) =
      if Boundary.natManhattanDist (f.1.1, f.2.1) (g.1.1, g.2.1) = 1
      then 1 else 0 := by
  classical
  by_cases hdist :
      Boundary.natManhattanDist (f.1.1, f.2.1) (g.1.1, g.2.1) = 1
  · rw [if_pos hdist]
    letI : Subsingleton
        ((rectangleDual r s).LinkEdge (some f) (some g)) :=
      rectangleDual_linkEdge_some_some_subsingleton f g
    haveI : Nonempty ((rectangleDual r s).LinkEdge (some f) (some g)) := by
      rcases (rectangleDual_exists_isLink_some_some_iff f g).2 hdist with ⟨e, he⟩
      exact ⟨⟨e, he⟩⟩
    exact Nat.card_unique
  · rw [if_neg hdist]
    apply Finite.card_eq_zero_iff.mpr
    constructor
    intro e
    exact hdist ((rectangleDual_exists_isLink_some_some_iff f g).1 ⟨e.1, e.2⟩)

/-- The loop-free adjacency multiplicity on bounded dual faces is precisely
the square-lattice adjacency indicator. -/
theorem rectangleDual_adjacencyMultiplicity_some_some
    {r s : ℕ} (f g : BoundedFace r s) :
    (rectangleDual r s).adjacencyMultiplicity (some f) (some g) =
      if Boundary.natManhattanDist (f.1.1, f.2.1) (g.1.1, g.2.1) = 1
      then 1 else 0 := by
  classical
  by_cases hfg : f = g
  · subst g
    simp [Boundary.natManhattanDist]
  · rw [(rectangleDual r s).adjacencyMultiplicity_of_ne (by simpa using hfg),
      rectangleDual_edgeMultiplicity_some_some]

/-- Edge labels incident with a displayed vertex, expressed directly as
membership in the unordered endpoint pair. -/
abbrev IncidentLabel {V E : Type*} (G : LabeledMultigraph V E) (u : V) :=
  {e : E // u ∈ G.ends e}

private theorem otherEndpoint_unique {V E : Type*}
    (G : LabeledMultigraph V E) {e : E} {u v w : V}
    (hv : G.IsLink e u v) (hw : G.IsLink e u w) : v = w := by
  have h : s(u, v) = s(u, w) := hv.symm.trans hw
  rcases Sym2.eq_iff.mp h with ⟨_, hvw⟩ | ⟨huw, hvu⟩
  · exact hvw
  · exact hvu.trans huw

/-- Summing link-label types over the other endpoint counts incident labels
once. -/
noncomputable def sigmaLinkEdgeEquivIncidentLabel {V E : Type*}
    (G : LabeledMultigraph V E) (u : V) :
    (Σ v, G.LinkEdge u v) ≃ IncidentLabel G u :=
  Equiv.ofBijective
    (fun x => ⟨x.2.1, by
      rw [x.2.2]
      exact Sym2.mem_mk_left u x.1⟩)
    ⟨by
      rintro ⟨v, ⟨e, he⟩⟩ ⟨w, ⟨e', he'⟩⟩ h
      have heq : e = e' := congrArg Subtype.val h
      subst e'
      have hvw : v = w := otherEndpoint_unique G he he'
      subst w
      rfl,
    by
      rintro ⟨e, he⟩
      rcases Sym2.mem_iff_exists.mp he with ⟨v, hv⟩
      refine ⟨⟨v, ⟨e, hv⟩⟩, ?_⟩
      apply Subtype.ext
      rfl⟩

/-- For a loopless labelled multigraph, the Laplacian degree is the number
of incident labels. -/
theorem degree_eq_natCard_incidentLabel {V E : Type*}
    [Fintype V] [Finite E] (G : LabeledMultigraph V E)
    (hloop : ∀ e, ¬G.IsLoop e) (u : V) :
    G.degree u = Nat.card (IncidentLabel G u) := by
  classical
  calc
    G.degree u = ∑ v, G.edgeMultiplicity u v := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases huv : u = v
      · subst v
        rw [G.adjacencyMultiplicity_self]
        apply Eq.symm
        apply Finite.card_eq_zero_iff.mpr
        constructor
        intro e
        exact hloop e.1 ((G.isLoop_iff_exists_isLoopAt e.1).2 ⟨u, e.2⟩)
      · exact G.adjacencyMultiplicity_of_ne huv
    _ = ∑ v, Nat.card (G.LinkEdge u v) := rfl
    _ = Nat.card (Σ v, G.LinkEdge u v) := Nat.card_sigma.symm
    _ = Nat.card (IncidentLabel G u) :=
      Nat.card_congr (sigmaLinkEdgeEquivIncidentLabel G u)

/-- The four sides of a bounded square face. -/
inductive FaceSide
  | south | north | west | east
deriving DecidableEq, Fintype

/-- The primal edge label along a specified side of a bounded face. -/
def faceSideEdge {R S : ℕ} (f : BoundedFace (R + 1) (S + 1)) :
    FaceSide → RectangleEdge (R + 1) (S + 1)
  | .south => .horizontal
      ⟨f.1, ⟨f.2.1, by have := f.2.2; omega⟩⟩
  | .north => .horizontal
      ⟨f.1, ⟨f.2.1 + 1, by have := f.2.2; omega⟩⟩
  | .west => .vertical
      ⟨⟨f.1.1, by have := f.1.2; omega⟩, f.2⟩
  | .east => .vertical
      ⟨⟨f.1.1 + 1, by have := f.1.2; omega⟩, f.2⟩

theorem faceSideEdge_incident {R S : ℕ}
    (f : BoundedFace (R + 1) (S + 1)) (d : FaceSide) :
    some f ∈ (rectangleDual (R + 1) (S + 1)).ends (faceSideEdge f d) := by
  cases d with
  | south =>
      rw [faceSideEdge, rectangleDual_horizontal_ends, Sym2.mem_iff]
      right
      simp [horizontalAbove]
  | north =>
      rw [faceSideEdge, rectangleDual_horizontal_ends, Sym2.mem_iff]
      left
      simp [horizontalBelow]
  | west =>
      rw [faceSideEdge, rectangleDual_vertical_ends, Sym2.mem_iff]
      right
      simp [verticalRight]
  | east =>
      rw [faceSideEdge, rectangleDual_vertical_ends, Sym2.mem_iff]
      left
      simp [verticalLeft]

theorem faceSideEdge_injective {R S : ℕ}
    (f : BoundedFace (R + 1) (S + 1)) :
    Function.Injective (faceSideEdge f) := by
  intro d d' h
  cases d <;> cases d' <;> try rfl
  all_goals
    exfalso
    simp [faceSideEdge, Fin.ext_iff] at h

theorem faceSideEdge_surjective_incident {R S : ℕ}
    (f : BoundedFace (R + 1) (S + 1))
    (e : IncidentLabel (rectangleDual (R + 1) (S + 1)) (some f)) :
    ∃ d, faceSideEdge f d = e.1 := by
  rcases e with ⟨e, he⟩
  cases e with
  | horizontal e =>
      change some f ∈ s(horizontalBelow e, horizontalAbove e) at he
      rw [Sym2.mem_iff] at he
      rcases he with hbelow | habove
      · by_cases hy0 : e.y.1 = 0
        · rw [horizontalBelow, dif_pos hy0] at hbelow
          cases hbelow
        · rw [horizontalBelow, dif_neg hy0] at hbelow
          have hface := Option.some_injective _ hbelow
          refine ⟨.north, congrArg RectangleEdge.horizontal ?_⟩
          apply horizontalEdge_ext
          · exact congrArg Prod.fst hface
          · apply Fin.ext
            change f.2.1 + 1 = e.y.1
            have h := congrArg (fun p => p.2.1) hface
            have hypos : 0 < e.y.1 := Nat.pos_of_ne_zero hy0
            dsimp only at h
            omega
      · by_cases hytop : e.y.1 + 1 < S + 1
        · rw [horizontalAbove, dif_pos hytop] at habove
          have hface := Option.some_injective _ habove
          refine ⟨.south, congrArg RectangleEdge.horizontal ?_⟩
          apply horizontalEdge_ext
          · exact congrArg Prod.fst hface
          · apply Fin.ext
            exact congrArg (fun p => p.2.1) hface
        · rw [horizontalAbove, dif_neg hytop] at habove
          cases habove
  | vertical e =>
      change some f ∈ s(verticalLeft e, verticalRight e) at he
      rw [Sym2.mem_iff] at he
      rcases he with hleft | hright
      · by_cases hx0 : e.x.1 = 0
        · rw [verticalLeft, dif_pos hx0] at hleft
          cases hleft
        · rw [verticalLeft, dif_neg hx0] at hleft
          have hface := Option.some_injective _ hleft
          refine ⟨.east, congrArg RectangleEdge.vertical ?_⟩
          apply verticalEdge_ext
          · apply Fin.ext
            change f.1.1 + 1 = e.x.1
            have h := congrArg (fun p => p.1.1) hface
            have hxpos : 0 < e.x.1 := Nat.pos_of_ne_zero hx0
            dsimp only at h
            omega
          · exact congrArg Prod.snd hface
      · by_cases hxright : e.x.1 + 1 < R + 1
        · rw [verticalRight, dif_pos hxright] at hright
          have hface := Option.some_injective _ hright
          refine ⟨.west, congrArg RectangleEdge.vertical ?_⟩
          apply verticalEdge_ext
          · apply Fin.ext
            exact congrArg (fun p => p.1.1) hface
          · exact congrArg Prod.snd hface
        · rw [verticalRight, dif_neg hxright] at hright
          cases hright

/-- The four side labels give an exact enumeration of all labels incident
with a bounded dual face. -/
noncomputable def faceSideEquivIncidentLabel {R S : ℕ}
    (f : BoundedFace (R + 1) (S + 1)) :
    FaceSide ≃ IncidentLabel (rectangleDual (R + 1) (S + 1)) (some f) :=
  Equiv.ofBijective
    (fun d => ⟨faceSideEdge f d, faceSideEdge_incident f d⟩)
    ⟨fun _ _ h => faceSideEdge_injective f (congrArg Subtype.val h),
      fun e => by
        rcases faceSideEdge_surjective_incident f e with ⟨d, hd⟩
        exact ⟨d, Subtype.ext hd⟩⟩

@[simp] theorem natCard_faceSide : Nat.card FaceSide = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- Every bounded face of a nondegenerate explicit rectangle has dual degree
four, including boundary faces (whose missing bounded neighbours are replaced
by parallel labels to the exterior). -/
theorem rectangleDual_degree_some {R S : ℕ}
    (f : BoundedFace (R + 1) (S + 1)) :
    (rectangleDual (R + 1) (S + 1)).degree (some f) = 4 := by
  have hR : 2 ≤ R + 1 := by have := f.1.2; omega
  have hS : 2 ≤ S + 1 := by have := f.2.2; omega
  rw [degree_eq_natCard_incidentLabel _
    (rectangleDual_not_isLoop hR hS) (some f)]
  calc
    Nat.card (IncidentLabel (rectangleDual (R + 1) (S + 1)) (some f)) =
        Nat.card FaceSide :=
      Nat.card_congr (faceSideEquivIncidentLabel f).symm
    _ = 4 := natCard_faceSide

/-- The exterior-rooted integer cofactor, transported to natural face
indices. -/
noncomputable def rectangleDualFaceLaplacianInt (R S : ℕ) :
    Matrix {z // z ∈ Boundary.faceIndices R S}
      {z // z ∈ Boundary.faceIndices R S} ℤ :=
  Matrix.reindex (dualAwayExteriorEquivFaceIndices R S)
    (dualAwayExteriorEquivFaceIndices R S)
    ((rectangleDual (R + 1) (S + 1)).reducedLaplacian ℤ none)

/-- Entrywise identification of the explicit dual cofactor with `4I-A` over
the integers. -/
theorem rectangleDualFaceLaplacianInt_apply (R S : ℕ)
    (z w : {p // p ∈ Boundary.faceIndices R S}) :
    rectangleDualFaceLaplacianInt R S z w =
      (if z = w then 4 else 0) -
        (if Boundary.natManhattanDist z.1 w.1 = 1 then 1 else 0) := by
  classical
  let e := dualAwayExteriorEquivFaceIndices R S
  let u := e.symm z
  let v := e.symm w
  have huSome : ∃ f : BoundedFace (R + 1) (S + 1), u.1 = some f := by
    cases hu : u.1 with
    | none => exact (u.2 hu).elim
    | some f => exact ⟨f, rfl⟩
  have hvSome : ∃ g : BoundedFace (R + 1) (S + 1), v.1 = some g := by
    cases hv : v.1 with
    | none => exact (v.2 hv).elim
    | some g => exact ⟨g, rfl⟩
  rcases huSome with ⟨f, huf⟩
  rcases hvSome with ⟨g, hvg⟩
  have hawayU : awayNoneEquiv (BoundedFace (R + 1) (S + 1)) u = f := by
    apply Option.some_injective
    exact (some_awayNoneEquiv _ u).trans huf
  have hawayV : awayNoneEquiv (BoundedFace (R + 1) (S + 1)) v = g := by
    apply Option.some_injective
    exact (some_awayNoneEquiv _ v).trans hvg
  have hcoordU : (f.1.1, f.2.1) = z.1 := by
    have h := congrArg Subtype.val (e.apply_symm_apply z)
    change
      (boundedFaceEquivFaceIndices R S
        (awayNoneEquiv (BoundedFace (R + 1) (S + 1)) u)).1 = z.1 at h
    rw [hawayU] at h
    exact h
  have hcoordV : (g.1.1, g.2.1) = w.1 := by
    have h := congrArg Subtype.val (e.apply_symm_apply w)
    change
      (boundedFaceEquivFaceIndices R S
        (awayNoneEquiv (BoundedFace (R + 1) (S + 1)) v)).1 = w.1 at h
    rw [hawayV] at h
    exact h
  have huv_iff : u = v ↔ z = w := by
    constructor
    · intro huv
      exact e.symm.injective huv
    · intro hzw
      exact congrArg e.symm hzw
  rw [rectangleDualFaceLaplacianInt, Matrix.reindex_apply]
  change (rectangleDual (R + 1) (S + 1)).laplacian ℤ u.1 v.1 = _
  rw [(rectangleDual (R + 1) (S + 1)).laplacian_apply_eq_diagonal_sub]
  rw [huf, hvg, rectangleDual_degree_some,
    rectangleDual_adjacencyMultiplicity_some_some]
  simp only [Option.some.injEq]
  have hfg_iff : f = g ↔ z = w := (show f = g ↔ u = v by
    constructor
    · intro hfg
      apply Subtype.ext
      simpa [huf, hvg] using congrArg some hfg
    · intro huv
      exact Option.some_injective _ (huf.symm.trans
        ((congrArg Subtype.val huv).trans hvg))).trans huv_iff
  rw [hcoordU, hcoordV]
  by_cases hzw : z = w
  · simp [hzw, hfg_iff.mpr hzw]
  · have hfg : f ≠ g := fun h => hzw (hfg_iff.mp h)
    simp [hzw, hfg]

/-- Casting the reindexed integer dual cofactor to the reals gives exactly
the matrix used by the boundary determinant series. -/
theorem map_rectangleDualFaceLaplacianInt (R S : ℕ) :
    (Int.castRingHom ℝ).mapMatrix (rectangleDualFaceLaplacianInt R S) =
      Boundary.fourIminusAdjacency (Boundary.faceIndices R S) := by
  classical
  ext z w
  rw [RingHom.mapMatrix_apply, Matrix.map_apply,
    rectangleDualFaceLaplacianInt_apply,
    Boundary.fourIminusAdjacency_apply]
  by_cases hzw : z = w <;>
    by_cases hadj : Boundary.natManhattanDist z.1 w.1 = 1 <;>
    simp [hzw, hadj]

/-- Determinant form of the full rectangular dual cofactor identification. -/
theorem det_rectangleDual_reducedLaplacian_eq_fourIminusAdjacency
    (R S : ℕ) :
    ((Matrix.det ((rectangleDual (R + 1) (S + 1)).reducedLaplacian ℤ none) : ℤ) : ℝ) =
      Matrix.det
        (Boundary.fourIminusAdjacency (Boundary.faceIndices R S)) := by
  classical
  let e := dualAwayExteriorEquivFaceIndices R S
  calc
    ((Matrix.det ((rectangleDual (R + 1) (S + 1)).reducedLaplacian ℤ none) : ℤ) : ℝ) =
        ((Int.castRingHom ℝ).mapMatrix
          ((rectangleDual (R + 1) (S + 1)).reducedLaplacian ℤ none)).det :=
      RingHom.map_det (Int.castRingHom ℝ) _
    _ = ((Int.castRingHom ℝ).mapMatrix
          (rectangleDualFaceLaplacianInt R S)).det := by
      have hdet := Matrix.det_reindex_self e
        ((rectangleDual (R + 1) (S + 1)).reducedLaplacian ℤ none)
      have hdet' : Matrix.det (rectangleDualFaceLaplacianInt R S) =
          Matrix.det
            ((rectangleDual (R + 1) (S + 1)).reducedLaplacian ℤ none) := by
        simp only [rectangleDualFaceLaplacianInt]
        exact hdet
      rw [← RingHom.map_det (Int.castRingHom ℝ),
        ← RingHom.map_det (Int.castRingHom ℝ), hdet']
    _ = Matrix.det
          (Boundary.fourIminusAdjacency (Boundary.faceIndices R S)) := by
      rw [map_rectangleDualFaceLaplacianInt]

/-- The full rectangle determinant follows from the labelled Matrix--Tree
cofactor interface once its spanning trees have been identified
with the explicit dual spanning trees. -/
theorem rectangleDet_of_treeEquiv
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    (R S : ℕ)
    (treeEquiv :
      {T : SimpleGraph {p : Point // p ∈ rectangle 0 0 (R + 1) (S + 1)} //
          T ≤ inducedGrid (rectangle 0 0 (R + 1) (S + 1)) ∧ T.IsTree} ≃
        (rectangleDual (R + 1) (S + 1)).SpanningTree) :
    (tauRect (R + 1) (S + 1) : ℝ) =
      Matrix.det
        (Boundary.fourIminusAdjacency (Boundary.faceIndices R S)) := by
  classical
  have hcount : tauRect (R + 1) (S + 1) =
      (rectangleDual (R + 1) (S + 1)).spanningTreeCount := by
    unfold tauRect tau treeCount LabeledMultigraph.spanningTreeCount
    exact Nat.card_congr treeEquiv
  have hcofactor :
      ((rectangleDual (R + 1) (S + 1)).spanningTreeCount : ℤ) =
        Matrix.det
          ((rectangleDual (R + 1) (S + 1)).reducedLaplacian ℤ none) :=
    hMatrixTree (RectangleDualVertex (R + 1) (S + 1))
      (RectangleEdge (R + 1) (S + 1))
      (rectangleDual (R + 1) (S + 1))
      (none : RectangleDualVertex (R + 1) (S + 1))
  rw [hcount]
  calc
    ((rectangleDual (R + 1) (S + 1)).spanningTreeCount : ℝ) =
        ((Matrix.det
          ((rectangleDual (R + 1) (S + 1)).reducedLaplacian ℤ none) : ℤ) : ℝ) := by
      exact_mod_cast hcofactor
    _ = Matrix.det
          (Boundary.fourIminusAdjacency (Boundary.faceIndices R S)) :=
      det_rectangleDual_reducedLaplacian_eq_fourIminusAdjacency R S

noncomputable section BoundaryContraction

/-- The exact simple spanning-tree type counted by `treeCount`. -/
abbrev SimpleSpanningTreeType {V : Type*} (G : SimpleGraph V) :=
  {T : SimpleGraph V // T ≤ G ∧ T.IsTree}

/-- The natural-coordinate boundary vacancy set used in the determinant
identity. -/
abbrev canonicalBoundaryNaturalVacancies (R S : ℕ) (A : Finset Point) :=
  Boundary.boundaryVacancies R S (Boundary.encodedVacancies R S A)

/-- Dual labels contracted after deleting the canonical boundary vacancies. -/
def canonicalBoundaryDualEdges (R S : ℕ) (A : Finset Point) :
    Finset (RectangleEdge (R + 1) (S + 1)) :=
  vacancyDualEdges (canonicalBoundaryPrimal R S A)

/-- The explicit dual after contracting every label incident with a deleted
boundary-vacancy vertex. -/
def canonicalBoundaryContractedDual (R S : ℕ) (A : Finset Point) :=
  (rectangleDual (R + 1) (S + 1)).contract
    (canonicalBoundaryDualEdges R S A)

/-- Vertex type of the contracted dual. -/
abbrev CanonicalBoundaryContractedVertex (R S : ℕ) (A : Finset Point) :=
  ((rectangleDual (R + 1) (S + 1)).simpleGraphOn
    (canonicalBoundaryDualEdges R S A :
      Set (RectangleEdge (R + 1) (S + 1)))).ConnectedComponent

/-- The component containing the exterior face is the contraction root. -/
def canonicalBoundaryContractionRoot (R S : ℕ) (A : Finset Point) :
    CanonicalBoundaryContractedVertex R S A :=
  (rectangleDual (R + 1) (S + 1)).contractionMap
    (canonicalBoundaryDualEdges R S A) none

/-- Remaining unmarked bounded faces after the boundary vacancies are wired
to the exterior. -/
abbrev CanonicalBoundaryUnmarkedFace (R S : ℕ) (A : Finset Point) :=
  {z // z ∈ Boundary.unmarkedFaces R S
    (canonicalBoundaryNaturalVacancies R S A)}

noncomputable local instance canonicalBoundaryContractedVertexFintype
    (R S : ℕ) (A : Finset Point) :
    Fintype (CanonicalBoundaryContractedVertex R S A) := by
  classical
  exact SimpleGraph.instFintypeConnectedComponent _

noncomputable local instance canonicalBoundaryContractedVertexDecidableEq
    (R S : ℕ) (A : Finset Point) :
    DecidableEq (CanonicalBoundaryContractedVertex R S A) :=
  Classical.decEq _

/-- Explicit finite geometric presentation of the boundary contraction.

This contains no determinant or tree-count equation.  Its vertex equivalence
says that the exterior/marked component is one root and every other component
is one unmarked face; the last two fields record the local labelled incidence
under that equivalence. -/
structure BoundaryContractionPresentation (R S : ℕ) (A : Finset Point) where
  componentEquiv : CanonicalBoundaryContractedVertex R S A ≃
    Option (CanonicalBoundaryUnmarkedFace R S A)
  root_eq : componentEquiv (canonicalBoundaryContractionRoot R S A) = none
  degree_face : ∀ z : CanonicalBoundaryUnmarkedFace R S A,
    (canonicalBoundaryContractedDual R S A).degree
      (componentEquiv.symm (some z)) = 4
  adjacency_face : ∀ z w : CanonicalBoundaryUnmarkedFace R S A,
    (canonicalBoundaryContractedDual R S A).adjacencyMultiplicity
      (componentEquiv.symm (some z)) (componentEquiv.symm (some w)) =
        if Boundary.natManhattanDist z.1 w.1 = 1 then 1 else 0

/-- The exact remaining planar residual: complementing primal tree labels
gives the full dual tree, and after deletion gives a tree of the contracted
dual, together with the explicit contraction presentation above. -/
structure BoundaryPlanarTreeComplement (R S : ℕ) (A : Finset Point) where
  rectangleTreeEquiv :
    SimpleSpanningTreeType
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1))) ≃
      (rectangleDual (R + 1) (S + 1)).SpanningTree
  vacancyTreeEquiv :
    SimpleSpanningTreeType
      (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A)) ≃
      (canonicalBoundaryContractedDual R S A).SpanningTree
  contraction : BoundaryContractionPresentation R S A

/-- Restrict a component equivalence sending `root` to `none` to the
non-root / non-exterior subtypes. -/
def awayRootEquivOfOption {C U : Type*} (e : C ≃ Option U) (root : C)
    (hroot : e root = none) : {c : C // c ≠ root} ≃ U :=
  (e.subtypeEquiv fun c => by
    simpa [hroot] using
      (e.injective.ne_iff : e c ≠ e root ↔ c ≠ root).symm).trans
      (awayNoneEquiv U)

theorem option_eq_some_awayRootEquivOfOption {C U : Type*}
    (e : C ≃ Option U) (root : C) (hroot : e root = none)
    (c : {c : C // c ≠ root}) :
    e c.1 = some (awayRootEquivOfOption e root hroot c) := by
  classical
  exact (some_awayNoneEquiv U
    ((e.subtypeEquiv fun c => by
      simpa [hroot] using
        (e.injective.ne_iff : e c ≠ e root ↔ c ≠ root).symm) c)).symm

/-- The contracted cofactor transported to unmarked face indices. -/
def canonicalBoundaryFaceLaplacianInt (R S : ℕ) (A : Finset Point)
    (p : BoundaryContractionPresentation R S A) :
    Matrix (CanonicalBoundaryUnmarkedFace R S A)
      (CanonicalBoundaryUnmarkedFace R S A) ℤ :=
  let e := awayRootEquivOfOption p.componentEquiv
    (canonicalBoundaryContractionRoot R S A) p.root_eq
  Matrix.reindex e e
    ((canonicalBoundaryContractedDual R S A).reducedLaplacian ℤ
      (canonicalBoundaryContractionRoot R S A))

/-- Entrywise cofactor identification supplied by the explicit contraction
presentation. -/
theorem canonicalBoundaryFaceLaplacianInt_apply
    (R S : ℕ) (A : Finset Point)
    (p : BoundaryContractionPresentation R S A)
    (z w : CanonicalBoundaryUnmarkedFace R S A) :
    canonicalBoundaryFaceLaplacianInt R S A p z w =
      (if z = w then 4 else 0) -
        (if Boundary.natManhattanDist z.1 w.1 = 1 then 1 else 0) := by
  classical
  let root := canonicalBoundaryContractionRoot R S A
  let e := awayRootEquivOfOption p.componentEquiv root p.root_eq
  let u := e.symm z
  let v := e.symm w
  have hcomponentU : p.componentEquiv u.1 = some z := by
    calc
      p.componentEquiv u.1 = some (e u) :=
        option_eq_some_awayRootEquivOfOption
          p.componentEquiv root p.root_eq u
      _ = some z := congrArg some (e.apply_symm_apply z)
  have hcomponentV : p.componentEquiv v.1 = some w := by
    calc
      p.componentEquiv v.1 = some (e v) :=
        option_eq_some_awayRootEquivOfOption
          p.componentEquiv root p.root_eq v
      _ = some w := congrArg some (e.apply_symm_apply w)
  have hu : u.1 = p.componentEquiv.symm (some z) := by
    apply p.componentEquiv.injective
    rw [hcomponentU, p.componentEquiv.apply_symm_apply]
  have hv : v.1 = p.componentEquiv.symm (some w) := by
    apply p.componentEquiv.injective
    rw [hcomponentV, p.componentEquiv.apply_symm_apply]
  have hu' :
      ((awayRootEquivOfOption p.componentEquiv
        (canonicalBoundaryContractionRoot R S A) p.root_eq).symm z).1 =
          p.componentEquiv.symm (some z) := by
    simpa [u, e, root] using hu
  have hv' :
      ((awayRootEquivOfOption p.componentEquiv
        (canonicalBoundaryContractionRoot R S A) p.root_eq).symm w).1 =
          p.componentEquiv.symm (some w) := by
    simpa [v, e, root] using hv
  rw [canonicalBoundaryFaceLaplacianInt, Matrix.reindex_apply]
  simp only [Matrix.submatrix_apply, LabeledMultigraph.reducedLaplacian_apply]
  rw [(canonicalBoundaryContractedDual R S A).laplacian_apply_eq_diagonal_sub]
  rw [hu', hv', p.degree_face, p.adjacency_face]
  by_cases hzw : z = w
  · subst w
    simp
  · have hcomp : p.componentEquiv.symm (some z) ≠
        p.componentEquiv.symm (some w) := by
      intro h
      apply hzw
      exact Option.some_injective _ (p.componentEquiv.symm.injective h)
    simp [hzw, hcomp]

theorem map_canonicalBoundaryFaceLaplacianInt
    (R S : ℕ) (A : Finset Point)
    (p : BoundaryContractionPresentation R S A) :
    (Int.castRingHom ℝ).mapMatrix
        (canonicalBoundaryFaceLaplacianInt R S A p) =
      Boundary.fourIminusAdjacency
        (Boundary.unmarkedFaces R S
          (canonicalBoundaryNaturalVacancies R S A)) := by
  classical
  ext z w
  rw [RingHom.mapMatrix_apply, Matrix.map_apply,
    canonicalBoundaryFaceLaplacianInt_apply,
    Boundary.fourIminusAdjacency_apply]
  by_cases hzw : z = w <;>
    by_cases hadj : Boundary.natManhattanDist z.1 w.1 = 1 <;>
    simp [hzw, hadj]

theorem det_canonicalBoundaryContractedDual_eq_fourIminusAdjacency
    (R S : ℕ) (A : Finset Point)
    (p : BoundaryContractionPresentation R S A) :
    ((Matrix.det ((canonicalBoundaryContractedDual R S A).reducedLaplacian ℤ
      (canonicalBoundaryContractionRoot R S A)) : ℤ) : ℝ) =
      Matrix.det (Boundary.fourIminusAdjacency
        (Boundary.unmarkedFaces R S
          (canonicalBoundaryNaturalVacancies R S A))) := by
  classical
  let e := awayRootEquivOfOption p.componentEquiv
    (canonicalBoundaryContractionRoot R S A) p.root_eq
  calc
    ((Matrix.det ((canonicalBoundaryContractedDual R S A).reducedLaplacian ℤ
        (canonicalBoundaryContractionRoot R S A)) : ℤ) : ℝ) =
        ((Int.castRingHom ℝ).mapMatrix
          ((canonicalBoundaryContractedDual R S A).reducedLaplacian ℤ
            (canonicalBoundaryContractionRoot R S A))).det :=
      RingHom.map_det (Int.castRingHom ℝ) _
    _ = ((Int.castRingHom ℝ).mapMatrix
          (canonicalBoundaryFaceLaplacianInt R S A p)).det := by
      have hdet := Matrix.det_reindex_self e
        ((canonicalBoundaryContractedDual R S A).reducedLaplacian ℤ
          (canonicalBoundaryContractionRoot R S A))
      have hdet' : Matrix.det (canonicalBoundaryFaceLaplacianInt R S A p) =
          Matrix.det ((canonicalBoundaryContractedDual R S A).reducedLaplacian ℤ
            (canonicalBoundaryContractionRoot R S A)) := by
        simp only [canonicalBoundaryFaceLaplacianInt]
        exact hdet
      rw [← RingHom.map_det (Int.castRingHom ℝ),
        ← RingHom.map_det (Int.castRingHom ℝ), hdet']
    _ = Matrix.det (Boundary.fourIminusAdjacency
          (Boundary.unmarkedFaces R S
            (canonicalBoundaryNaturalVacancies R S A))) := by
      rw [map_canonicalBoundaryFaceLaplacianInt]

theorem vacancyDet_of_treeEquiv_and_contraction
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    (R S : ℕ) (A : Finset Point)
    (treeEquiv :
      SimpleSpanningTreeType
        (inducedGrid (rectangle 0 0 (R + 1) (S + 1) \
          Boundary.canonicalBoundary R S A)) ≃
        (canonicalBoundaryContractedDual R S A).SpanningTree)
    (p : BoundaryContractionPresentation R S A) :
    (tau (rectangle 0 0 (R + 1) (S + 1) \
      Boundary.canonicalBoundary R S A) : ℝ) =
      Matrix.det (Boundary.fourIminusAdjacency
        (Boundary.unmarkedFaces R S
          (canonicalBoundaryNaturalVacancies R S A))) := by
  classical
  have hcount :
      tau (rectangle 0 0 (R + 1) (S + 1) \
        Boundary.canonicalBoundary R S A) =
        (canonicalBoundaryContractedDual R S A).spanningTreeCount := by
    unfold tau treeCount LabeledMultigraph.spanningTreeCount
    exact Nat.card_congr treeEquiv
  have hcofactor :
      ((canonicalBoundaryContractedDual R S A).spanningTreeCount : ℤ) =
        Matrix.det ((canonicalBoundaryContractedDual R S A).reducedLaplacian ℤ
          (canonicalBoundaryContractionRoot R S A)) :=
    hMatrixTree (CanonicalBoundaryContractedVertex R S A)
      ((rectangleDual (R + 1) (S + 1)).contractWithLoops
        (canonicalBoundaryDualEdges R S A)).NonLoopEdge
      (canonicalBoundaryContractedDual R S A)
      (canonicalBoundaryContractionRoot R S A)
  rw [hcount]
  calc
    ((canonicalBoundaryContractedDual R S A).spanningTreeCount : ℝ) =
        ((Matrix.det ((canonicalBoundaryContractedDual R S A).reducedLaplacian ℤ
          (canonicalBoundaryContractionRoot R S A)) : ℤ) : ℝ) := by
      exact_mod_cast hcofactor
    _ = Matrix.det (Boundary.fourIminusAdjacency
          (Boundary.unmarkedFaces R S
            (canonicalBoundaryNaturalVacancies R S A))) :=
      det_canonicalBoundaryContractedDual_eq_fourIminusAdjacency R S A p

/-- End-to-end constructor: the Matrix--Tree interface plus the exact finite
planar complement/contraction certificate yields both determinant identities
requested by the boundary series development. -/
theorem boundaryDualDeterminantIdentities_of_planarTreeComplement
    (hMatrixTree : LabeledMultigraphCofactorInput.{0, 0})
    (R S : ℕ) (A : Finset Point)
    (p : BoundaryPlanarTreeComplement R S A) :
    Boundary.DeterminantSeries.BoundaryDualDeterminantIdentities R S A where
  rectangleDet := rectangleDet_of_treeEquiv hMatrixTree R S
    p.rectangleTreeEquiv
  vacancyDet := vacancyDet_of_treeEquiv_and_contraction hMatrixTree R S A
    p.vacancyTreeEquiv p.contraction

end BoundaryContraction

end Dual
end SquareMaximality
