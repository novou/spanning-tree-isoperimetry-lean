import SquareMaximality.Boundary.Windows2D
import Mathlib.Combinatorics.SimpleGraph.Metric

set_option autoImplicit false

/-!
# The sliding-window injection

This file formalizes the rooted-forest construction in `general.tex`, lines
867--904.  A `BoundaryRootedRunForest` is a finite parent forest in the full
vertical-run graph: every parent edge is a graph edge, depth strictly decreases
toward roots, and every root is either marked or lies in boundary column `0`
or `R`.  This is a geometric/rooted strengthening of the manuscript hypothesis
that every connected component contains such a vertex.  It is the standard
finite rooted-spanning-forest certificate; no injection or cardinality bound is
included in it.

From such a forest we choose, for each internal component in each sliding
window, an eligible run of minimum depth.  Its parent must lie outside the
window.  The oriented parent edge (or the boundary location of a root) recovers
the window start, which makes the resulting map injective.
-/

namespace SquareMaximality

namespace Boundary

open Windows

abbrev RunVertex (R S : ℕ) (V : Finset LatticePoint) :=
  ↑(verticalRuns R S V)

abbrev WindowComponent (R S p : ℕ) (V : Finset LatticePoint) :=
  ↑(windowInternalComponents R S p V)

/-- A run is an admissible root when it is marked or lies in a boundary column. -/
def IsBoundaryRoot {R S : ℕ} {V : Finset LatticePoint}
    (v : RunVertex R S V) : Prop :=
  runMarked S (column S V v.1.1) v.1.2 ∨ v.1.1 = 0 ∨ v.1.1 = R

/-- The manuscript's component hypothesis: every run can reach a marked or
boundary-column run in the full run graph. -/
def BoundaryRootedComponents (R S : ℕ) (V : Finset LatticePoint) : Prop :=
  ∀ v : RunVertex R S V,
    ∃ r, (fullVerticalRunGraph R S V).Reachable v r ∧ IsBoundaryRoot r

/--
A rooted spanning-forest certificate for the finite full run graph.

Strict decrease of `depth` makes directed parent cycles impossible and forces
iteration of `parent` to reach a root.  Thus the data are stronger than merely
saying that every graph component has a suitable root, but are exactly the
finite rooted forest selected in the manuscript proof.
-/
structure BoundaryRootedRunForest (R S : ℕ) (V : Finset LatticePoint) where
  parent : RunVertex R S V → RunVertex R S V
  depth : RunVertex R S V → ℕ
  parent_step : ∀ v, parent v = v ∨ (fullVerticalRunGraph R S V).Adj (parent v) v
  depth_parent_lt : ∀ v, parent v ≠ v → depth (parent v) < depth v
  root_boundary : ∀ v, parent v = v → IsBoundaryRoot v

namespace BoundaryRootedRunForest

variable {R S : ℕ} {V : Finset LatticePoint}

/-- Every vertex reaches a geometrically admissible root in its graph component. -/
theorem reaches_boundary_root (F : BoundaryRootedRunForest R S V)
    (v : RunVertex R S V) :
    ∃ r, (fullVerticalRunGraph R S V).Reachable v r ∧ IsBoundaryRoot r := by
  induction h : F.depth v using Nat.strong_induction_on generalizing v with
  | h n ih =>
      by_cases hv : F.parent v = v
      · exact ⟨v, SimpleGraph.Reachable.refl v, F.root_boundary v hv⟩
      · have hlt : F.depth (F.parent v) < n := by
          rw [← h]
          exact F.depth_parent_lt v hv
        rcases ih (F.depth (F.parent v)) hlt (F.parent v) rfl with ⟨r, hr, hroot⟩
        have hedge : (fullVerticalRunGraph R S V).Adj v (F.parent v) :=
          (F.parent_step v).resolve_left hv |>.symm
        exact ⟨r, hedge.reachable.trans hr, hroot⟩

end BoundaryRootedRunForest

/-! ## Constructing the rooted forest from the component hypothesis -/

section ForestConstruction

variable {R S : ℕ} {V : Finset LatticePoint}

private noncomputable def boundaryRootCandidates (v : RunVertex R S V) :
    Finset (RunVertex R S V) := by
  classical
  exact Finset.univ.filter fun r =>
    (fullVerticalRunGraph R S V).Reachable v r ∧ IsBoundaryRoot r

private theorem boundaryRootCandidates_nonempty
    (hcomp : BoundaryRootedComponents R S V) (v : RunVertex R S V) :
    (boundaryRootCandidates v).Nonempty := by
  classical
  rcases hcomp v with ⟨r, hreach, hroot⟩
  exact ⟨r, by simp [boundaryRootCandidates, hreach, hroot]⟩

/-- A closest admissible root in the component of `v`. -/
private noncomputable def closestBoundaryRoot
    (hcomp : BoundaryRootedComponents R S V) (v : RunVertex R S V) :
    RunVertex R S V :=
  Classical.choose ((boundaryRootCandidates v).exists_min_image
    (fun r => (fullVerticalRunGraph R S V).dist v r)
    (boundaryRootCandidates_nonempty hcomp v))

private theorem closestBoundaryRoot_mem
    (hcomp : BoundaryRootedComponents R S V) (v : RunVertex R S V) :
    closestBoundaryRoot hcomp v ∈ boundaryRootCandidates v :=
  (Classical.choose_spec ((boundaryRootCandidates v).exists_min_image
    (fun r => (fullVerticalRunGraph R S V).dist v r)
    (boundaryRootCandidates_nonempty hcomp v))).1

private theorem closestBoundaryRoot_min
    (hcomp : BoundaryRootedComponents R S V) (v r : RunVertex R S V)
    (hr : r ∈ boundaryRootCandidates v) :
    (fullVerticalRunGraph R S V).dist v (closestBoundaryRoot hcomp v) ≤
      (fullVerticalRunGraph R S V).dist v r :=
  (Classical.choose_spec ((boundaryRootCandidates v).exists_min_image
    (fun r => (fullVerticalRunGraph R S V).dist v r)
    (boundaryRootCandidates_nonempty hcomp v))).2 r hr

private theorem closestBoundaryRoot_reachable
    (hcomp : BoundaryRootedComponents R S V) (v : RunVertex R S V) :
    (fullVerticalRunGraph R S V).Reachable v (closestBoundaryRoot hcomp v) := by
  have hmem := closestBoundaryRoot_mem hcomp v
  have hboth : (fullVerticalRunGraph R S V).Reachable v (closestBoundaryRoot hcomp v) ∧
      IsBoundaryRoot (closestBoundaryRoot hcomp v) := by
    simpa only [boundaryRootCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
      using hmem
  exact hboth.1

private theorem closestBoundaryRoot_isRoot
    (hcomp : BoundaryRootedComponents R S V) (v : RunVertex R S V) :
    IsBoundaryRoot (closestBoundaryRoot hcomp v) := by
  have hmem := closestBoundaryRoot_mem hcomp v
  have hboth : (fullVerticalRunGraph R S V).Reachable v (closestBoundaryRoot hcomp v) ∧
      IsBoundaryRoot (closestBoundaryRoot hcomp v) := by
    simpa only [boundaryRootCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
      using hmem
  exact hboth.2

private noncomputable def rootWalk
    (hcomp : BoundaryRootedComponents R S V) (v : RunVertex R S V) :
    (fullVerticalRunGraph R S V).Walk v (closestBoundaryRoot hcomp v) :=
  Classical.choose (closestBoundaryRoot_reachable hcomp v).exists_walk_length_eq_dist

private theorem rootWalk_length
    (hcomp : BoundaryRootedComponents R S V) (v : RunVertex R S V) :
    (rootWalk hcomp v).length =
      (fullVerticalRunGraph R S V).dist v (closestBoundaryRoot hcomp v) :=
  Classical.choose_spec (closestBoundaryRoot_reachable hcomp v).exists_walk_length_eq_dist

private theorem rootWalk_not_nil
    (hcomp : BoundaryRootedComponents R S V) {v : RunVertex R S V}
    (hv : ¬ IsBoundaryRoot v) : ¬ (rootWalk hcomp v).Nil := by
  have hne : v ≠ closestBoundaryRoot hcomp v := by
    intro h
    exact hv (h ▸ closestBoundaryRoot_isRoot hcomp v)
  have hpos := (closestBoundaryRoot_reachable hcomp v).pos_dist_of_ne hne
  rw [← rootWalk_length hcomp v] at hpos
  simpa [SimpleGraph.Walk.not_nil_iff_lt_length] using hpos

private noncomputable def forestParent
    (hcomp : BoundaryRootedComponents R S V) (v : RunVertex R S V) :
    RunVertex R S V := by
  classical
  exact if IsBoundaryRoot v then v else (rootWalk hcomp v).snd

private noncomputable def forestDepth
    (hcomp : BoundaryRootedComponents R S V) (v : RunVertex R S V) : ℕ :=
  (fullVerticalRunGraph R S V).dist v (closestBoundaryRoot hcomp v)

private theorem forestParent_step
    (hcomp : BoundaryRootedComponents R S V) (v : RunVertex R S V) :
    forestParent hcomp v = v ∨
      (fullVerticalRunGraph R S V).Adj (forestParent hcomp v) v := by
  classical
  by_cases hv : IsBoundaryRoot v
  · exact Or.inl (by simp [forestParent, hv])
  · right
    rw [forestParent, if_neg hv]
    exact (rootWalk hcomp v).adj_snd (rootWalk_not_nil hcomp hv) |>.symm

private theorem forestParent_ne_of_not_root
    (hcomp : BoundaryRootedComponents R S V) {v : RunVertex R S V}
    (hv : ¬ IsBoundaryRoot v) : forestParent hcomp v ≠ v := by
  intro h
  have hadj := (rootWalk hcomp v).adj_snd (rootWalk_not_nil hcomp hv)
  have hsnd : (rootWalk hcomp v).snd = v := by
    simpa [forestParent, hv] using h
  exact hadj.ne hsnd.symm

private theorem forestDepth_parent_lt
    (hcomp : BoundaryRootedComponents R S V) (v : RunVertex R S V)
    (hne : forestParent hcomp v ≠ v) :
    forestDepth hcomp (forestParent hcomp v) < forestDepth hcomp v := by
  classical
  have hv : ¬ IsBoundaryRoot v := by
    intro hv
    apply hne
    simp [forestParent, hv]
  have hp : forestParent hcomp v = (rootWalk hcomp v).snd := by
    simp [forestParent, hv]
  let r := closestBoundaryRoot hcomp v
  have htailReach : (fullVerticalRunGraph R S V).Reachable
      (forestParent hcomp v) r := by
    rw [hp]
    exact (rootWalk hcomp v).tail.reachable
  have hrCandidate : r ∈ boundaryRootCandidates (forestParent hcomp v) := by
    classical
    simp only [boundaryRootCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨htailReach, closestBoundaryRoot_isRoot hcomp v⟩
  have hmin := closestBoundaryRoot_min hcomp (forestParent hcomp v) r hrCandidate
  have hdistTail : (fullVerticalRunGraph R S V).dist (forestParent hcomp v) r ≤
      (rootWalk hcomp v).tail.length := by
    rw [hp]
    exact SimpleGraph.dist_le (rootWalk hcomp v).tail
  have hlength := (rootWalk hcomp v).length_tail_add_one (rootWalk_not_nil hcomp hv)
  rw [rootWalk_length hcomp v] at hlength
  dsimp only [forestDepth]
  exact lt_of_le_of_lt hmin (lt_of_le_of_lt hdistTail (by omega))

private theorem forestRoot_boundary
    (hcomp : BoundaryRootedComponents R S V) (v : RunVertex R S V)
    (hroot : forestParent hcomp v = v) : IsBoundaryRoot v := by
  classical
  by_contra hv
  exact forestParent_ne_of_not_root hcomp hv hroot

/-- Every component satisfying the manuscript's boundary-root condition admits
the rooted forest certificate used by the injection proof. -/
noncomputable def rootedRunForestOfComponents
    (hcomp : BoundaryRootedComponents R S V) : BoundaryRootedRunForest R S V where
  parent := forestParent hcomp
  depth := forestDepth hcomp
  parent_step := forestParent_step hcomp
  depth_parent_lt := forestDepth_parent_lt hcomp
  root_boundary := forestRoot_boundary hcomp

end ForestConstruction

/-! ## Interval-component lemmas -/

private theorem internalComponent_absorbs_right {L a y z : ℕ} {B : Finset ℕ}
    (hy : y ∈ intervalComponent L B a) (hyz : y ≤ z) (hzL : z ≤ L)
    (hsegment : Finset.Icc y z ⊆ B) :
    z ∈ intervalComponent L B a := by
  rw [mem_intervalComponent] at hy ⊢
  refine ⟨hy.1.trans hyz, hzL, ?_⟩
  intro t ht
  simp only [Finset.mem_Icc] at ht
  by_cases hty : t ≤ y
  · exact hy.2.2 (by simp only [Finset.mem_Icc]; omega)
  · exact hsegment (by simp only [Finset.mem_Icc]; omega)

private theorem internalComponent_absorbs_left {L a y z : ℕ} {B : Finset ℕ}
    (ha : a ∈ internalRunStarts L B) (hy : y ∈ intervalComponent L B a)
    (hzy : z ≤ y) (hsegment : Finset.Icc z y ⊆ B) :
    z ∈ intervalComponent L B a := by
  have hi := mem_internalRunStarts.mp ha
  have hy' := mem_intervalComponent.mp hy
  have haz : a ≤ z := by
    by_contra h
    have hpredBounds : z ≤ a - 1 ∧ a - 1 ≤ y := by omega
    exact hi.2.2.2.1 (hsegment (by
      simp only [Finset.mem_Icc]
      exact hpredBounds))
  exact intervalComponent_interval hy haz hzy

private theorem internalComponent_absorbs_interval {L a y z : ℕ} {B : Finset ℕ}
    (ha : a ∈ internalRunStarts L B) (hy : y ∈ intervalComponent L B a)
    (hzL : z ≤ L)
    (hforward : y ≤ z → Finset.Icc y z ⊆ B)
    (hbackward : z ≤ y → Finset.Icc z y ⊆ B) :
    z ∈ intervalComponent L B a := by
  rcases le_total y z with hyz | hzy
  · exact internalComponent_absorbs_right hy hyz hzL (hforward hyz)
  · exact internalComponent_absorbs_left ha hy hzy (hbackward hzy)

private theorem internalComponent_absorbs_adjacent {L a y z : ℕ} {B : Finset ℕ}
    (hB : B ⊆ line L) (ha : a ∈ internalRunStarts L B)
    (hy : y ∈ intervalComponent L B a) (hz : z ∈ B)
    (hnear : Nat.dist y z ≤ 1) :
    z ∈ intervalComponent L B a := by
  have hzL : z ≤ L := mem_line.mp (hB hz)
  apply internalComponent_absorbs_interval ha hy hzL
  · intro hyz t ht
    simp only [Finset.mem_Icc] at ht
    rcases eq_or_lt_of_le ht.2 with hty | hty
    · simpa [hty] using hz
    · have : t = y := by
        rw [Nat.dist_eq_sub_of_le hyz] at hnear
        omega
      simpa [this] using intervalComponent_subset_B hy
  · intro hzy t ht
    simp only [Finset.mem_Icc] at ht
    rcases eq_or_lt_of_le ht.2 with hty | hty
    · simpa [hty] using intervalComponent_subset_B hy
    · have : t = z := by
        rw [Nat.dist_eq_sub_of_le_right hzy] at hnear
        omega
      simpa [this] using hz

private theorem internalRunStarts_eq_of_components_meet {L a b z : ℕ} {B : Finset ℕ}
    (ha : a ∈ internalRunStarts L B) (hb : b ∈ internalRunStarts L B)
    (hza : z ∈ intervalComponent L B a) (hzb : z ∈ intervalComponent L B b) :
    a = b := by
  have hia := mem_internalRunStarts.mp ha
  have hib := mem_internalRunStarts.mp hb
  have hca := mem_intervalComponent.mp hza
  have hcb := mem_intervalComponent.mp hzb
  rcases le_total a b with hab | hba
  · by_contra hne
    have hpBounds : a ≤ b - 1 ∧ b - 1 ≤ z := by omega
    exact hib.2.2.2.1 (hca.2.2 (by
      simp only [Finset.mem_Icc]
      exact hpBounds))
  · by_contra hne
    have hpBounds : b ≤ a - 1 ∧ a - 1 ≤ z := by omega
    exact hia.2.2.2.1 (hcb.2.2 (by
      simp only [Finset.mem_Icc]
      exact hpBounds))

/-! ## Runs projected into a window -/

private theorem runPoint_mem_horizontalSection {R S p : ℕ} {V : Finset LatticePoint}
    {x : ℕ} (hx : x ∈ validWindowStarts R p) (v : RunVertex R S V)
    (hleft : x ≤ v.1.1) (hright : v.1.1 ≤ x + p) {y : ℕ}
    (hy : y ∈ intervalComponent S (column S V v.1.1) v.1.2) :
    y ∈ horizontalSection R S p V x := by
  have hxvalid := mem_validWindowStarts.mp hx
  have hycol := intervalComponent_subset_B hy
  have hycol' := mem_column.mp hycol
  refine mem_horizontalSection.mpr ⟨hycol'.1, ?_⟩
  exact mem_meetingWindowStarts.mpr
    ⟨hxvalid, v.1.1, mem_row.mpr ⟨hright.trans hxvalid, hycol'.2⟩,
      hleft, hright⟩

/-- A full vertical run meets a specified internal component of a horizontal window. -/
def RunMeetsWindowComponent {R S p : ℕ} {V : Finset LatticePoint}
    (d : WindowComponent R S p V) (v : RunVertex R S V) : Prop :=
  d.1.1 ≤ v.1.1 ∧ v.1.1 ≤ d.1.1 + p ∧
    ∃ y,
      y ∈ intervalComponent S (column S V v.1.1) v.1.2 ∧
      y ∈ intervalComponent S
        (horizontalSection R S p V d.1.1) d.1.2

private theorem entireRun_mem_windowComponent {R S p : ℕ} {V : Finset LatticePoint}
    {d : WindowComponent R S p V} {v : RunVertex R S V}
    (hmeet : RunMeetsWindowComponent d v) {z : ℕ}
    (hz : z ∈ intervalComponent S (column S V v.1.1) v.1.2) :
    z ∈ intervalComponent S (horizontalSection R S p V d.1.1) d.1.2 := by
  rcases hmeet.2.2 with ⟨y, hyrun, hycomp⟩
  have hd := Finset.mem_sigma.mp d.2
  have ha := hd.2
  have hx := hd.1
  have hzS := (mem_intervalComponent.mp hz).2.1
  apply internalComponent_absorbs_interval ha hycomp hzS
  · intro hyz t ht
    apply runPoint_mem_horizontalSection hx v hmeet.1 hmeet.2.1
    exact intervalComponent_interval hz
      ((mem_intervalComponent.mp hyrun).1.trans (Finset.mem_Icc.mp ht).1)
      (Finset.mem_Icc.mp ht).2
  · intro hzy t ht
    apply runPoint_mem_horizontalSection hx v hmeet.1 hmeet.2.1
    exact intervalComponent_interval hyrun
      ((mem_intervalComponent.mp hz).1.trans (Finset.mem_Icc.mp ht).1)
      (Finset.mem_Icc.mp ht).2

private theorem runMeetsWindowComponent_unmarked {R S p : ℕ}
    {V : Finset LatticePoint} {d : WindowComponent R S p V} {v : RunVertex R S V}
    (hmeet : RunMeetsWindowComponent d v) :
    ¬ runMarked S (column S V v.1.1) v.1.2 := by
  intro hmarked
  have hd := Finset.mem_sigma.mp d.2
  have hends := internal_component_avoids_endpoints hd.2
  rcases hmarked with hzero | htop
  · apply hends.1
    rw [← hzero]
    apply entireRun_mem_windowComponent hmeet
    exact intervalComponent_contains_start
      (mem_runStarts.mp (Finset.mem_sigma.mp v.2).2).1
      (mem_runStarts.mp (Finset.mem_sigma.mp v.2).2).2.1
  · exact hends.2 (entireRun_mem_windowComponent hmeet htop)

private theorem runGraph_adjacent_columns {R S : ℕ} {V : Finset LatticePoint}
    {u v : RunVertex R S V} (h : (fullVerticalRunGraph R S V).Adj u v) :
    Nat.dist u.1.1 v.1.1 = 1 := by
  rw [fullVerticalRunGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with huv | hvu
  · exact huv.1
  · simpa [Nat.dist_comm] using hvu.1

private theorem runGraph_adjacent_witnesses {R S : ℕ} {V : Finset LatticePoint}
    {u v : RunVertex R S V} (h : (fullVerticalRunGraph R S V).Adj u v) :
    ∃ yu ∈ intervalComponent S (column S V u.1.1) u.1.2,
      ∃ yv ∈ intervalComponent S (column S V v.1.1) v.1.2,
        Nat.dist yu yv ≤ 1 := by
  rw [fullVerticalRunGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with huv | hvu
  · exact huv.2
  · rcases hvu.2 with ⟨yv, hyv, yu, hyu, hdist⟩
    exact ⟨yu, hyu, yv, hyv, by simpa [Nat.dist_comm] using hdist⟩

private theorem parent_meets_of_inside {R S p : ℕ} {V : Finset LatticePoint}
    (F : BoundaryRootedRunForest R S V) {d : WindowComponent R S p V}
    {v : RunVertex R S V} (hv : RunMeetsWindowComponent d v)
    (hne : F.parent v ≠ v)
    (hleft : d.1.1 ≤ (F.parent v).1.1)
    (hright : (F.parent v).1.1 ≤ d.1.1 + p) :
    RunMeetsWindowComponent d (F.parent v) := by
  have hadj := (F.parent_step v).resolve_left hne
  rcases runGraph_adjacent_witnesses hadj with ⟨yu, hyu, yv, hyv, hdist⟩
  have hyvcomp := entireRun_mem_windowComponent hv hyv
  have hd := Finset.mem_sigma.mp d.2
  have hyuSection := runPoint_mem_horizontalSection hd.1 (F.parent v) hleft hright hyu
  have hyucomp := internalComponent_absorbs_adjacent
    (horizontalSection_subset_line R S p V d.1.1) hd.2 hyvcomp hyuSection
      (by simpa [Nat.dist_comm] using hdist)
  exact ⟨hleft, hright, yu, hyu, hyucomp⟩

/-! ## Eligible runs and the minimum-depth choice -/

/-- Eligible representatives for one window component. -/
noncomputable def eligibleRuns {R S p : ℕ} {V : Finset LatticePoint}
    (d : WindowComponent R S p V) : Finset (RunVertex R S V) := by
  classical
  exact Finset.univ.filter fun v => RunMeetsWindowComponent d v

@[simp] theorem mem_eligibleRuns {R S p : ℕ} {V : Finset LatticePoint}
    {d : WindowComponent R S p V} {v : RunVertex R S V} :
    v ∈ eligibleRuns d ↔ RunMeetsWindowComponent d v := by
  classical
  simp [eligibleRuns]

private theorem eligibleRuns_nonempty {R S p : ℕ} {V : Finset LatticePoint}
    (d : WindowComponent R S p V) : (eligibleRuns d).Nonempty := by
  have hd := Finset.mem_sigma.mp d.2
  have hi := mem_internalRunStarts.mp hd.2
  have hsection := mem_horizontalSection.mp hi.2.2.1
  rcases mem_meetingWindowStarts.mp hsection.2 with
    ⟨hxvalid, c, hcRow, hxc, hcxp⟩
  have hcV := (mem_row.mp hcRow).2
  have haColumn : d.1.2 ∈ column S V c :=
    mem_column.mpr ⟨hi.1, hcV⟩
  have hpredColumn : d.1.2 - 1 ∉ column S V c := by
    intro hpred
    have hpred' := mem_column.mp hpred
    apply hi.2.2.2.1
    refine mem_horizontalSection.mpr ⟨hpred'.1, ?_⟩
    exact mem_meetingWindowStarts.mpr
      ⟨hxvalid, c, mem_row.mpr ⟨hcxp.trans hxvalid, hpred'.2⟩, hxc, hcxp⟩
  have hrunStart : d.1.2 ∈ runStarts S (column S V c) := by
    exact mem_runStarts.mpr
      ⟨hi.1, haColumn, Or.inr hpredColumn⟩
  have hcLine : c ∈ line R := mem_line.mpr (hcxp.trans hxvalid)
  let v : RunVertex R S V := ⟨⟨c, d.1.2⟩, Finset.mem_sigma.mpr ⟨hcLine, hrunStart⟩⟩
  have haRun : d.1.2 ∈ intervalComponent S (column S V c) d.1.2 :=
    intervalComponent_contains_start hi.1 haColumn
  refine ⟨v, mem_eligibleRuns.mpr ⟨hxc, hcxp, d.1.2, haRun, ?_⟩⟩
  exact intervalComponent_contains_start hi.1 hi.2.2.1

/-- The eligible run of minimum forest depth. -/
noncomputable def selectedRun {R S p : ℕ} {V : Finset LatticePoint}
    (F : BoundaryRootedRunForest R S V) (d : WindowComponent R S p V) :
    RunVertex R S V :=
  Classical.choose ((eligibleRuns d).exists_min_image F.depth (eligibleRuns_nonempty d))

theorem selectedRun_mem {R S p : ℕ} {V : Finset LatticePoint}
    (F : BoundaryRootedRunForest R S V) (d : WindowComponent R S p V) :
    selectedRun F d ∈ eligibleRuns d :=
  (Classical.choose_spec
    ((eligibleRuns d).exists_min_image F.depth (eligibleRuns_nonempty d))).1

theorem selectedRun_min_depth {R S p : ℕ} {V : Finset LatticePoint}
    (F : BoundaryRootedRunForest R S V) (d : WindowComponent R S p V)
    {v : RunVertex R S V} (hv : v ∈ eligibleRuns d) :
    F.depth (selectedRun F d) ≤ F.depth v :=
  (Classical.choose_spec
    ((eligibleRuns d).exists_min_image F.depth (eligibleRuns_nonempty d))).2 v hv

theorem parent_selectedRun_outside {R S p : ℕ} {V : Finset LatticePoint}
    (F : BoundaryRootedRunForest R S V) (d : WindowComponent R S p V)
    (hne : F.parent (selectedRun F d) ≠ selectedRun F d) :
    (F.parent (selectedRun F d)).1.1 < d.1.1 ∨
      d.1.1 + p < (F.parent (selectedRun F d)).1.1 := by
  have hmeet := mem_eligibleRuns.mp (selectedRun_mem F d)
  by_contra hnot
  push Not at hnot
  have hparentMeet := parent_meets_of_inside F hmeet hne hnot.1 hnot.2
  have hparentEligible : F.parent (selectedRun F d) ∈ eligibleRuns d :=
    mem_eligibleRuns.mpr hparentMeet
  have hminimal := selectedRun_min_depth F d hparentEligible
  exact (not_le_of_gt (F.depth_parent_lt (selectedRun F d) hne)) hminimal

/-! ## Decoding the window and proving injectivity -/

/-- The window start determined by the chosen run and its oriented parent edge/root. -/
def decodedWindowStart {R S : ℕ} (p : ℕ) {V : Finset LatticePoint}
    (F : BoundaryRootedRunForest R S V) (v : RunVertex R S V) : ℕ :=
  if F.parent v = v then
    if v.1.1 = 0 then 0 else R - p
  else if (F.parent v).1.1 < v.1.1 then v.1.1 else v.1.1 - p

private theorem selectedRun_decodes_start {R S p : ℕ} {V : Finset LatticePoint}
    (F : BoundaryRootedRunForest R S V) (d : WindowComponent R S p V) :
    decodedWindowStart p F (selectedRun F d) = d.1.1 := by
  have hd := Finset.mem_sigma.mp d.2
  have hxvalid := mem_validWindowStarts.mp hd.1
  have hmeet := mem_eligibleRuns.mp (selectedRun_mem F d)
  have hwindowLeft := hmeet.1
  have hwindowRight := hmeet.2.1
  by_cases hroot : F.parent (selectedRun F d) = selectedRun F d
  · rw [decodedWindowStart, if_pos hroot]
    have hlocated := F.root_boundary (selectedRun F d) hroot
    have hunmarked := runMeetsWindowComponent_unmarked hmeet
    rcases hlocated with hmarked | hzero | hright
    · exact (hunmarked hmarked).elim
    · rw [if_pos hzero]
      omega
    · by_cases hzero : (selectedRun F d).1.1 = 0
      · rw [if_pos hzero]
        omega
      · rw [if_neg hzero]
        omega
  · rw [decodedWindowStart, if_neg hroot]
    have hout := parent_selectedRun_outside F d hroot
    have hdist := runGraph_adjacent_columns ((F.parent_step _).resolve_left hroot)
    by_cases hleft : (F.parent (selectedRun F d)).1.1 < (selectedRun F d).1.1
    · rw [if_pos hleft]
      rw [Nat.dist_eq_sub_of_le hleft.le] at hdist
      omega
    · rw [if_neg hleft]
      have hrightdir : (selectedRun F d).1.1 ≤
          (F.parent (selectedRun F d)).1.1 := Nat.le_of_not_gt hleft
      rw [Nat.dist_eq_sub_of_le_right hrightdir] at hdist
      omega

private theorem selectedRun_injective {R S p : ℕ} {V : Finset LatticePoint}
    (F : BoundaryRootedRunForest R S V) :
    Function.Injective (selectedRun F : WindowComponent R S p V → RunVertex R S V) := by
  intro d₁ d₂ hselected
  have hx : d₁.1.1 = d₂.1.1 := by
    rw [← selectedRun_decodes_start F d₁, ← selectedRun_decodes_start F d₂,
      hselected]
  have hm₁ := mem_eligibleRuns.mp (selectedRun_mem F d₁)
  have hm₂ := mem_eligibleRuns.mp (selectedRun_mem F d₂)
  rcases hm₁.2.2 with ⟨y₁, hy₁run, hy₁comp⟩
  rcases hm₂.2.2 with ⟨y₂, hy₂run, hy₂comp⟩
  have hy₂comp₁ : y₂ ∈
      intervalComponent S (horizontalSection R S p V d₁.1.1) d₁.1.2 := by
    have hm₁' : RunMeetsWindowComponent d₁ (selectedRun F d₂) := by
      rw [← hselected]
      exact hm₁
    exact entireRun_mem_windowComponent hm₁' hy₂run
  have ha : d₁.1.2 = d₂.1.2 := by
    have hd₁ := (Finset.mem_sigma.mp d₁.2).2
    have hd₂ := (Finset.mem_sigma.mp d₂.2).2
    rw [hx] at hy₂comp₁
    have hd₁' : d₁.1.2 ∈
        internalRunStarts S (horizontalSection R S p V d₂.1.1) := by
      simpa [hx] using hd₁
    exact internalRunStarts_eq_of_components_meet hd₁' hd₂ hy₂comp₁ hy₂comp
  apply Subtype.ext
  apply Sigma.ext hx
  simpa [hx] using ha

/-- The actual injection constructed from the rooted run forest. -/
noncomputable def slidingWindowEmbedding {R S p : ℕ} {V : Finset LatticePoint}
    (F : BoundaryRootedRunForest R S V) :
    WindowComponent R S p V ↪ ↑(unmarkedVerticalRuns R S V) where
  toFun d := by
    let v := selectedRun F d
    refine ⟨v.1, ?_⟩
    simp only [unmarkedVerticalRuns, Finset.mem_filter]
    exact ⟨v.2, runMeetsWindowComponent_unmarked (mem_eligibleRuns.mp (selectedRun_mem F d))⟩
  inj' := by
    intro d₁ d₂ h
    have hv : (selectedRun F d₁).1 = (selectedRun F d₂).1 :=
      congrArg (fun z : ↑(unmarkedVerticalRuns R S V) => z.1) h
    exact selectedRun_injective F (Subtype.ext hv)

/-- The rooted-forest construction discharges the sole predicate left in `Windows2D`. -/
theorem slidingWindowInjection_of_rootedForest {R S p : ℕ} {V : Finset LatticePoint}
    (F : BoundaryRootedRunForest R S V) :
    SlidingWindowInjection R S p V :=
  ⟨slidingWindowEmbedding F⟩

/-- The manuscript's component hypothesis alone therefore produces the
sliding-window injection. -/
theorem slidingWindowInjection_of_components {R S p : ℕ} {V : Finset LatticePoint}
    (hcomp : BoundaryRootedComponents R S V) :
    SlidingWindowInjection R S p V :=
  slidingWindowInjection_of_rootedForest (rootedRunForestOfComponents hcomp)

/-- Consequently, the manuscript's window-injection inequality holds. -/
theorem window_injection_inequality_of_rootedForest {R S p : ℕ}
    {V : Finset LatticePoint} (F : BoundaryRootedRunForest R S V) :
    (∑ x ∈ validWindowStarts R p,
        (internalRunStarts S (horizontalSection R S p V x)).card) ≤
      verticalInternalRunCount R S V :=
  window_injection_inequality R S p V (slidingWindowInjection_of_rootedForest F)

/-- Equation `window-injection`, now directly from the component hypothesis. -/
theorem window_injection_inequality_of_components {R S p : ℕ}
    {V : Finset LatticePoint} (hcomp : BoundaryRootedComponents R S V) :
    (∑ x ∈ validWindowStarts R p,
        (internalRunStarts S (horizontalSection R S p V x)).card) ≤
      verticalInternalRunCount R S V :=
  window_injection_inequality R S p V (slidingWindowInjection_of_components hcomp)

end Boundary

end SquareMaximality
