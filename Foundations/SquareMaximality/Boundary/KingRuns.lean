import SquareMaximality.Boundary.King
import SquareMaximality.Boundary.SlidingInjection

set_option autoImplicit false

/-!
# From king components to vertical-run components

This file proves the geometric bridge used by the sliding-window argument.
Every vacancy point is sent to the canonical vertical run containing it.
King-adjacent points either belong to the same vertical run or their runs are
adjacent in `fullVerticalRunGraph`.  Consequently a king path to the perimeter
becomes a run-graph path to a marked run or a boundary-column run.
-/

namespace SquareMaximality

namespace Boundary

open Windows

/-! ## The canonical run containing a point -/

/-- Possible left endpoints of the consecutive part of `B` ending at `y`. -/
private def runStartCandidates (B : Finset ℕ) (y : ℕ) : Finset ℕ :=
  (line y).filter fun a => Finset.Icc a y ⊆ B

private theorem runStartCandidates_nonempty {B : Finset ℕ} {y : ℕ}
    (hy : y ∈ B) : (runStartCandidates B y).Nonempty := by
  refine ⟨y, ?_⟩
  simp only [runStartCandidates, Finset.mem_filter, mem_line]
  refine ⟨le_rfl, ?_⟩
  simpa using hy

/-- The least point from which every integer through `y` belongs to `B`.
It is used only under the hypothesis `y ∈ B`; the other branch is a harmless
totalization. -/
private noncomputable def pointRunStart (B : Finset ℕ) (y : ℕ) : ℕ := by
  classical
  exact if hy : y ∈ B then
    (runStartCandidates B y).min' (runStartCandidates_nonempty hy)
  else 0

private theorem pointRunStart_mem_candidates {B : Finset ℕ} {y : ℕ}
    (hy : y ∈ B) : pointRunStart B y ∈ runStartCandidates B y := by
  classical
  simp only [pointRunStart, dif_pos hy]
  exact Finset.min'_mem _ _

private theorem pointRunStart_le {B : Finset ℕ} {y : ℕ}
    (hy : y ∈ B) : pointRunStart B y ≤ y := by
  exact (Finset.mem_filter.mp (pointRunStart_mem_candidates hy)).1 |> mem_line.mp

private theorem pointRunStart_segment {B : Finset ℕ} {y : ℕ}
    (hy : y ∈ B) : Finset.Icc (pointRunStart B y) y ⊆ B := by
  exact (Finset.mem_filter.mp (pointRunStart_mem_candidates hy)).2

private theorem pointRunStart_mem {B : Finset ℕ} {y : ℕ}
    (hy : y ∈ B) : pointRunStart B y ∈ B := by
  exact pointRunStart_segment hy (by simp [pointRunStart_le hy])

private theorem pointRunStart_zero_or_pred_not_mem {B : Finset ℕ} {y : ℕ}
    (hy : y ∈ B) :
    pointRunStart B y = 0 ∨ pointRunStart B y - 1 ∉ B := by
  classical
  by_cases hzero : pointRunStart B y = 0
  · exact Or.inl hzero
  · right
    intro hpred
    have hpos : 0 < pointRunStart B y := by omega
    have hcandidate : pointRunStart B y - 1 ∈ runStartCandidates B y := by
      simp only [runStartCandidates, Finset.mem_filter, mem_line]
      refine ⟨(Nat.sub_le _ _).trans (pointRunStart_le hy), ?_⟩
      intro z hz
      simp only [Finset.mem_Icc] at hz
      by_cases hzpred : z = pointRunStart B y - 1
      · simpa [hzpred] using hpred
      · apply pointRunStart_segment hy
        simp only [Finset.mem_Icc]
        omega
    have hmin : pointRunStart B y ≤ pointRunStart B y - 1 := by
      simpa only [pointRunStart, dif_pos hy] using
        (Finset.min'_le (runStartCandidates B y) _ hcandidate)
    omega

private theorem pointRunStart_mem_runStarts {L y : ℕ} {B : Finset ℕ}
    (hB : B ⊆ line L) (hy : y ∈ B) : pointRunStart B y ∈ runStarts L B := by
  rw [mem_runStarts]
  exact ⟨mem_line.mp (hB (pointRunStart_mem hy)), pointRunStart_mem hy,
    pointRunStart_zero_or_pred_not_mem hy⟩

private theorem point_mem_pointRunStart_component {L y : ℕ} {B : Finset ℕ}
    (hB : B ⊆ line L) (hy : y ∈ B) :
    y ∈ intervalComponent L B (pointRunStart B y) := by
  rw [mem_intervalComponent]
  exact ⟨pointRunStart_le hy, mem_line.mp (hB hy), pointRunStart_segment hy⟩

/-- Points of the same set at distance at most one vertically have the same
canonical vertical-run start. -/
private theorem pointRunStart_eq_of_dist_le_one {B : Finset ℕ} {y z : ℕ}
    (hy : y ∈ B) (hz : z ∈ B) (hnear : Nat.dist y z ≤ 1) :
    pointRunStart B y = pointRunStart B z := by
  classical
  suffices horiented : ∀ {u v : ℕ}, u ∈ B → v ∈ B → u ≤ v →
      Nat.dist u v ≤ 1 → pointRunStart B u = pointRunStart B v by
    rcases le_total y z with hyz | hzy
    · exact horiented hy hz hyz hnear
    · exact (horiented hz hy hzy (by simpa [Nat.dist_comm] using hnear)).symm
  intro u v hu hv huv hdist
  have hv_le : v ≤ u + 1 := by
    rw [Nat.dist_eq_sub_of_le huv] at hdist
    omega
  have hstartU_candidate_v : pointRunStart B u ∈ runStartCandidates B v := by
    simp only [runStartCandidates, Finset.mem_filter, mem_line]
    refine ⟨(pointRunStart_le hu).trans huv, ?_⟩
    intro t ht
    simp only [Finset.mem_Icc] at ht
    by_cases htu : t ≤ u
    · exact pointRunStart_segment hu (by
        simp only [Finset.mem_Icc]
        exact ⟨ht.1, htu⟩)
    · have htv : t = v := by omega
      simpa [htv] using hv
  have hVU : pointRunStart B v ≤ pointRunStart B u := by
    simpa only [pointRunStart, dif_pos hv] using
      (Finset.min'_le (runStartCandidates B v) _ hstartU_candidate_v)
  have hstartV_candidate_u : pointRunStart B v ∈ runStartCandidates B u := by
    simp only [runStartCandidates, Finset.mem_filter, mem_line]
    refine ⟨hVU.trans (pointRunStart_le hu), ?_⟩
    intro t ht
    apply pointRunStart_segment hv
    simp only [Finset.mem_Icc] at ht ⊢
    exact ⟨ht.1, ht.2.trans huv⟩
  have hUV : pointRunStart B u ≤ pointRunStart B v := by
    simpa only [pointRunStart, dif_pos hu] using
      (Finset.min'_le (runStartCandidates B u) _ hstartV_candidate_u)
  exact Nat.le_antisymm hUV hVU

/-- A recognized run start is recovered by the canonical point-to-run map. -/
private theorem pointRunStart_eq_of_mem_runStarts {L a : ℕ} {B : Finset ℕ}
    (ha : a ∈ runStarts L B) : pointRunStart B a = a := by
  classical
  have hs := mem_runStarts.mp ha
  have haCandidate : a ∈ runStartCandidates B a := by
    simp only [runStartCandidates, Finset.mem_filter, mem_line]
    exact ⟨le_rfl, by simpa using hs.2.1⟩
  have hle : pointRunStart B a ≤ a := by
    simpa only [pointRunStart, dif_pos hs.2.1] using
      (Finset.min'_le (runStartCandidates B a) _ haCandidate)
  have hge : a ≤ pointRunStart B a := by
    rcases hs.2.2 with hzero | hpred
    · simp [hzero]
    · by_contra h
      have hsegment := pointRunStart_segment hs.2.1
      exact hpred (hsegment (by
        simp only [Finset.mem_Icc]
        omega))
  exact Nat.le_antisymm hle hge

/-! ## Mapping vacancy points to run vertices -/

private theorem point_mem_column_of_mem_grid {R S : ℕ} {V : Finset LatticePoint}
    (hV : V ⊆ grid R S) (p : {z // z ∈ V}) :
    p.1.2 ∈ column S V p.1.1 := by
  have hpGrid := mem_grid.mp (hV p.2)
  exact mem_column.mpr ⟨hpGrid.2, p.2⟩

/-- The full vertical run containing a vacancy point. -/
private noncomputable def runVertexOfPoint {R S : ℕ} {V : Finset LatticePoint}
    (hV : V ⊆ grid R S) (p : {z // z ∈ V}) : RunVertex R S V := by
  classical
  refine ⟨⟨p.1.1, pointRunStart (column S V p.1.1) p.1.2⟩, ?_⟩
  simp only [verticalRuns, Finset.mem_sigma]
  have hpGrid := mem_grid.mp (hV p.2)
  exact ⟨mem_line.mpr hpGrid.1,
    pointRunStart_mem_runStarts (column_subset_line S V p.1.1)
      (point_mem_column_of_mem_grid hV p)⟩

@[simp] private theorem runVertexOfPoint_column {R S : ℕ} {V : Finset LatticePoint}
    (hV : V ⊆ grid R S) (p : {z // z ∈ V}) :
    (runVertexOfPoint hV p).1.1 = p.1.1 := rfl

private theorem point_mem_runVertexOfPoint_component
    {R S : ℕ} {V : Finset LatticePoint}
    (hV : V ⊆ grid R S) (p : {z // z ∈ V}) :
    p.1.2 ∈ intervalComponent S (column S V p.1.1)
      (runVertexOfPoint hV p).1.2 := by
  exact point_mem_pointRunStart_component (column_subset_line S V p.1.1)
    (point_mem_column_of_mem_grid hV p)

private theorem runVertexOfPoint_eq_of_same_column
    {R S : ℕ} {V : Finset LatticePoint}
    (hV : V ⊆ grid R S) {p q : {z // z ∈ V}}
    (hx : p.1.1 = q.1.1) (hy : Nat.dist p.1.2 q.1.2 ≤ 1) :
    runVertexOfPoint hV p = runVertexOfPoint hV q := by
  apply Subtype.ext
  change (⟨p.1.1, pointRunStart (column S V p.1.1) p.1.2⟩ : Σ _ : ℕ, ℕ) =
    ⟨q.1.1, pointRunStart (column S V q.1.1) q.1.2⟩
  rw [Sigma.mk.inj_iff, heq_iff_eq]
  refine ⟨hx, ?_⟩
  have hqColumn : q.1.2 ∈ column S V p.1.1 := by
    simpa only [hx] using point_mem_column_of_mem_grid hV q
  simpa only [hx] using pointRunStart_eq_of_dist_le_one
    (point_mem_column_of_mem_grid hV p) hqColumn hy

/-- A king move projects either to a stationary run or to one edge of the
full vertical-run graph. -/
private theorem runVertexOfPoint_reachable_of_kingAdjacent
    {R S : ℕ} {V : Finset LatticePoint}
    (hV : V ⊆ grid R S) {p q : {z // z ∈ V}}
    (hpq : KingAdjacent p.1 q.1) :
    (fullVerticalRunGraph R S V).Reachable
      (runVertexOfPoint hV p) (runVertexOfPoint hV q) := by
  by_cases hx : p.1.1 = q.1.1
  · rw [runVertexOfPoint_eq_of_same_column hV hx hpq.2.2]
  · have hxdist : Nat.dist p.1.1 q.1.1 = 1 := by
      have hpos : 0 < Nat.dist p.1.1 q.1.1 := by
        exact Nat.pos_of_ne_zero (fun hzero => hx (Nat.eq_of_dist_eq_zero hzero))
      have hle := hpq.2.1
      omega
    have hrel : verticalRunRelation R S V
        (runVertexOfPoint hV p) (runVertexOfPoint hV q) := by
      refine ⟨hxdist, p.1.2, point_mem_runVertexOfPoint_component hV p,
        q.1.2, point_mem_runVertexOfPoint_component hV q, hpq.2.2⟩
    have hne : runVertexOfPoint hV p ≠ runVertexOfPoint hV q := by
      intro h
      exact hx (congrArg (fun z : RunVertex R S V => z.1.1) h)
    have hadj : (fullVerticalRunGraph R S V).Adj
        (runVertexOfPoint hV p) (runVertexOfPoint hV q) := by
      simp only [fullVerticalRunGraph, SimpleGraph.fromRel_adj]
      exact ⟨hne, Or.inl hrel⟩
    exact hadj.reachable

private theorem runVertexOfPoint_reachable_of_walk
    {R S : ℕ} {V : Finset LatticePoint}
    (hV : V ⊆ grid R S) {p q : {z // z ∈ V}}
    (w : (kingGraph V).Walk p q) :
    (fullVerticalRunGraph R S V).Reachable
      (runVertexOfPoint hV p) (runVertexOfPoint hV q) := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons h w ih =>
      exact (runVertexOfPoint_reachable_of_kingAdjacent hV
        ((kingGraph_adj_iff _ _).mp h)).trans ih

private theorem runVertexOfPoint_reachable_of_kingReachable
    {R S : ℕ} {V : Finset LatticePoint}
    (hV : V ⊆ grid R S) {p q : {z // z ∈ V}}
    (hpq : (kingGraph V).Reachable p q) :
    (fullVerticalRunGraph R S V).Reachable
      (runVertexOfPoint hV p) (runVertexOfPoint hV q) := by
  rcases hpq with ⟨w⟩
  exact runVertexOfPoint_reachable_of_walk hV w

private theorem runVertexOfPoint_isBoundaryRoot_of_perimeter
    {R S : ℕ} {V : Finset LatticePoint}
    (hV : V ⊆ grid R S) (q : {z // z ∈ V})
    (hq : IsPerimeter R S q.1) : IsBoundaryRoot (runVertexOfPoint hV q) := by
  rcases hq with hx0 | hxR | hy0 | hyS
  · exact Or.inr (Or.inl (by simpa using hx0))
  · exact Or.inr (Or.inr (by simpa using hxR))
  · left
    left
    have hle := pointRunStart_le (point_mem_column_of_mem_grid hV q)
    change pointRunStart (column S V q.1.1) q.1.2 = 0
    omega
  · left
    right
    have hmem := point_mem_runVertexOfPoint_component hV q
    simpa [hyS] using hmem

/-! ## The generic king-component bridge -/

/-- If every king component of `V` meets the rectangle perimeter, then every
component of the full vertical-run graph has an admissible root. -/
theorem boundaryRootedComponents_of_kingComponents
    {R S : ℕ} {V : Finset LatticePoint}
    (hV : V ⊆ grid R S)
    (hperimeter : ∀ p : {z // z ∈ V}, ∃ q : {z // z ∈ V},
      IsPerimeter R S q.1 ∧ (kingGraph V).Reachable p q) :
    BoundaryRootedComponents R S V := by
  intro v
  rcases v with ⟨⟨x, a⟩, hva⟩
  have hva' := Finset.mem_sigma.mp hva
  have haRun : a ∈ runStarts S (column S V x) := hva'.2
  have haV : (x, a) ∈ V :=
    (mem_column.mp (mem_runStarts.mp haRun).2.1).2
  let p : {z // z ∈ V} := ⟨(x, a), haV⟩
  have hpRun : runVertexOfPoint hV p = ⟨⟨x, a⟩, hva⟩ := by
    apply Subtype.ext
    change (⟨x, pointRunStart (column S V x) a⟩ : Σ _ : ℕ, ℕ) = ⟨x, a⟩
    rw [Sigma.mk.inj_iff, heq_iff_eq]
    exact ⟨rfl, pointRunStart_eq_of_mem_runStarts haRun⟩
  rcases hperimeter p with ⟨q, hqPerim, hpq⟩
  refine ⟨runVertexOfPoint hV q, ?_,
    runVertexOfPoint_isBoundaryRoot_of_perimeter hV q hqPerim⟩
  rw [← hpRun]
  exact runVertexOfPoint_reachable_of_kingReachable hV hpq

/-! ## Boundary-attached vacancy sets -/

private def asBoundaryVacancy
    {R S : ℕ} {V : Finset LatticePoint} {p : {z // z ∈ V}}
    (hp : IsBoundaryAttached R S V p.1) :
    {z // z ∈ boundaryVacancies R S V} :=
  ⟨p.1, mem_boundaryVacancies.mpr hp⟩

private theorem boundaryReachable_lift
    {R S : ℕ} {V : Finset LatticePoint} {p q : {z // z ∈ V}}
    (hp : IsBoundaryAttached R S V p.1)
    (w : (kingGraph V).Walk p q) :
    ∃ q' : {z // z ∈ boundaryVacancies R S V}, q'.1 = q.1 ∧
      (kingGraph (boundaryVacancies R S V)).Reachable
        (asBoundaryVacancy hp) q' := by
  induction w with
  | nil =>
      exact ⟨asBoundaryVacancy hp, rfl,
        SimpleGraph.Reachable.refl _⟩
  | @cons u v q huv w ih =>
      have hpv : IsBoundaryAttached R S V v.1 :=
        isBoundaryAttached_of_reachable hp huv.reachable
      rcases ih hpv with ⟨q', hq', hvq⟩
      let u' : {z // z ∈ boundaryVacancies R S V} :=
        asBoundaryVacancy hp
      let v' : {z // z ∈ boundaryVacancies R S V} :=
        asBoundaryVacancy hpv
      have huv' : (kingGraph (boundaryVacancies R S V)).Adj u' v' := by
        rw [kingGraph_adj_iff]
        exact (kingGraph_adj_iff u v).mp huv
      exact ⟨q', hq', huv'.reachable.trans hvq⟩

/-- The union of king components which meet the perimeter automatically
satisfies the run-component hypothesis required by the sliding injection. -/
theorem boundaryRootedComponents_boundaryVacancies
    {R S : ℕ} {V : Finset LatticePoint} (hV : V ⊆ grid R S) :
    BoundaryRootedComponents R S (boundaryVacancies R S V) := by
  apply boundaryRootedComponents_of_kingComponents
  · exact fun _ hp => hV (boundaryVacancies_subset R S V hp)
  · intro p
    have hpAttach : IsBoundaryAttached R S V p.1 := mem_boundaryVacancies.mp p.2
    rcases hpAttach with ⟨hpV, q, hqPerim, hpq⟩
    rcases hpq with ⟨w⟩
    rcases boundaryReachable_lift (p := ⟨p.1, hpV⟩)
        (q := q) (mem_boundaryVacancies.mp p.2) w with ⟨q', hq', hpq'⟩
    exact ⟨q', hq' ▸ hqPerim, hpq'⟩

/-- Encoded vacancies lie in their displayed natural-coordinate grid. -/
theorem encodedVacancies_subset_grid (R S : ℕ) (A : Finset Point) :
    encodedVacancies R S A ⊆ grid R S := by
  intro z hz
  exact mem_grid.mpr ⟨(mem_encodedVacancies.mp hz).1,
    (mem_encodedVacancies.mp hz).2.1⟩

/-- Exact bridge used for a normalized lattice set: the boundary-attached
encoded vacancies satisfy the component hypothesis with no further assumption. -/
theorem boundaryRootedComponents_encodedBoundaryVacancies
    (R S : ℕ) (A : Finset Point) :
    BoundaryRootedComponents R S
      (boundaryVacancies R S (encodedVacancies R S A)) :=
  boundaryRootedComponents_boundaryVacancies (encodedVacancies_subset_grid R S A)

/-- Therefore the manuscript's finite sliding injection is available for the
boundary-attached encoded vacancy set. -/
theorem slidingWindowInjection_encodedBoundaryVacancies
    (R S p : ℕ) (A : Finset Point) :
    SlidingWindowInjection R S p
      (boundaryVacancies R S (encodedVacancies R S A)) :=
  slidingWindowInjection_of_components
    (boundaryRootedComponents_encodedBoundaryVacancies R S A)

end Boundary

end SquareMaximality
