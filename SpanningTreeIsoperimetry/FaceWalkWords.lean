import SquareMaximality.Boundary.TraceWalks

/-! Open finite face walks and their actual step words. -/
namespace SpanningTreeIsoperimetry.FaceWalkWords

open SquareMaximality SquareMaximality.Boundary SquareMaximality.ClosedWalk
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every translated partial displacement is a vertex of the finite domain. -/
def StaysIn {n : ℕ} (U : Finset LatticePoint) (z : {p // p ∈ U}) (ω : Word n) : Prop :=
  ∀ t ≤ n, ∃ q : {p // p ∈ U},
    latticePointToPoint q = latticePointToPoint z + position ω t

abbrev EndpointWord (U : Finset LatticePoint) (z w : {p // p ∈ U}) (n : ℕ) :=
  {ω : Word n // total ω = latticePointToPoint w - latticePointToPoint z ∧ StaysIn U z ω}

/-- Prescribed-length reading of an open face walk. -/
noncomputable def wordOfWalk {U : Finset LatticePoint} {z w : {p // p ∈ U}} {n : ℕ}
    (p : (faceGraph U).Walk z w) (hp : p.length = n) : Word n :=
  fun i => stepOfAdjacent (p.getVert i).1 (p.getVert (i.1 + 1)).1
    (p.adj_getVert_succ (by omega))

theorem wordOfWalk_vector {U : Finset LatticePoint} {z w : {p // p ∈ U}} {n : ℕ}
    (p : (faceGraph U).Walk z w) (hp : p.length = n) (i : Fin n) :
    (wordOfWalk p hp i).vector =
      latticePointToPoint (p.getVert (i.1 + 1)) - latticePointToPoint (p.getVert i) :=
  stepOfAdjacent_vector _ _ _

theorem position_wordOfWalk {U : Finset LatticePoint} {z w : {p // p ∈ U}} {n t : ℕ}
    (p : (faceGraph U).Walk z w) (hp : p.length = n) (ht : t ≤ n) :
    position (wordOfWalk p hp) t =
      latticePointToPoint (p.getVert t) - latticePointToPoint z := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [position_succ _ (by omega), ih (by omega), wordOfWalk_vector]
    abel

theorem total_wordOfWalk {U : Finset LatticePoint} {z w : {p // p ∈ U}} {n : ℕ}
    (p : (faceGraph U).Walk z w) (hp : p.length = n) :
    total (wordOfWalk p hp) = latticePointToPoint w - latticePointToPoint z := by
  rw [← position_length, position_wordOfWalk p hp le_rfl, ← hp, p.getVert_length]

theorem wordOfWalk_staysIn {U : Finset LatticePoint} {z w : {p // p ∈ U}} {n : ℕ}
    (p : (faceGraph U).Walk z w) (hp : p.length = n) : StaysIn U z (wordOfWalk p hp) := by
  intro t ht
  refine ⟨p.getVert t, ?_⟩
  rw [position_wordOfWalk p hp ht]
  abel

noncomputable def wordVertex {U : Finset LatticePoint} {z w : {p // p ∈ U}} {n : ℕ}
    (ω : EndpointWord U z w n) (t : Fin (n + 1)) : {p // p ∈ U} :=
  Classical.choose (ω.2.2 t (by omega))

theorem wordVertex_point {U : Finset LatticePoint} {z w : {p // p ∈ U}} {n : ℕ}
    (ω : EndpointWord U z w n) (t : Fin (n + 1)) :
    latticePointToPoint (wordVertex ω t) = latticePointToPoint z + position ω.1 t :=
  Classical.choose_spec (ω.2.2 t (by omega))

theorem wordVertex_adj {U : Finset LatticePoint} {z w : {p // p ∈ U}} {n : ℕ}
    (ω : EndpointWord U z w n) (t : ℕ) (ht : t < n) :
    (faceGraph U).Adj (wordVertex ω ⟨t, by omega⟩) (wordVertex ω ⟨t + 1, by omega⟩) := by
  change faceLattice.Adj _ _
  rw [faceLattice_adj_iff_step, wordVertex_point, wordVertex_point, position_succ _ ht]
  have he : latticePointToPoint z + (position ω.1 t + (ω.1 ⟨t, ht⟩).vector) -
      (latticePointToPoint z + position ω.1 t) = (ω.1 ⟨t, ht⟩).vector := by abel
  rw [he]
  cases ω.1 ⟨t, ht⟩ <;> simp

noncomputable def wordWalk {U : Finset LatticePoint} {z w : {p // p ∈ U}} {n : ℕ}
    (ω : EndpointWord U z w n) : (faceGraph U).Walk z w := by
  let l := List.ofFn (wordVertex ω)
  have hn : l ≠ [] := by simp [l]
  have hc : l.IsChain (faceGraph U).Adj := by
    rw [List.isChain_iff_getElem]
    intro i hi
    have hi' : i < n := by simpa [l] using hi
    simp only [l, List.getElem_ofFn]
    exact wordVertex_adj ω i hi'
  let p := SimpleGraph.Walk.ofSupport l hn hc
  apply p.copy
  · apply Subtype.ext
    apply latticePointToPoint_injective
    change latticePointToPoint (l.head hn) = latticePointToPoint z
    simp only [l, List.head_ofFn]
    rw [wordVertex_point]
    simp
  · apply Subtype.ext
    apply latticePointToPoint_injective
    change latticePointToPoint (l.getLast hn) = latticePointToPoint w
    rw [List.getLast_eq_getElem]
    simp only [l, List.length_ofFn, Nat.add_sub_cancel, List.getElem_ofFn]
    rw [wordVertex_point, position_length, ω.2.1]
    abel

@[simp] theorem wordWalk_length {U : Finset LatticePoint} {z w : {p // p ∈ U}} {n : ℕ}
    (ω : EndpointWord U z w n) : (wordWalk ω).length = n := by
  simp [wordWalk]

@[simp] theorem wordWalk_support {U : Finset LatticePoint} {z w : {p // p ∈ U}} {n : ℕ}
    (ω : EndpointWord U z w n) : (wordWalk ω).support = List.ofFn (wordVertex ω) := by
  simp [wordWalk]

theorem wordWalk_getVert {U : Finset LatticePoint} {z w : {p // p ∈ U}} {n t : ℕ}
    (ω : EndpointWord U z w n) (ht : t ≤ n) :
    (wordWalk ω).getVert t = wordVertex ω ⟨t, by omega⟩ := by
  rw [SimpleGraph.Walk.getVert_eq_getD_support, wordWalk_support,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos (show t < n + 1 by omega)]
  rfl

theorem wordOfWalk_wordWalk {U : Finset LatticePoint} {z w : {p // p ∈ U}} {n : ℕ}
    (ω : EndpointWord U z w n) : wordOfWalk (wordWalk ω) (wordWalk_length ω) = ω.1 := by
  funext i
  apply Step.vector_injective
  rw [wordOfWalk_vector, wordWalk_getVert ω (by omega), wordWalk_getVert ω (by omega),
    wordVertex_point, wordVertex_point, position_succ _ i.2]
  abel

theorem wordOfWalk_injective {U : Finset LatticePoint} {z w : {p // p ∈ U}} (n : ℕ) :
    Function.Injective (fun p : {p : (faceGraph U).Walk z w // p.length = n} =>
      wordOfWalk p.1 p.2) := by
  intro p q he
  apply Subtype.ext
  apply SimpleGraph.Walk.support_injective
  apply List.ext_getElem
  · simp [p.2, q.2]
  · intro t ht hq
    rw [SimpleGraph.Walk.support_getElem_eq_getVert,
      SimpleGraph.Walk.support_getElem_eq_getVert]
    apply Subtype.ext
    apply latticePointToPoint_injective
    have ht' : t ≤ n := by simpa [p.2] using ht
    have h := congrArg (fun ω : Word n => position ω t) he
    rw [position_wordOfWalk _ p.2 ht', position_wordOfWalk _ q.2 ht'] at h
    exact sub_left_inj.mp h

/-- Exact finite equivalence for arbitrary open endpoints. -/
noncomputable def endpointWordEquiv (U : Finset LatticePoint) (z w : {p // p ∈ U}) (n : ℕ) :
    {p : (faceGraph U).Walk z w // p.length = n} ≃ EndpointWord U z w n :=
  Equiv.ofBijective
    (fun p => ⟨wordOfWalk p.1 p.2, total_wordOfWalk p.1 p.2, wordOfWalk_staysIn p.1 p.2⟩)
    ⟨fun p q h => wordOfWalk_injective n (congrArg Subtype.val h),
      fun ω => ⟨⟨wordWalk ω, wordWalk_length ω⟩, Subtype.ext (wordOfWalk_wordWalk ω)⟩⟩

end SpanningTreeIsoperimetry.FaceWalkWords
