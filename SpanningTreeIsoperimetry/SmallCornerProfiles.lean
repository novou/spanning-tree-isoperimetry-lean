module

public import SpanningTreeIsoperimetry.SmallShapeCatalogue
public import SpanningTreeIsoperimetry.CornerPrimalDomains
public import SpanningTreeIsoperimetry.CornerPrimalSymmetry
public import SpanningTreeIsoperimetry.TwoCornerStripTree

@[expose] public section

/-! Exhaustive profiles of sparse four-corner defects. The finite catalogue
describes the literal diagrams, before count comparisons or maximality. -/
namespace SpanningTreeIsoperimetry.SmallCornerProfiles
open Ferrers CornerEnergy CornerPrimalDomains SmallShapeCatalogue StripRigidity CornerStripBridge
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def smallDiagram : Fin 7 → Diagram :=
  ![∅,horizontalStrip 1,horizontalStrip 2,verticalDiagram 2,
    horizontalStrip 3,verticalDiagram 3,threeCell]

theorem small_diagram_catalogue {M : Diagram} (hM : IsFerrers M) (hk : M.card≤3) :
    ∃ i : Fin 7, M=smallDiagram i := by
  rcases ferrers_three_cell_catalogue hM hk with hs|rfl
  · rcases hs with he|he
    · interval_cases h : M.card
      · exact ⟨0,he.trans (by decide +kernel)⟩
      · exact ⟨1,he⟩
      · exact ⟨2,he⟩
      · exact ⟨4,he⟩
    · interval_cases h : M.card
      · exact ⟨0,he.trans (by decide +kernel)⟩
      · exact ⟨1,he.trans (by decide +kernel)⟩
      · exact ⟨3,he⟩
      · exact ⟨5,he⟩
  · exact ⟨6,rfl⟩

def smallFamily (p : Corner → Fin 7) : Corner → Diagram := fun c => smallDiagram (p c)

theorem family_diagram_le_total (M : Corner → Diagram) (c : Corner) :
    (M c).card≤totalDefect M := by
  exact Finset.single_le_sum (fun d _ => Nat.zero_le (M d).card) (Finset.mem_univ c)

theorem sparse_family_catalogue {M : Corner → Diagram}
    (hM : ∀ c, IsFerrers (M c)) (hk : totalDefect M≤3) :
    ∃ p : Corner → Fin 7, M=smallFamily p := by
  classical
  have hp (c : Corner) : ∃ i : Fin 7, M c=smallDiagram i :=
    small_diagram_catalogue (hM c) ((family_diagram_le_total M c).trans hk)
  choose p hp using hp
  exact ⟨p,funext hp⟩

def SingleStripProfile (M : Corner → Diagram) : Prop :=
  ∃ c : Corner, ∃ k : Fin 4, ∃ v : Bool,
    M=twoCornerFamily c (reflectCorner (false,false) c) (stripDiagram k.val v) ∅

def EllProfile (M : Corner → Diagram) : Prop :=
  ∃ c : Corner, M=twoCornerFamily c (reflectCorner (false,false) c) threeCell ∅

def PairProfile (M : Corner → Diagram) : Prop :=
  ∃ c d : Corner, c≠d ∧ ∃ a b : Fin 3, 0<a.val ∧ 0<b.val ∧ a.val+b.val≤3 ∧
    ∃ u v : Bool, M=twoCornerFamily c d (stripDiagram a.val u) (stripDiagram b.val v)

def TripleProfile (M : Corner → Diagram) : Prop :=
  ∃ missing : Corner, M=(fun c => if c=missing then ∅ else horizontalStrip 1)

def SparseProfile (M : Corner → Diagram) : Prop :=
  SingleStripProfile M ∨ EllProfile M ∨ PairProfile M ∨ TripleProfile M

instance sparseProfileDecidable (M : Corner → Diagram) : Decidable (SparseProfile M) := by
  unfold SparseProfile SingleStripProfile EllProfile PairProfile TripleProfile
  infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem small_family_profiles : ∀ p : Corner → Fin 7,
    totalDefect (smallFamily p)≤3 → SparseProfile (smallFamily p) := by
  decide +kernel

theorem sparse_ferrers_profiles {M : Corner → Diagram}
    (hM : ∀ c, IsFerrers (M c)) (hk : totalDefect M≤3) : SparseProfile M := by
  obtain ⟨p,rfl⟩ := sparse_family_catalogue hM hk
  exact small_family_profiles p hk

end SpanningTreeIsoperimetry.SmallCornerProfiles
