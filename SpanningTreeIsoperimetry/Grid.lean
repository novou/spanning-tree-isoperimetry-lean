import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-! The actual lattice and combinatorial spanning-tree count.
The count is not defined to be a determinant: the matrix-tree bridge is a
separate obligation. All graphs here are induced on the specified vertex set. -/

namespace SpanningTreeIsoperimetry

abbrev Vertex := ℤ × ℤ
abbrev Domain := Finset Vertex

def transposeDomain (S : Domain) : Domain := S.image Prod.swap

@[simp] theorem mem_transposeDomain {S : Domain} {v : Vertex} :
    v ∈ transposeDomain S ↔ v.swap ∈ S := by
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    simpa using hw
  · intro hv
    exact Finset.mem_image.mpr ⟨v.swap, hv, by simp⟩

@[simp] theorem card_transposeDomain (S : Domain) :
    (transposeDomain S).card = S.card :=
  Finset.card_image_of_injective _ Prod.swap_injective

def lattice : SimpleGraph Vertex where
  Adj u v := (u.1 = v.1 ∧ |u.2 - v.2| = 1) ∨
    (u.2 = v.2 ∧ |u.1 - v.1| = 1)
  symm := ⟨by
    intro u v h
    rcases h with h | h
    · exact Or.inl ⟨h.1.symm, by simpa only [abs_sub_comm] using h.2⟩
    · exact Or.inr ⟨h.1.symm, by simpa only [abs_sub_comm] using h.2⟩⟩
  loopless := ⟨by intro u; simp⟩

def domainGraph (S : Domain) : SimpleGraph (S : Set Vertex) := lattice.induce S

def SpanningTrees (S : Domain) :=
  { T : SimpleGraph (S : Set Vertex) // T ≤ domainGraph S ∧ T.IsTree }

noncomputable def treeCount (S : Domain) : ℕ := Nat.card (SpanningTrees S)

instance (S : Domain) : Finite (SpanningTrees S) := inferInstanceAs
  (Finite { T : SimpleGraph (S : Set Vertex) // T ≤ domainGraph S ∧ T.IsTree })

theorem treeCount_pos_iff_connected (S : Domain) :
    0 < treeCount S ↔ (domainGraph S).Connected := by
  constructor
  · intro h
    obtain ⟨⟨T, hT, htree⟩⟩ := (Nat.card_pos_iff.mp h).1
    exact htree.connected.mono hT
  · intro h
    obtain ⟨T, hT, ht⟩ := h.exists_isTree_le
    exact Nat.card_pos_iff.mpr ⟨⟨⟨T, hT, ht⟩⟩, inferInstance⟩

theorem treeCount_eq_one_of_tree {S : Domain} (h : (domainGraph S).IsTree) :
    treeCount S = 1 := by
  have heq (T : SpanningTrees S) : T.val = domainGraph S :=
    le_antisymm T.property.1
      ((SimpleGraph.isTree_iff_minimal_connected.mp h).2 T.property.2.connected T.property.1)
  let : Nonempty (SpanningTrees S) := ⟨⟨domainGraph S, le_rfl, h⟩⟩
  let : Subsingleton (SpanningTrees S) := ⟨fun T U =>
    Subtype.ext ((heq T).trans (heq U).symm)⟩
  exact Nat.card_unique

@[simp] theorem treeCount_singleton (v : Vertex) : treeCount {v} = 1 := by
  let : Nonempty (({v} : Domain) : Set Vertex) := ⟨⟨v, by simp⟩⟩
  let : Subsingleton (({v} : Domain) : Set Vertex) := ⟨by
    intro x y
    apply Subtype.ext
    have hx : x.val = v := by simpa using x.property
    have hy : y.val = v := by simpa using y.property
    exact hx.trans hy.symm⟩
  exact treeCount_eq_one_of_tree SimpleGraph.IsTree.of_subsingleton

def rectangle (r s : ℕ) : Domain :=
  Finset.Ico (0 : ℤ) r ×ˢ Finset.Ico (0 : ℤ) s

@[simp] theorem mem_rectangle {r s : ℕ} {v : Vertex} :
    v ∈ rectangle r s ↔ 0 ≤ v.1 ∧ v.1 < r ∧ 0 ≤ v.2 ∧ v.2 < s := by
  simp only [rectangle, Finset.mem_product, Finset.mem_Ico]
  tauto

@[simp] theorem card_rectangle (r s : ℕ) : (rectangle r s).card = r * s := by
  simp [rectangle, Finset.card_product, Int.card_Ico]

theorem rectangle_mono {r s R T : ℕ} (hr : r ≤ R) (hs : s ≤ T) :
    rectangle r s ⊆ rectangle R T := by
  intro v hv
  rw [mem_rectangle] at hv ⊢
  exact ⟨hv.1, lt_of_lt_of_le hv.2.1 (by exact_mod_cast hr),
    hv.2.2.1, lt_of_lt_of_le hv.2.2.2 (by exact_mod_cast hs)⟩

/-- Deleting the vertical corner strip used in Sections 1 and 8. -/
def cornerStrip (r s k : ℕ) : Domain := rectangle r s \ rectangle 1 k

@[simp] theorem card_cornerStrip {r s k : ℕ} (hr : 1 ≤ r) (hk : k ≤ s) :
    (cornerStrip r s k).card = r * s - k := by
  rw [cornerStrip, Finset.card_sdiff_of_subset (rectangle_mono hr hk)]
  simp

def translate (a v : Vertex) : Vertex := (a.1 + v.1, a.2 + v.2)

theorem translate_injective (a : Vertex) : Function.Injective (translate a) := by
  intro u v h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [translate, add_right_inj] at h₁ h₂
  exact Prod.ext h₁ h₂

@[simp] theorem translate_adj (a u v : Vertex) :
    lattice.Adj (translate a u) (translate a v) ↔ lattice.Adj u v := by
  simp [lattice, translate]

/-- The paper maximizes over connected induced graphs at fixed cardinality. -/
def IsMaximizer (S : Domain) : Prop :=
  (domainGraph S).Connected ∧
  ∀ T : Domain, T.card = S.card → (domainGraph T).Connected → treeCount T ≤ treeCount S

theorem treeCount_eq_one_of_card_one {S : Domain} (h : S.card = 1) :
    treeCount S = 1 := by
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h
  exact treeCount_singleton v

theorem singleton_isMaximizer (v : Vertex) : IsMaximizer {v} := by
  refine ⟨(treeCount_pos_iff_connected {v}).mp (by simp), ?_⟩
  intro T hT _
  have hcard : T.card = 1 := by simpa using hT
  simp [treeCount_eq_one_of_card_one hcard]

def IsFerrers (M : Finset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ M, ∀ q : ℕ × ℕ, q.1 ≤ p.1 → q.2 ≤ p.2 → q ∈ M

def IsRowConvex (S : Domain) : Prop :=
  ∀ x₁ x x₂ y : ℤ, (x₁,y) ∈ S → (x₂,y) ∈ S → x₁ ≤ x → x ≤ x₂ → (x,y) ∈ S

def IsColumnConvex (S : Domain) : Prop :=
  ∀ x y₁ y y₂ : ℤ, (x,y₁) ∈ S → (x,y₂) ∈ S → y₁ ≤ y → y ≤ y₂ → (x,y) ∈ S

theorem rectangle_rowConvex (r s : ℕ) : IsRowConvex (rectangle r s) := by
  intro x₁ x x₂ y h₁ h₂ hl hu
  simp only [mem_rectangle] at h₁ h₂ ⊢
  omega

theorem rectangle_columnConvex (r s : ℕ) : IsColumnConvex (rectangle r s) := by
  intro x y₁ y y₂ h₁ h₂ hl hu
  simp only [mem_rectangle] at h₁ h₂ ⊢
  omega

end SpanningTreeIsoperimetry
