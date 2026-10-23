module

public import SpanningTreeIsoperimetry.PolarizationStrict
public import Mathlib.LinearAlgebra.Matrix.Reindex

@[expose] public section

/-!
# Concrete strip folds

Dimensions in `faceStripX` and `faceStripY` count bounded faces. Thus the
paper's primal rectangle `(r,s)` uses face dimensions `(r−1,s−1)`.
-/
namespace SpanningTreeIsoperimetry.StripPolarization

open Polarization
open scoped Classical

def faceStripY (m n k : ℕ) : Domain := rectangle m n \ rectangle 1 k

def faceStripX (m n k : ℕ) : Domain := rectangle m n \ rectangle k 1

@[simp] theorem mem_faceStripY {m n k : ℕ} {v : Vertex} :
    v ∈ faceStripY m n k ↔
      0 ≤ v.1 ∧ v.1 < m ∧ 0 ≤ v.2 ∧ v.2 < n ∧ (v.1 ≠ 0 ∨ (k : ℤ) ≤ v.2) := by
  simp only [faceStripY, Finset.mem_sdiff, mem_rectangle]
  omega

@[simp] theorem mem_faceStripX {m n k : ℕ} {v : Vertex} :
    v ∈ faceStripX m n k ↔
      0 ≤ v.1 ∧ v.1 < m ∧ 0 ≤ v.2 ∧ v.2 < n ∧ (v.2 ≠ 0 ∨ (k : ℤ) ≤ v.1) := by
  simp only [faceStripX, Finset.mem_sdiff, mem_rectangle]
  omega

theorem transpose_faceStripY (m n k : ℕ) :
    transposeDomain (faceStripY m n k) = faceStripX n m k := by
  ext v
  simp only [mem_transposeDomain, mem_faceStripY, mem_faceStripX, Prod.fst_swap, Prod.snd_swap]
  omega

theorem faceStrips_eq_of_short {m n k : ℕ} (hk : k ≤ 1) :
    faceStripY m n k = faceStripX m n k := by
  ext v
  simp only [mem_faceStripY, mem_faceStripX]
  omega

/-- The orientation fold is a literal equality of finite coordinate sets. -/
theorem polarize_faceStripY {m n k : ℕ} (hmn : m ≤ n) (hk : k ≤ m) :
    polarized (faceStripY m n k) Prod.swap (fun x : Vertex => x.1 < x.2) = faceStripX m n k := by
  ext v
  rw [mem_polarized Prod.swap_swap]
  simp only [mem_faceStripY, mem_faceStripX, Prod.fst_swap, Prod.snd_swap]
  split_ifs <;> omega

noncomputable def faceDeterminant (U : Domain) (z : ℝ) : ℝ :=
  Matrix.det (z • (1 : Matrix (U : Set Vertex) (U : Set Vertex) ℝ) - (domainGraph U).adjMatrix ℝ)

/-- Coordinate graph isomorphisms preserve every shifted adjacency determinant. -/
theorem faceDeterminant_iso {U V : Domain} (e : domainGraph U ≃g domainGraph V) (z : ℝ) :
    faceDeterminant U z = faceDeterminant V z := by
  let E := Matrix.reindexAlgEquiv ℝ ℝ e.toEquiv
  have he : E ((domainGraph U).adjMatrix ℝ) = (domainGraph V).adjMatrix ℝ :=
    e.reindex_adjMatrix ℝ
  have hm : E (z • (1 : Matrix (U : Set Vertex) (U : Set Vertex) ℝ) - (domainGraph U).adjMatrix ℝ) =
      z • (1 : Matrix (V : Set Vertex) (V : Set Vertex) ℝ) - (domainGraph V).adjMatrix ℝ := by
    rw [map_sub, map_smul, map_one, he]
  unfold faceDeterminant
  rw [← hm]
  exact (Matrix.det_reindexAlgEquiv ℝ ℝ e.toEquiv _).symm

noncomputable def graphIsoOfEquiv {U V : Domain} (e : Vertex ≃ Vertex)
    (hmem : ∀ x, x ∈ U ↔ e x ∈ V)
    (hadj : ∀ x y, x ∈ U → y ∈ U → (lattice.Adj (e x) (e y) ↔ lattice.Adj x y)) :
    domainGraph U ≃g domainGraph V :=
  { e.subtypeEquiv hmem with
    map_rel_iff' := by
      intro x y
      exact hadj x.val y.val x.property y.property }

noncomputable def transposeGraphIso (U : Domain) : domainGraph U ≃g domainGraph (transposeDomain U) :=
  graphIsoOfEquiv (Equiv.prodComm ℤ ℤ)
    (fun x => by simp)
    (fun x y _ _ => diagonal_adjacency_invariant x y)

theorem faceDeterminant_transpose (U : Domain) (z : ℝ) :
    faceDeterminant U z = faceDeterminant (transposeDomain U) z :=
  faceDeterminant_iso (transposeGraphIso U) z

theorem orientation_determinant {m n k : ℕ} (hmn : m ≤ n) (hk : k ≤ m)
    (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (faceStripX m n k) z ≤ faceDeterminant (faceStripY m n k) z := by
  have h := adjacency_determinant_of_domain_moments (faceStripY m n k)
    (polarized (faceStripY m n k) Prod.swap (fun x : Vertex => x.1 < x.2))
    (card_polarized Prod.swap_swap _ diagonal_preferred_side).symm
    (fun i => diagonal_adjacency_moments _ (i + 1)) z hz
  change faceDeterminant (polarized (faceStripY m n k) Prod.swap
    (fun x : Vertex => x.1 < x.2)) z ≤ faceDeterminant (faceStripY m n k) z at h
  rw [polarize_faceStripY hmn hk] at h
  exact h

/-- Build actual domain walks from a finite sequence of adjacent lattice points. -/
theorem reachable_along (S : Domain) (v : ℕ → Vertex) (n : ℕ)
    (hmem : ∀ i, i ≤ n → v i ∈ S)
    (hadj : ∀ i, i < n → lattice.Adj (v i) (v (i + 1))) :
    (domainGraph S).Reachable ⟨v 0, hmem 0 (by omega)⟩ ⟨v n, hmem n le_rfl⟩ := by
  revert hmem hadj
  induction n with
  | zero => intro _ _; exact SimpleGraph.Reachable.rfl
  | succ n ih =>
    intro hmem hadj
    have hp := ih (fun i hi => hmem i (by omega)) (fun i hi => hadj i (by omega))
    have he : (domainGraph S).Adj ⟨v n, hmem n (by omega)⟩ ⟨v (n + 1), hmem (n + 1) le_rfl⟩ :=
      hadj n (by omega)
    exact hp.trans he.reachable

theorem vertical_lattice_step (x y : ℤ) : lattice.Adj (x, y) (x, y + 1) := by
  left
  exact ⟨rfl, by norm_num⟩

def stripOrientationPath (i : ℕ) : Vertex := (0, i + 1)

theorem stripOrientationPath_mem {m n k : ℕ} (hmn : m < n) (hk : k ≤ m) (hk2 : 2 ≤ k)
    {i : ℕ} (hi : i ≤ m - 1) :
    stripOrientationPath i ∈ preferredDomain (faceStripY m n k) Prod.swap
      (fun x : Vertex => x.1 < x.2) := by
  rw [preferredDomain, Finset.mem_filter, polarize_faceStripY hmn.le hk]
  simp only [mem_faceStripX, stripOrientationPath]
  omega

theorem stripOrientation_opposite {m n k : ℕ} (hmn : m < n) (hk : k ≤ m) (hk2 : 2 ≤ k) :
    OppositeSingletons (faceStripY m n k) Prod.swap (stripOrientationPath 0) (stripOrientationPath (m - 1)) := by
  right
  simp only [mem_faceStripY, stripOrientationPath, Prod.fst_swap, Prod.snd_swap]
  omega

/-- The strict orientation witness is the vertical path `(0,1),…,(0,m)`. -/
theorem orientation_determinant_strict {m n k : ℕ} (hmn : m < n) (hk : k ≤ m) (hk2 : 2 ≤ k)
    (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (faceStripX m n k) z < faceDeterminant (faceStripY m n k) z := by
  let P := preferredDomain (faceStripY m n k) Prod.swap (fun x : Vertex => x.1 < x.2)
  have hmem : ∀ i, i ≤ m - 1 → stripOrientationPath i ∈ P :=
    fun i hi => stripOrientationPath_mem hmn hk hk2 hi
  have hadj : ∀ i, i < m - 1 → lattice.Adj (stripOrientationPath i) (stripOrientationPath (i + 1)) := by
    intro i _
    simpa [stripOrientationPath, Nat.cast_add, add_assoc] using vertical_lattice_step 0 (i + 1)
  obtain ⟨p⟩ := reachable_along P stripOrientationPath (m - 1) hmem hadj
  have hstrict := ordinary_strict_from_preferred_walk (faceStripY m n k) Prod.swap
    (fun x : Vertex => x.1 < x.2) Prod.swap_swap diagonal_preferred_side
    diagonal_adjacency_invariant diagonal_no_cross_edge p (stripOrientation_opposite hmn hk hk2)
  have h := adjacency_strict_determinant_of_domain_moments (faceStripY m n k)
    (polarized (faceStripY m n k) Prod.swap (fun x : Vertex => x.1 < x.2))
    (card_polarized Prod.swap_swap _ diagonal_preferred_side).symm
    (fun i => diagonal_adjacency_moments _ (i + 1)) hstrict z hz
  change faceDeterminant (polarized (faceStripY m n k) Prod.swap
    (fun x : Vertex => x.1 < x.2)) z < faceDeterminant (faceStripY m n k) z at h
  rw [polarize_faceStripY hmn.le hk] at h
  exact h

theorem orientation_determinant_eq_iff {m n k : ℕ} (hmn : m ≤ n) (hk : k ≤ m)
    (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (faceStripX m n k) z = faceDeterminant (faceStripY m n k) z ↔ m = n ∨ k ≤ 1 := by
  constructor
  · intro heq
    by_contra h
    have hm : m < n := by omega
    have hk2 : 2 ≤ k := by omega
    have hs := orientation_determinant_strict hm hk hk2 z hz
    linarith
  · rintro (rfl | hk1)
    · have h := faceDeterminant_transpose (faceStripY m m k) z
      rw [transpose_faceStripY] at h
      exact h.symm
    · rw [faceStrips_eq_of_short hk1]

def leftPatch (a b l : ℕ) : Domain :=
  rectangle a b ∪ ({(-1 : ℤ)} ×ˢ Finset.Ico (0 : ℤ) l)

def bottomPatch (a b l : ℕ) : Domain :=
  rectangle a b ∪ (Finset.Ico (0 : ℤ) l ×ˢ {(-1 : ℤ)})

@[simp] theorem mem_leftPatch {a b l : ℕ} {v : Vertex} :
    v ∈ leftPatch a b l ↔
      (0 ≤ v.1 ∧ v.1 < a ∧ 0 ≤ v.2 ∧ v.2 < b) ∨
        (v.1 = -1 ∧ 0 ≤ v.2 ∧ v.2 < l) := by
  simp only [leftPatch, Finset.mem_union, mem_rectangle, Finset.mem_product,
    Finset.mem_singleton, Finset.mem_Ico]

@[simp] theorem mem_bottomPatch {a b l : ℕ} {v : Vertex} :
    v ∈ bottomPatch a b l ↔
      (0 ≤ v.1 ∧ v.1 < a ∧ 0 ≤ v.2 ∧ v.2 < b) ∨
        (0 ≤ v.1 ∧ v.1 < l ∧ v.2 = -1) := by
  simp only [bottomPatch, Finset.mem_union, mem_rectangle, Finset.mem_product,
    Finset.mem_singleton, Finset.mem_Ico]
  tauto

theorem polarize_bottomPatch {a b l : ℕ} (hab : a ≤ b) (_hl : l ≤ a) :
    polarized (bottomPatch a b l) Prod.swap (fun x : Vertex => x.1 < x.2) = leftPatch a b l := by
  ext v
  rw [mem_polarized Prod.swap_swap]
  simp only [mem_bottomPatch, mem_leftPatch, Prod.fst_swap, Prod.snd_swap]
  split_ifs <;> omega

theorem patch_determinant {a b l : ℕ} (hab : a ≤ b) (hl : l ≤ a) (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (leftPatch a b l) z ≤ faceDeterminant (bottomPatch a b l) z := by
  have h := adjacency_determinant_of_domain_moments (bottomPatch a b l)
    (polarized (bottomPatch a b l) Prod.swap (fun x : Vertex => x.1 < x.2))
    (card_polarized Prod.swap_swap _ diagonal_preferred_side).symm
    (fun i => diagonal_adjacency_moments _ (i + 1)) z hz
  change faceDeterminant (polarized (bottomPatch a b l) Prod.swap
    (fun x : Vertex => x.1 < x.2)) z ≤ faceDeterminant (bottomPatch a b l) z at h
  rw [polarize_bottomPatch hab hl] at h
  exact h

def patchStrictPath (i : ℕ) : Vertex := if i = 0 then (-1, 1) else (0, i)

theorem patchStrictPath_mem {a b l : ℕ} (hab : a < b) (hl : l ≤ a) (hl2 : 2 ≤ l)
    {i : ℕ} (hi : i ≤ a) :
    patchStrictPath i ∈ preferredDomain (bottomPatch a b l) Prod.swap
      (fun x : Vertex => x.1 < x.2) := by
  rw [preferredDomain, Finset.mem_filter, polarize_bottomPatch hab.le hl]
  simp only [mem_leftPatch, patchStrictPath]
  split_ifs <;> omega

theorem patchStrictPath_adj (i : ℕ) : lattice.Adj (patchStrictPath i) (patchStrictPath (i + 1)) := by
  by_cases hi : i = 0
  · subst i
    norm_num [patchStrictPath, lattice]
  · have hn : i + 1 ≠ 0 := by omega
    simp only [patchStrictPath, ite_eq_right hi, ite_eq_right hn]
    simpa only [Nat.cast_add, Nat.cast_one] using vertical_lattice_step 0 i

theorem patch_opposite {a b l : ℕ} (hab : a < b) (hl : l ≤ a) (hl2 : 2 ≤ l) :
    OppositeSingletons (bottomPatch a b l) Prod.swap (patchStrictPath 0) (patchStrictPath a) := by
  right
  have ha : a ≠ 0 := by omega
  norm_num [patchStrictPath, ha]
  omega

theorem patch_determinant_strict {a b l : ℕ} (hab : a < b) (hl : l ≤ a) (hl2 : 2 ≤ l)
    (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (leftPatch a b l) z < faceDeterminant (bottomPatch a b l) z := by
  let P := preferredDomain (bottomPatch a b l) Prod.swap (fun x : Vertex => x.1 < x.2)
  have hmem : ∀ i, i ≤ a → patchStrictPath i ∈ P := fun _ hi => patchStrictPath_mem hab hl hl2 hi
  obtain ⟨p⟩ := reachable_along P patchStrictPath a hmem (fun i _ => patchStrictPath_adj i)
  have hstrict := ordinary_strict_from_preferred_walk (bottomPatch a b l) Prod.swap
    (fun x : Vertex => x.1 < x.2) Prod.swap_swap diagonal_preferred_side
    diagonal_adjacency_invariant diagonal_no_cross_edge p (patch_opposite hab hl hl2)
  have h := adjacency_strict_determinant_of_domain_moments (bottomPatch a b l)
    (polarized (bottomPatch a b l) Prod.swap (fun x : Vertex => x.1 < x.2))
    (card_polarized Prod.swap_swap _ diagonal_preferred_side).symm
    (fun i => diagonal_adjacency_moments _ (i + 1)) hstrict z hz
  change faceDeterminant (polarized (bottomPatch a b l) Prod.swap
    (fun x : Vertex => x.1 < x.2)) z < faceDeterminant (bottomPatch a b l) z at h
  rw [polarize_bottomPatch hab.le hl] at h
  exact h

theorem mem_bottomPatch_one {a b : ℕ} (x : Vertex) :
    x ∈ bottomPatch a b 1 ↔ x ∈ rectangle a b ∨ x = (0, -1) := by
  rcases x with ⟨x, y⟩
  simp only [mem_bottomPatch, mem_rectangle, Prod.mk.injEq]
  omega

theorem mem_leftPatch_one {a b : ℕ} (x : Vertex) :
    x ∈ leftPatch a b 1 ↔ x ∈ rectangle a b ∨ x = (-1, 0) := by
  rcases x with ⟨x, y⟩
  simp only [mem_leftPatch, mem_rectangle, Prod.mk.injEq]
  omega

def leafSwap : Vertex ≃ Vertex := Equiv.swap (0, -1) (-1, 0)

theorem leafSwap_fixes_core {a b : ℕ} {x : Vertex} (hx : x ∈ rectangle a b) : leafSwap x = x := by
  have hb := mem_rectangle.mp hx
  have h₁ : x ≠ (0, -1) := by intro h; subst x; norm_num at hb
  have h₂ : x ≠ (-1, 0) := by intro h; subst x; norm_num at hb
  exact Equiv.swap_apply_of_ne_of_ne h₁ h₂

theorem leafSwap_mem (a b : ℕ) (x : Vertex) :
    x ∈ bottomPatch a b 1 ↔ leafSwap x ∈ leftPatch a b 1 := by
  rw [mem_bottomPatch_one, mem_leftPatch_one]
  by_cases h₁ : x = (0, -1)
  · subst x
    simp [leafSwap]
  · by_cases h₂ : x = (-1, 0)
    · subst x
      simp [leafSwap, mem_rectangle]
    · rw [show leafSwap x = x from Equiv.swap_apply_of_ne_of_ne h₁ h₂]
      simp only [h₁, h₂, or_false]

theorem lattice_leaf_rotation (x : Vertex) (hx : 0 ≤ x.1) (hy : 0 ≤ x.2) :
    lattice.Adj (-1, 0) x ↔ lattice.Adj (0, -1) x := by
  simp only [lattice, abs_eq (by norm_num : (0 : ℤ) ≤ 1)]
  omega

theorem leafSwap_adj {a b : ℕ} {x y : Vertex}
    (hx : x ∈ bottomPatch a b 1) (hy : y ∈ bottomPatch a b 1) :
    lattice.Adj (leafSwap x) (leafSwap y) ↔ lattice.Adj x y := by
  rcases (mem_bottomPatch_one x).mp hx with hx | rfl
  · rcases (mem_bottomPatch_one y).mp hy with hy | rfl
    · rw [leafSwap_fixes_core hx, leafSwap_fixes_core hy]
    · rw [leafSwap_fixes_core hx]
      simp only [leafSwap, Equiv.swap_apply_left]
      calc
        lattice.Adj x (-1, 0) ↔ lattice.Adj (-1, 0) x := lattice.adj_comm x (-1, 0)
        _ ↔ lattice.Adj (0, -1) x := lattice_leaf_rotation x
          (mem_rectangle.mp hx).1 (mem_rectangle.mp hx).2.2.1
        _ ↔ lattice.Adj x (0, -1) := lattice.adj_comm (0, -1) x
  · rcases (mem_bottomPatch_one y).mp hy with hy | rfl
    · rw [leafSwap_fixes_core hy]
      simp only [leafSwap, Equiv.swap_apply_left]
      exact lattice_leaf_rotation y (mem_rectangle.mp hy).1 (mem_rectangle.mp hy).2.2.1
    · simp [leafSwap, lattice]

noncomputable def leafPatchIso (a b : ℕ) : domainGraph (bottomPatch a b 1) ≃g domainGraph (leftPatch a b 1) :=
  graphIsoOfEquiv leafSwap (leafSwap_mem a b) (fun _ _ hx hy => leafSwap_adj hx hy)

theorem patch_determinant_eq_of_short {a b l : ℕ} (hl : l ≤ 1) (z : ℝ) :
    faceDeterminant (leftPatch a b l) z = faceDeterminant (bottomPatch a b l) z := by
  by_cases hl0 : l = 0
  · subst l
    simp [leftPatch, bottomPatch]
  · have hl1 : l = 1 := by omega
    subst l
    exact (faceDeterminant_iso (leafPatchIso a b) z).symm

theorem patch_determinant_eq_iff {a b l : ℕ} (hab : a < b) (hl : l ≤ a)
    (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (leftPatch a b l) z = faceDeterminant (bottomPatch a b l) z ↔ l ≤ 1 := by
  constructor
  · intro h
    by_contra hn
    have hs := patch_determinant_strict hab hl (by omega) z hz
    linarith
  · intro h
    exact patch_determinant_eq_of_short h z

def translationEquiv (a : Vertex) : Vertex ≃ Vertex where
  toFun := translate a
  invFun := translate (-a)
  left_inv x := by ext <;> simp [translate]
  right_inv x := by ext <;> simp [translate]

def leftCoordinates (b : ℕ) : Vertex ≃ Vertex :=
  (Function.Involutive.toPerm (axialReflection ((b : ℤ) - 1)) (axialReflection_involutive _)).trans
    (translationEquiv (-1, 0))

def bottomCoordinates (a : ℕ) : Vertex ≃ Vertex :=
  (Function.Involutive.toPerm (verticalReflection ((a : ℤ) - 1)) (vertical_involutive _)).trans
    (translationEquiv (0, -1))

@[simp] theorem leftCoordinates_apply (b : ℕ) (x : Vertex) :
    leftCoordinates b x = (-1 + x.1, (b : ℤ) - 1 - x.2) := by
  simp [leftCoordinates, translationEquiv, translate, axialReflection, Function.Involutive.toPerm]

@[simp] theorem bottomCoordinates_apply (a : ℕ) (x : Vertex) :
    bottomCoordinates a x = ((a : ℤ) - 1 - x.1, -1 + x.2) := by
  simp [bottomCoordinates, translationEquiv, translate, verticalReflection, Function.Involutive.toPerm]

theorem leftCoordinates_adj (b : ℕ) (x y : Vertex) :
    lattice.Adj (leftCoordinates b x) (leftCoordinates b y) ↔ lattice.Adj x y := by
  change lattice.Adj (translate (-1, 0) (axialReflection ((b : ℤ) - 1) x))
    (translate (-1, 0) (axialReflection ((b : ℤ) - 1) y)) ↔ _
  rw [translate_adj, axial_adjacency_invariant]

theorem vertical_adjacency_invariant (c : ℤ) (x y : Vertex) :
    lattice.Adj (verticalReflection c x) (verticalReflection c y) ↔ lattice.Adj x y := by
  change lattice.Adj (axialReflection c x.swap).swap (axialReflection c y.swap).swap ↔ _
  rw [diagonal_adjacency_invariant, axial_adjacency_invariant, diagonal_adjacency_invariant]

theorem bottomCoordinates_adj (a : ℕ) (x y : Vertex) :
    lattice.Adj (bottomCoordinates a x) (bottomCoordinates a y) ↔ lattice.Adj x y := by
  change lattice.Adj (translate (0, -1) (verticalReflection ((a : ℤ) - 1) x))
    (translate (0, -1) (verticalReflection ((a : ℤ) - 1) y)) ↔ _
  rw [translate_adj, vertical_adjacency_invariant]

theorem leftCoordinates_mem {a b k l : ℕ} (hb : b = k + l) (x : Vertex) :
    x ∈ faceStripY (a + 1) b k ↔ leftCoordinates b x ∈ leftPatch a b l := by
  simp only [mem_faceStripY, mem_leftPatch, leftCoordinates_apply, Nat.cast_add, Nat.cast_one]
  omega

theorem bottomCoordinates_mem {a b k l : ℕ} (ha : a = k + l) (x : Vertex) :
    x ∈ faceStripX a (b + 1) k ↔ bottomCoordinates a x ∈ bottomPatch a b l := by
  simp only [mem_faceStripX, mem_bottomPatch, bottomCoordinates_apply, Nat.cast_add, Nat.cast_one]
  omega

noncomputable def stripToLeftIso {a b k l : ℕ} (hb : b = k + l) :
    domainGraph (faceStripY (a + 1) b k) ≃g domainGraph (leftPatch a b l) :=
  graphIsoOfEquiv (leftCoordinates b) (leftCoordinates_mem hb) (fun x y _ _ => leftCoordinates_adj b x y)

noncomputable def stripToBottomIso {a b k l : ℕ} (ha : a = k + l) :
    domainGraph (faceStripX a (b + 1) k) ≃g domainGraph (bottomPatch a b l) :=
  graphIsoOfEquiv (bottomCoordinates a) (bottomCoordinates_mem ha) (fun x y _ _ => bottomCoordinates_adj a x y)

theorem adjacent_face_determinant {a b k k' l : ℕ} (hab : a ≤ b) (hl : l ≤ a)
    (hb : b = k + l) (ha : a = k' + l) (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (faceStripY (a + 1) b k) z ≤ faceDeterminant (faceStripX a (b + 1) k') z := by
  rw [faceDeterminant_iso (stripToLeftIso hb) z, faceDeterminant_iso (stripToBottomIso ha) z]
  exact patch_determinant hab hl z hz

theorem adjacent_face_determinant_eq_iff {a b k k' l : ℕ} (hab : a < b) (hl : l ≤ a)
    (hb : b = k + l) (ha : a = k' + l) (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (faceStripY (a + 1) b k) z = faceDeterminant (faceStripX a (b + 1) k') z ↔ l ≤ 1 := by
  rw [faceDeterminant_iso (stripToLeftIso hb) z, faceDeterminant_iso (stripToBottomIso ha) z]
  exact patch_determinant_eq_iff hab hl z hz

/-- The gap condition is explicit because natural subtraction truncates at zero. -/
theorem adjacent_parameters {r s k : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) (hk : k < r)
    (hgap : s - r + 1 ≤ k) :
    2 ≤ r ∧ r - 2 < s - 1 ∧ s - 1 - k ≤ r - 2 ∧
      s - 1 = k + (s - 1 - k) ∧ r - 2 = (k - (s - r + 1)) + (s - 1 - k) ∧
      k - (s - r + 1) ≤ r - 2 := by omega

theorem adjacent_hull_faces {r s k : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) (hk : k < r)
    (hgap : s - r + 1 ≤ k) (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (faceStripY (r - 1) (s - 1) k) z ≤
        faceDeterminant (faceStripX (r - 2) s (k - (s - r + 1))) z ∧
      faceDeterminant (faceStripX (r - 2) s (k - (s - r + 1))) z ≤
        faceDeterminant (faceStripY (r - 2) s (k - (s - r + 1))) z := by
  obtain ⟨hr2, hab, hl, hb, ha, hk'⟩ := adjacent_parameters hr hrs hk hgap
  constructor
  · have h := adjacent_face_determinant hab.le hl hb ha z hz
    have he₁ : r - 2 + 1 = r - 1 := by omega
    have he₂ : s - 1 + 1 = s := by omega
    simpa only [he₁, he₂] using h
  · exact orientation_determinant (by omega) hk' z hz

theorem adjacent_hull_faces_eq_iff {r s k : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) (hk : k < r)
    (hgap : s - r + 1 ≤ k) (z : ℝ) (hz : 4 ≤ z) :
    faceDeterminant (faceStripY (r - 1) (s - 1) k) z =
      faceDeterminant (faceStripY (r - 2) s (k - (s - r + 1))) z ↔
        s - 1 - k ≤ 1 ∧ k - (s - r + 1) ≤ 1 := by
  obtain ⟨hr2, hab, hl, hb, ha, hk'⟩ := adjacent_parameters hr hrs hk hgap
  have hchain := adjacent_hull_faces hr hrs hk hgap z hz
  have hfirst := adjacent_face_determinant_eq_iff hab hl hb ha z hz
  have he₁ : r - 2 + 1 = r - 1 := by omega
  have he₂ : s - 1 + 1 = s := by omega
  rw [he₁, he₂] at hfirst
  have hsecond := orientation_determinant_eq_iff (by omega : r - 2 ≤ s) hk' z hz
  have hnot : r - 2 ≠ s := by omega
  simp only [hnot, false_or] at hsecond
  constructor
  · intro h
    exact ⟨hfirst.mp (by linarith), hsecond.mp (by linarith)⟩
  · rintro ⟨h₁, h₂⟩
    exact (hfirst.mpr h₁).trans (hsecond.mpr h₂)

theorem adjacent_equality_triples {r s k : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) (hk : k < r)
    (hgap : s - r + 1 ≤ k) :
    (s - 1 - k ≤ 1 ∧ k - (s - r + 1) ≤ 1) ↔
      (r, s, k) = (2, 2, 1) ∨ (r, s, k) = (3, 3, 2) ∨ (r, s, k) = (3, 3, 1) ∨
      (r, s, k) = (3, 4, 2) ∨ (r, s, k) = (4, 4, 2) ∨ (r, s, k) = (4, 5, 3) := by
  simp only [Prod.mk.injEq]
  omega

end SpanningTreeIsoperimetry.StripPolarization



