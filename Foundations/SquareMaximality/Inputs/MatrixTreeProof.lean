module

public import SquareMaximality.Inputs.MatrixTree
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

set_option autoImplicit false

/-!
# A proof of the labelled multigraph Matrix--Tree theorem

This file proves the previously explicit `LabeledMultigraphCofactorInput`.
The proof uses the signed incidence matrix, total unimodularity, and the
Cauchy--Binet identity obtained from Mathlib's polynomial principal-minor
formula and the Weinstein--Aronszajn determinant identity.
-/

namespace SquareMaximality
namespace Multigraph
namespace LabeledMultigraph

open scoped BigOperators Matrix Polynomial

noncomputable section

universe uV uE

variable {V : Type uV} {E : Type uE} [DecidableEq V]
    (G : LabeledMultigraph V E)

noncomputable local instance matrixTreeProofDecidableEqE : DecidableEq E :=
  Classical.decEq E
noncomputable local instance (priority := 100) matrixTreeProofDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- An arbitrary orientation of an edge's unordered pair of ends. -/
def kirchhoffSource (e : E) : V := (G.ends e).out.1

/-- The other endpoint in the arbitrary orientation. -/
def kirchhoffTarget (e : E) : V := (G.ends e).out.2

omit [DecidableEq V] in theorem ends_kirchhoffSource_kirchhoffTarget (e : E) :
    G.ends e = s(G.kirchhoffSource e, G.kirchhoffTarget e) := by
  symm
  exact (G.ends e).out_eq

/-- The integral signed vertex-edge incidence matrix. -/
def kirchhoffIncidence : Matrix V E ℤ := fun v e =>
  (if v = G.kirchhoffSource e then 1 else 0) -
    (if v = G.kirchhoffTarget e then 1 else 0)

@[simp] theorem kirchhoffIncidence_apply (v : V) (e : E) :
    G.kirchhoffIncidence v e =
      (if v = G.kirchhoffSource e then 1 else 0) -
        (if v = G.kirchhoffTarget e then 1 else 0) := rfl

theorem kirchhoffIncidence_eq_zero_of_ne (v : V) (e : E)
    (hs : v ≠ G.kirchhoffSource e) (ht : v ≠ G.kirchhoffTarget e) :
    G.kirchhoffIncidence v e = 0 := by
  simp [kirchhoffIncidence, hs, ht]

theorem eq_source_or_eq_target_of_kirchhoffIncidence_ne_zero
    {v : V} {e : E} (h : G.kirchhoffIncidence v e ≠ 0) :
    v = G.kirchhoffSource e ∨ v = G.kirchhoffTarget e := by
  by_contra hnot
  push Not at hnot
  exact h (G.kirchhoffIncidence_eq_zero_of_ne v e hnot.1 hnot.2)

theorem kirchhoffIncidence_column_sum [Fintype V] (e : E) :
    ∑ v, G.kirchhoffIncidence v e = 0 := by
  simp [kirchhoffIncidence, Finset.sum_sub_distrib]

theorem kirchhoffIncidence_mem_sign (v : V) (e : E) :
    G.kirchhoffIncidence v e ∈ Set.range SignType.cast := by
  by_cases hs : v = G.kirchhoffSource e
  · by_cases ht : v = G.kirchhoffTarget e
    · refine ⟨0, ?_⟩
      have hst : G.kirchhoffSource e = G.kirchhoffTarget e := hs.symm.trans ht
      change (0 : ℤ) =
        (if v = G.kirchhoffSource e then 1 else 0) -
          (if v = G.kirchhoffTarget e then 1 else 0)
      simp [hs, hst]
    · refine ⟨1, ?_⟩
      have hst : G.kirchhoffSource e ≠ G.kirchhoffTarget e :=
        fun h => ht (hs.trans h)
      change (1 : ℤ) =
        (if v = G.kirchhoffSource e then 1 else 0) -
          (if v = G.kirchhoffTarget e then 1 else 0)
      simp [hs, hst]
  · by_cases ht : v = G.kirchhoffTarget e
    · refine ⟨-1, ?_⟩
      have hts : G.kirchhoffTarget e ≠ G.kirchhoffSource e :=
        fun h => hs (ht.trans h)
      change (-1 : ℤ) =
        (if v = G.kirchhoffSource e then 1 else 0) -
          (if v = G.kirchhoffTarget e then 1 else 0)
      simp [ht, hts]
    · refine ⟨0, ?_⟩
      change (0 : ℤ) =
        (if v = G.kirchhoffSource e then 1 else 0) -
          (if v = G.kirchhoffTarget e then 1 else 0)
      simp [hs, ht]

private theorem submatrix_column_sum_eq_zero_of_two_nonzero
    {k : ℕ} (f : Fin k → V) (hf : Function.Injective f)
    (g : Fin k → E) (j i₁ i₂ : Fin k) (hi : i₁ ≠ i₂)
    (h₁ : G.kirchhoffIncidence (f i₁) (g j) ≠ 0)
    (h₂ : G.kirchhoffIncidence (f i₂) (g j) ≠ 0) :
    ∑ i, G.kirchhoffIncidence (f i) (g j) = 0 := by
  let s := G.kirchhoffSource (g j)
  let t := G.kirchhoffTarget (g j)
  have hends₁ : f i₁ = s ∨ f i₁ = t :=
    G.eq_source_or_eq_target_of_kirchhoffIncidence_ne_zero h₁
  have hends₂ : f i₂ = s ∨ f i₂ = t :=
    G.eq_source_or_eq_target_of_kirchhoffIncidence_ne_zero h₂
  have hfi : f i₁ ≠ f i₂ := fun h => hi (hf h)
  obtain ⟨iS, hiS, iT, hiT⟩ :
      ∃ iS, f iS = s ∧ ∃ iT, f iT = t := by
    rcases hends₁ with h₁s | h₁t <;>
      rcases hends₂ with h₂s | h₂t
    · exact (hfi (h₁s.trans h₂s.symm)).elim
    · exact ⟨i₁, h₁s, i₂, h₂t⟩
    · exact ⟨i₂, h₂s, i₁, h₁t⟩
    · exact (hfi (h₁t.trans h₂t.symm)).elim
  have hsumS : (∑ i, if f i = s then (1 : ℤ) else 0) = 1 := by
    calc
      (∑ i, if f i = s then (1 : ℤ) else 0) =
          (if f iS = s then 1 else 0) := by
        apply Fintype.sum_eq_single iS
        intro i hne
        rw [if_neg]
        exact fun h => hne (hf (h.trans hiS.symm))
      _ = 1 := by simp [hiS]
  have hsumT : (∑ i, if f i = t then (1 : ℤ) else 0) = 1 := by
    calc
      (∑ i, if f i = t then (1 : ℤ) else 0) =
          (if f iT = t then 1 else 0) := by
        apply Fintype.sum_eq_single iT
        intro i hne
        rw [if_neg]
        exact fun h => hne (hf (h.trans hiT.symm))
      _ = 1 := by simp [hiT]
  simp only [kirchhoffIncidence, Finset.sum_sub_distrib]
  change (∑ i, if f i = s then (1 : ℤ) else 0) -
      (∑ i, if f i = t then (1 : ℤ) else 0) = 0
  rw [hsumS, hsumT, sub_self]

/-- The signed incidence matrix of an edge-labelled multigraph is totally
unimodular.  Loops give zero columns and parallel labels give separate,
identically shaped columns. -/
theorem kirchhoffIncidence_isTotallyUnimodular :
    G.kirchhoffIncidence.IsTotallyUnimodular := by
  intro k f g hf hg
  induction k with
  | zero =>
      refine ⟨1, ?_⟩
      simp
  | succ k ih =>
      let M : Matrix (Fin k.succ) (Fin k.succ) ℤ :=
        G.kirchhoffIncidence.submatrix f g
      by_cases hsparse : ∃ j : Fin k.succ,
          ∀ i₁ i₂ : Fin k.succ, M i₁ j ≠ 0 → M i₂ j ≠ 0 → i₁ = i₂
      · obtain ⟨j, hj⟩ := hsparse
        by_cases hnonzero : ∃ i : Fin k.succ, M i j ≠ 0
        · obtain ⟨i, hi⟩ := hnonzero
          have hminor := ih (f ∘ i.succAbove) (g ∘ j.succAbove)
            (hf.comp i.succAbove_right_injective)
            (hg.comp j.succAbove_right_injective)
          rw [show (G.kirchhoffIncidence.submatrix
              (f ∘ i.succAbove) (g ∘ j.succAbove)) =
              M.submatrix i.succAbove j.succAbove by
                ext a b
                rfl] at hminor
          rw [Matrix.det_succ_column M j, Fintype.sum_eq_single i]
          · change _ ∈ MonoidHom.mrange SignType.castHom.toMonoidHom
            refine mul_mem (mul_mem ?_ ?_) hminor
            · apply pow_mem
              exact ⟨-1, by simp⟩
            · exact G.kirchhoffIncidence_mem_sign (f i) (g j)
          · intro i' hne
            have hzero : M i' j = 0 := by
              by_contra hi'
              exact hne (hj i' i hi' hi)
            simp [hzero]
        · push Not at hnonzero
          refine ⟨0, ?_⟩
          symm
          rw [Matrix.det_succ_column M j]
          apply Finset.sum_eq_zero
          intro i _hi
          simp [hnonzero i]
      · push Not at hsparse
        have hcol (j : Fin k.succ) : ∑ i, M i j = 0 := by
          obtain ⟨i₁, i₂, h₁, h₂, hi⟩ := hsparse j
          exact submatrix_column_sum_eq_zero_of_two_nonzero
            G f hf g j i₁ i₂ hi h₁ h₂
        have hrowsum : (∑ i, M i) = 0 := by
          funext j
          calc
            (∑ i, M i) j = ∑ i, M i j := Finset.sum_apply _ _ _
            _ = 0 := hcol j
        have hupdate := Matrix.det_updateRow_sum M (0 : Fin k.succ)
          (fun _ => (1 : ℤ))
        simp only [one_smul] at hupdate
        rw [hrowsum] at hupdate
        have hzero : (M.updateRow (0 : Fin k.succ) 0).det = 0 := by
          simpa using Matrix.det_updateRow_smul M (0 : Fin k.succ)
            (0 : ℤ) (0 : Fin k.succ → ℤ)
        refine ⟨0, ?_⟩
        exact (hupdate.symm.trans hzero).symm

/-- Delete the root row from the integral incidence matrix. -/
def kirchhoffReducedIncidence (root : V) : Matrix (AwayFrom root) E ℤ :=
  G.kirchhoffIncidence.submatrix Subtype.val id

@[simp] theorem kirchhoffReducedIncidence_apply (root : V)
    (v : AwayFrom root) (e : E) :
    G.kirchhoffReducedIncidence root v e = G.kirchhoffIncidence v.1 e := rfl

private def kirchhoffLinkSignedIndicator (e : E) (u v : V) : ℤ :=
  if G.IsLink e u v then -1 else 0

private theorem kirchhoffIncidence_mul_apply_of_ne
    {u v : V} (huv : u ≠ v) (e : E) :
    G.kirchhoffIncidence u e * G.kirchhoffIncidence v e =
      G.kirchhoffLinkSignedIndicator e u v := by
  have hlink : G.IsLink e u v ↔
      (G.kirchhoffSource e = u ∧ G.kirchhoffTarget e = v) ∨
        (G.kirchhoffSource e = v ∧ G.kirchhoffTarget e = u) := by
    rw [IsLink, G.ends_kirchhoffSource_kirchhoffTarget, Sym2.eq_iff]
  simp only [kirchhoffIncidence, kirchhoffLinkSignedIndicator, hlink]
  by_cases hus : u = G.kirchhoffSource e <;>
    by_cases hut : u = G.kirchhoffTarget e <;>
    by_cases hvs : v = G.kirchhoffSource e <;>
    by_cases hvt : v = G.kirchhoffTarget e <;>
    simp_all [eq_comm]

private theorem kirchhoffIncidenceGram_offDiagonal
    [Fintype E] [Finite V] {u v : V} (huv : u ≠ v) :
    (G.kirchhoffIncidence * G.kirchhoffIncidenceᵀ) u v =
      -(G.adjacencyMultiplicity u v : ℤ) := by
  rw [Matrix.mul_apply]
  simp_rw [Matrix.transpose_apply, kirchhoffIncidence_mul_apply_of_ne G huv]
  simp only [kirchhoffLinkSignedIndicator]
  rw [G.adjacencyMultiplicity_of_ne huv, edgeMultiplicity,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const,
    smul_neg, add_zero]
  rw [nsmul_eq_mul]
  norm_num

private theorem kirchhoffIncidenceGram_row_sum
    [Fintype V] [Fintype E] (u : V) :
    ∑ v, (G.kirchhoffIncidence * G.kirchhoffIncidenceᵀ) u v = 0 := by
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro e _he
  rw [← Finset.mul_sum]
  simp

/-- The integral incidence Gram matrix is exactly the labelled-multigraph
Laplacian used by the rest of the development. -/
theorem kirchhoffIncidence_mul_transpose [Fintype V] [Fintype E] :
    G.kirchhoffIncidence * G.kirchhoffIncidenceᵀ = G.laplacian ℤ := by
  ext u v
  by_cases huv : u = v
  · subst v
    have hrow := kirchhoffIncidenceGram_row_sum G u
    rw [← Finset.univ.add_sum_erase _ (Finset.mem_univ u)] at hrow
    have hoff :
        ∑ x ∈ Finset.univ.erase u,
            (G.kirchhoffIncidence * G.kirchhoffIncidenceᵀ) u x =
          -(G.degree u : ℤ) := by
      calc
        (∑ x ∈ Finset.univ.erase u,
            (G.kirchhoffIncidence * G.kirchhoffIncidenceᵀ) u x) =
            ∑ x ∈ Finset.univ.erase u,
              -(G.adjacencyMultiplicity u x : ℤ) := by
                apply Finset.sum_congr rfl
                intro x hx
                rw [kirchhoffIncidenceGram_offDiagonal G]
                exact Ne.symm (Finset.mem_erase.mp hx).1
        _ = -∑ x ∈ Finset.univ.erase u,
              (G.adjacencyMultiplicity u x : ℤ) := by
                rw [Finset.sum_neg_distrib]
        _ = -(G.degree u : ℤ) := by
          simp only [degree]
          push_cast
          rw [← Finset.univ.add_sum_erase _ (Finset.mem_univ u)]
          simp
    rw [hoff] at hrow
    rw [G.laplacian_diagonal]
    omega
  · rw [kirchhoffIncidenceGram_offDiagonal G huv,
      G.laplacian_offDiagonal ℤ huv]

/-- Root-row deletion commutes with the integral incidence Gram
factorization. -/
theorem kirchhoffReducedIncidence_mul_transpose
    [Fintype V] [Fintype E] (root : V) :
    G.kirchhoffReducedIncidence root *
        (G.kirchhoffReducedIncidence root)ᵀ =
      G.reducedLaplacian ℤ root := by
  ext u v
  simp only [Matrix.mul_apply, kirchhoffReducedIncidence,
    Matrix.submatrix_apply, Matrix.transpose_apply, reducedLaplacian_apply]
  have hfull := congrArg (fun M : Matrix V V ℤ => M u.1 v.1)
    (G.kirchhoffIncidence_mul_transpose)
  rw [Matrix.mul_apply] at hfull
  exact hfull

/-- The canonical cardinality equivalence used to make a selected incidence
minor square. -/
def awayEquivSelectedEdge (_G : LabeledMultigraph V E)
    [Fintype V] (root : V) (F : Finset E)
    (hcard : F.card + 1 = Fintype.card V) :
    AwayFrom root ≃ {e : E // e ∈ F} := by
  classical
  apply Fintype.equivOfCardEq
  have hAway : Fintype.card (AwayFrom root) = Fintype.card V - 1 := by
    change Fintype.card {v : V // ¬v = root} = _
    rw [Fintype.card_subtype_compl]
    simp
  rw [hAway, Fintype.card_coe]
  omega

/-- A square root-deleted incidence minor for a set of `|V|-1` labels. -/
def selectedIncidenceMinor [Fintype V] (root : V) (F : Finset E)
    (hcard : F.card + 1 = Fintype.card V) :
    Matrix (AwayFrom root) (AwayFrom root) ℤ :=
  G.kirchhoffIncidence.submatrix Subtype.val
    (fun i => (G.awayEquivSelectedEdge root F hcard i).1)

theorem selectedIncidenceMinor_det_mem_sign [Fintype V]
    (root : V) (F : Finset E) (hcard : F.card + 1 = Fintype.card V) :
    (G.selectedIncidenceMinor root F hcard).det ∈ Set.range SignType.cast := by
  have hTU := G.kirchhoffIncidence_isTotallyUnimodular
  rw [Matrix.isTotallyUnimodular_iff_fintype] at hTU
  exact hTU (AwayFrom root)
    Subtype.val (fun i => (G.awayEquivSelectedEdge root F hcard i).1)

/-- Extend root-deleted coordinates by the value zero at the root. -/
def extendAwayByZero (_G : LabeledMultigraph V E)
    [Fintype V] (root : V) (x : AwayFrom root → ℤ) : V → ℤ :=
  fun v => if h : v ≠ root then x ⟨v, h⟩ else 0

@[simp] theorem extendAwayByZero_root [Fintype V] (root : V)
    (x : AwayFrom root → ℤ) : G.extendAwayByZero root x root = 0 := by
  simp [extendAwayByZero]

@[simp] theorem extendAwayByZero_apply [Fintype V] (root : V)
    (x : AwayFrom root → ℤ) (v : AwayFrom root) :
    G.extendAwayByZero root x v.1 = x v := by
  simp [extendAwayByZero, v.property]

private theorem sum_away_indicator_mul [Fintype V] (root a : V)
    (x : AwayFrom root → ℤ) :
    (∑ v : AwayFrom root, (if v.1 = a then (1 : ℤ) else 0) * x v) =
      G.extendAwayByZero root x a := by
  classical
  by_cases ha : a = root
  · subst a
    rw [G.extendAwayByZero_root]
    apply Finset.sum_eq_zero
    intro v _hv
    simp [v.property]
  · rw [Fintype.sum_eq_single (⟨a, ha⟩ : AwayFrom root)]
    · simp [extendAwayByZero, ha]
    · intro v hv
      have hne : v.1 ≠ a := fun h => hv (Subtype.ext h)
      simp [hne]

private theorem selectedIncidenceMinor_transpose_mulVec_apply [Fintype V]
    (root : V) (F : Finset E) (hcard : F.card + 1 = Fintype.card V)
    (x : AwayFrom root → ℤ) (i : AwayFrom root) :
    ((G.selectedIncidenceMinor root F hcard)ᵀ *ᵥ x) i =
      G.extendAwayByZero root x
          (G.kirchhoffSource (G.awayEquivSelectedEdge root F hcard i).1) -
        G.extendAwayByZero root x
          (G.kirchhoffTarget (G.awayEquivSelectedEdge root F hcard i).1) := by
  classical
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    selectedIncidenceMinor, Matrix.submatrix_apply, kirchhoffIncidence,
    sub_mul, Finset.sum_sub_distrib]
  rw [sum_away_indicator_mul G, sum_away_indicator_mul G]

private theorem extendAwayByZero_eq_on_selected_edge [Fintype V]
    (root : V) (F : Finset E) (hcard : F.card + 1 = Fintype.card V)
    (x : AwayFrom root → ℤ)
    (hx : (G.selectedIncidenceMinor root F hcard)ᵀ *ᵥ x = 0)
    {e : E} (he : e ∈ F) :
    G.extendAwayByZero root x (G.kirchhoffSource e) =
      G.extendAwayByZero root x (G.kirchhoffTarget e) := by
  let i : AwayFrom root :=
    (G.awayEquivSelectedEdge root F hcard).symm ⟨e, he⟩
  have hi : (G.awayEquivSelectedEdge root F hcard i).1 = e := by
    exact congrArg Subtype.val
      ((G.awayEquivSelectedEdge root F hcard).apply_symm_apply ⟨e, he⟩)
  have hz := congrFun hx i
  rw [selectedIncidenceMinor_transpose_mulVec_apply G] at hz
  simp only [Pi.zero_apply, hi] at hz
  exact sub_eq_zero.mp hz

private theorem extendAwayByZero_eq_of_selected_adj [Fintype V]
    (root : V) (F : Finset E) (hcard : F.card + 1 = Fintype.card V)
    (x : AwayFrom root → ℤ)
    (hx : (G.selectedIncidenceMinor root F hcard)ᵀ *ᵥ x = 0)
    {u v : V} (huv : (G.simpleGraphOn (F : Set E)).Adj u v) :
    G.extendAwayByZero root x u = G.extendAwayByZero root x v := by
  obtain ⟨_hne, e, he, hlink⟩ := huv
  have hedge := extendAwayByZero_eq_on_selected_edge G root F hcard x hx he
  have horient :
      (G.kirchhoffSource e = u ∧ G.kirchhoffTarget e = v) ∨
        (G.kirchhoffSource e = v ∧ G.kirchhoffTarget e = u) := by
    apply Sym2.eq_iff.mp
    calc
      s(G.kirchhoffSource e, G.kirchhoffTarget e) = G.ends e :=
        (G.ends_kirchhoffSource_kirchhoffTarget e).symm
      _ = s(u, v) := hlink
  rcases horient with h | h
  · simpa [h.1, h.2] using hedge
  · simpa [h.1, h.2] using hedge.symm

private theorem extendAwayByZero_eq_of_selected_walk [Fintype V]
    (root : V) (F : Finset E) (hcard : F.card + 1 = Fintype.card V)
    (x : AwayFrom root → ℤ)
    (hx : (G.selectedIncidenceMinor root F hcard)ᵀ *ᵥ x = 0)
    {u v : V} (p : (G.simpleGraphOn (F : Set E)).Walk u v) :
    G.extendAwayByZero root x u = G.extendAwayByZero root x v := by
  induction p with
  | nil => rfl
  | @cons u v w huv p ih =>
      exact (extendAwayByZero_eq_of_selected_adj G root F hcard x hx huv).trans ih

private theorem selectedIncidenceMinor_transpose_kernel_eq_zero_of_connected
    [Fintype V] (root : V) (F : Finset E)
    (hcard : F.card + 1 = Fintype.card V)
    (hconn : (G.simpleGraphOn (F : Set E)).Connected)
    (x : AwayFrom root → ℤ)
    (hx : (G.selectedIncidenceMinor root F hcard)ᵀ *ᵥ x = 0) : x = 0 := by
  funext v
  obtain ⟨p⟩ := hconn v.1 root
  have hp := extendAwayByZero_eq_of_selected_walk G root F hcard x hx p
  simpa using hp

/-- A selected square incidence minor is nonsingular whenever the selected
labels form a spanning tree. -/
theorem selectedIncidenceMinor_det_ne_zero_of_isSpanningTree
    [Fintype V] (root : V) (F : Finset E)
    (hF : G.IsSpanningTree F) :
    (G.selectedIncidenceMinor root F hF.card_edges_add_one).det ≠ 0 := by
  intro hdet
  let M := G.selectedIncidenceMinor root F hF.card_edges_add_one
  have hdetT : Mᵀ.det = 0 := by
    simpa [Matrix.det_transpose] using hdet
  obtain ⟨x, hxne, hx⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdetT
  apply hxne
  exact selectedIncidenceMinor_transpose_kernel_eq_zero_of_connected
    G root F hF.card_edges_add_one hF.selected_connected x hx

/-- The determinant square of a spanning-tree incidence minor is one. -/
theorem selectedIncidenceMinor_det_sq_of_isSpanningTree
    [Fintype V] (root : V) (F : Finset E)
    (hF : G.IsSpanningTree F) :
    (G.selectedIncidenceMinor root F hF.card_edges_add_one).det ^ 2 = 1 := by
  have hsign := G.selectedIncidenceMinor_det_mem_sign root F hF.card_edges_add_one
  obtain ⟨s, hs⟩ := hsign
  have hne := G.selectedIncidenceMinor_det_ne_zero_of_isSpanningTree root F hF
  have hdet := hs.symm
  rw [hdet] at hne ⊢
  cases s <;> simp_all

private theorem selectedIncidenceMinor_det_eq_zero_of_loop
    [Fintype V] (root : V) (F : Finset E)
    (hcard : F.card + 1 = Fintype.card V)
    {e : E} (he : e ∈ F) (hloop : G.IsLoop e) :
    (G.selectedIncidenceMinor root F hcard).det = 0 := by
  let M := G.selectedIncidenceMinor root F hcard
  let j : AwayFrom root :=
    (G.awayEquivSelectedEdge root F hcard).symm ⟨e, he⟩
  have hj : (G.awayEquivSelectedEdge root F hcard j).1 = e := by
    exact congrArg Subtype.val
      ((G.awayEquivSelectedEdge root F hcard).apply_symm_apply ⟨e, he⟩)
  have hst : G.kirchhoffSource e = G.kirchhoffTarget e := by
    change (G.ends e).IsDiag at hloop
    rw [G.ends_kirchhoffSource_kirchhoffTarget, Sym2.mk_isDiag_iff] at hloop
    exact hloop
  have hcol : M.col j = 0 := by
    funext v
    simp [M, selectedIncidenceMinor, hj, kirchhoffIncidence, hst]
  have hvec : (Pi.single j (1 : ℤ) : AwayFrom root → ℤ) ≠ 0 := by
    intro hzero
    have := congrFun hzero j
    simp at this
  apply (Matrix.exists_mulVec_eq_zero_iff).mp
  refine ⟨Pi.single j 1, hvec, ?_⟩
  rw [Matrix.mulVec_single_one, hcol]

private theorem selectedIncidenceMinor_det_eq_zero_of_not_connected
    [Fintype V] (root : V) (F : Finset E)
    (hcard : F.card + 1 = Fintype.card V)
    (hconn : ¬(G.simpleGraphOn (F : Set E)).Connected) :
    (G.selectedIncidenceMinor root F hcard).det = 0 := by
  let K := G.simpleGraphOn (F : Set E)
  have hnotUniversal : ¬(∃ v, ∀ w, K.Reachable v w) := by
    exact fun h => hconn ((SimpleGraph.connected_iff_exists_forall_reachable K).mpr h)
  push Not at hnotUniversal
  obtain ⟨v, hvroot⟩ := hnotUniversal root
  have hvr : v ≠ root := by
    intro h
    subst v
    exact hvroot SimpleGraph.Reachable.rfl
  let x : AwayFrom root → ℤ := fun w => if K.Reachable v w.1 then 1 else 0
  have hxne : x ≠ 0 := by
    intro hx
    have hz := congrFun hx (⟨v, hvr⟩ : AwayFrom root)
    simp [x] at hz
  have hext (w : V) :
      G.extendAwayByZero root x w = if K.Reachable v w then 1 else 0 := by
    by_cases hw : w = root
    · subst w
      have hvroot' : ¬K.Reachable v root := fun h => hvroot h.symm
      simp [hvroot']
    · simp [extendAwayByZero, x, hw]
  have hxker : (G.selectedIncidenceMinor root F hcard)ᵀ *ᵥ x = 0 := by
    funext i
    rw [selectedIncidenceMinor_transpose_mulVec_apply G]
    let e := (G.awayEquivSelectedEdge root F hcard i).1
    have he : e ∈ F := (G.awayEquivSelectedEdge root F hcard i).2
    rw [hext, hext]
    by_cases hst : G.kirchhoffSource e = G.kirchhoffTarget e
    · change
        (if K.Reachable v (G.kirchhoffSource e) then 1 else 0) -
            (if K.Reachable v (G.kirchhoffTarget e) then 1 else 0) = 0
      rw [hst, sub_self]
    · have hadj : K.Adj (G.kirchhoffSource e) (G.kirchhoffTarget e) := by
        refine ⟨hst, e, he, ?_⟩
        exact G.ends_kirchhoffSource_kirchhoffTarget e
      have hreach :
          K.Reachable v (G.kirchhoffSource e) ↔
            K.Reachable v (G.kirchhoffTarget e) := by
        constructor
        · exact fun h => h.trans hadj.reachable
        · exact fun h => h.trans hadj.symm.reachable
      simp only [Pi.zero_apply]
      rw [if_congr hreach rfl rfl, sub_self]
  have hdetT : (G.selectedIncidenceMinor root F hcard)ᵀ.det = 0 :=
    (Matrix.exists_mulVec_eq_zero_iff).mp ⟨x, hxne, hxker⟩
  simpa [Matrix.det_transpose] using hdetT

/-- Exact classification of a square selected incidence minor. -/
theorem selectedIncidenceMinor_det_sq
    [Fintype V] (root : V) (F : Finset E)
    (hcard : F.card + 1 = Fintype.card V) :
    (G.selectedIncidenceMinor root F hcard).det ^ 2 =
      if G.IsSpanningTree F then 1 else 0 := by
  by_cases hF : G.IsSpanningTree F
  · have hcardEq : hF.card_edges_add_one = hcard := Subsingleton.elim _ _
    subst hcardEq
    simp only [hF, if_true]
    exact G.selectedIncidenceMinor_det_sq_of_isSpanningTree root F hF
  · rw [if_neg hF]
    have hfail : (∃ e ∈ F, G.IsLoop e) ∨
        ¬(G.simpleGraphOn (F : Set E)).Connected := by
      by_contra h
      push Not at h
      exact hF ⟨h.1, h.2, hcard⟩
    rcases hfail with ⟨e, he, hloop⟩ | hconn
    · rw [G.selectedIncidenceMinor_det_eq_zero_of_loop root F hcard he hloop]
      norm_num
    · rw [G.selectedIncidenceMinor_det_eq_zero_of_not_connected root F hcard hconn]
      norm_num

end

end LabeledMultigraph
end Multigraph
end SquareMaximality
