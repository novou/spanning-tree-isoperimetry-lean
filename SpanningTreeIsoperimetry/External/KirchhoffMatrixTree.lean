module

/-
Copyright (c) 2026 Ho Boon Suan.
Released under the MIT license; see LICENSE-FerrersBound in this directory.
Source: https://github.com/boonsuan/FerrersBound
Revision: 49bdf47cc096f37a4abe3eebf09a327a590fba81
Original path: FerrersBound/Graph/KirchhoffMatrixTreeCore.lean
Ported to Lean/mathlib 4.34.1 with API and tactic compatibility changes.
-/

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Dart
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators Matrix
open Matrix Finset

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-!
# Kirchhoff matrix-tree theorem

This file proves Kirchhoff's matrix-tree theorem for finite simple graphs,
using the Cauchy–Binet formula and a characterization of spanning trees
via the signed incidence matrix.

It is used by `FerrersBound.Graph.KirchhoffMatrixTree` to bridge the generic
`SimpleGraph` theorem back to the bundled `BipartiteData` wrapper used in the
Ferrers-bound proof.
-/

universe u

/-!
## Cauchy–Binet formula

We prove the Cauchy–Binet formula in the "function form":
`det(A * B) = ∑ f : m → n, (∏ i, A i (f i)) * det(B.submatrix f id)`
and then restrict to injective functions.
-/
section CauchyBinet

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]


theorem Matrix.det_mul_sum (A : Matrix m n R) (B : Matrix n m R) :
    (A * B).det = ∑ f : m → n, (∏ i, A i (f i)) * (B.submatrix f id).det := by
  -- Expand det(A * B) using Matrix.det_apply'.
  have h_det : Matrix.det (A * B) = ∑ σ : Equiv.Perm m, (Equiv.Perm.sign σ) * ∏ i, (A * B) i (σ i) := by
    rw [ ← Matrix.det_transpose, Matrix.det_apply' ];
    rfl;
  -- Each entry (A*B)_{i,σ(i)} = Σ_k A_{i,k} * B_{k,σ(i)} by Matrix.mul_apply.
  have h_mul : ∀ σ : Equiv.Perm m, ∏ i, (A * B) i (σ i) = ∑ f : m → n, (∏ i, A i (f i)) * (∏ i, B (f i) (σ i)) := by
    simp +decide only [← prod_mul_distrib];
    exact fun σ => Fintype.prod_sum fun i j => (fun j => A i j) j * (fun j => B j (σ i)) j
  simp_all +decide [ Matrix.det_apply' ];
  simp +decide only [Finset.mul_sum _ _ _];
  rw [ Finset.sum_comm ];
  refine' Finset.sum_congr rfl fun f _ => _;
  refine' Finset.sum_bij ( fun σ _ => σ⁻¹ ) _ _ _ _ <;> simp +decide [ mul_assoc, mul_comm, mul_left_comm ];
  · exact fun σ => ⟨ σ⁻¹, inv_inv σ ⟩;
  · intro σ; rw [ ← Equiv.prod_comp σ⁻¹ ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
    rw [ ← Equiv.prod_comp σ⁻¹ ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ;


theorem Matrix.det_submatrix_eq_zero_of_not_injective (B : Matrix n m R)
    (f : m → n) (hf : ¬Function.Injective f) :
    (B.submatrix f id).det = 0 := by
  -- Since $f$ is not injective, there exist $i \ne j$ such that $f(i) = f(j)$.
  obtain ⟨i, j, hij, hfij⟩ : ∃ i j : m, i ≠ j ∧ f i = f j := by
    simpa [ Function.Injective, and_comm ] using hf;
  apply Matrix.det_zero_of_row_eq hij;
  aesop


theorem cauchyBinetEmbedding (A : Matrix m n R) (B : Matrix n m R) :
    (A * B).det = ∑ f : m ↪ n, (∏ i, A i (f i)) * (B.submatrix (⇑f) id).det := by
  -- Apply the Cauchy-Binet formula to expand the determinant.
  have h_det : (A * B).det = ∑ f : m → n, (∏ i, A i (f i)) * (B.submatrix f id).det := by
    have := Matrix.det_mul_sum A B
    exact this;
  rw [ h_det, ← Finset.sum_subset ( Finset.subset_univ { f : m → n | Function.Injective f } ) ];
  · refine' Finset.sum_bij ( fun f hf => ⟨ f, (Finset.mem_filter_univ f).mp hf ⟩ ) _ _ _ _ <;> simp +decide [ Function.Injective ] at * ;
    exact fun b => ⟨ b, b.injective, rfl ⟩;
  · exact fun f _ hf => mul_eq_zero_of_right _ ( Matrix.det_submatrix_eq_zero_of_not_injective _ _ fun h => hf <| by aesop )

end CauchyBinet

namespace SimpleGraph

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable section

/-- The vertex type obtained by deleting `q`. -/
abbrev DelVert (_G : SimpleGraph V) (q : V) := {v : V // v ≠ q}

/-- The reduced Laplacian obtained by deleting the row and column indexed by `q`. -/
def reducedLaplacian (R : Type*) [AddGroupWithOne R] (q : V) :
    Matrix (G.DelVert q) (G.DelVert q) R :=
  (G.lapMatrix R).submatrix (fun i => (i : V)) (fun j => (j : V))

@[simp]
theorem reducedLaplacian_apply (R : Type*) [AddGroupWithOne R] (q : V)
    (i j : G.DelVert q) :
    G.reducedLaplacian R q i j = G.lapMatrix R i j := rfl

/-- Spanning trees of a simple graph. -/
def SpanningTree :=
  {T : SimpleGraph V // T ≤ G ∧ T.IsTree}

/-- The combinatorial spanning-tree count. -/
def spanningTreeCount : ℕ :=
  Nat.card G.SpanningTree

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem spanningTreeCount_eq_natCard :
    G.spanningTreeCount = Nat.card G.SpanningTree := rfl

/-- A choice of one orientation for each edge of `G`. -/
structure EdgeOrientation where
  toDart : ↥G.edgeSet → G.Dart
  edge_toDart : ∀ e, (toDart e).edge = e

attribute [simp] EdgeOrientation.edge_toDart

namespace EdgeOrientation

variable {G}

/-- The signed incidence matrix attached to a chosen orientation. -/
def signedIncMatrix (o : G.EdgeOrientation) : Matrix V ↥G.edgeSet ℤ :=
  fun v e =>
    if v = (o.toDart e).fst then 1
    else if v = (o.toDart e).snd then -1
    else 0

/-- The signed incidence matrix with the row indexed by `q` deleted. -/
def deletedSignedIncMatrix (o : G.EdgeOrientation) (q : V) :
    Matrix (G.DelVert q) ↥G.edgeSet ℤ :=
  (o.signedIncMatrix).submatrix (fun i => (i : V)) id


theorem signedIncMatrix_mul_transpose_eq_lapMatrix (o : G.EdgeOrientation) :
    o.signedIncMatrix * o.signedIncMatrix.transpose = G.lapMatrix ℤ := by
  ext v w; by_cases hvw : v = w <;> simp +decide [ hvw, Matrix.mul_apply ] ;
  · -- Since $N_{we}$ is either $1$ or $-1$ when $w$ is incident to $e$, squaring it gives $1$. Thus, the sum counts the number of edges incident to $w$, which is the degree of $w$.
    have h_deg : ∑ e : G.edgeSet, (o.signedIncMatrix w e) * (o.signedIncMatrix w e) = ∑ e : G.edgeSet, if w ∈ e.val then 1 else 0 := by
      refine' Finset.sum_congr rfl fun e he => _;
      unfold EdgeOrientation.signedIncMatrix;
      have := o.edge_toDart e; simp_all +decide [ SimpleGraph.Dart.edge ] ;
      grind;
    simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ];
    convert congr_arg ( fun x : ℕ => x : ℕ → ℤ ) ( SimpleGraph.card_incidenceFinset_eq_degree G w ) using 1;
    · refine' congr_arg _ ( Finset.card_bij ( fun e _ => e.val ) _ _ _ ) <;> simp +decide [ SimpleGraph.incidenceFinset ];
      · simp +contextual [ SimpleGraph.incidenceSet ];
      · simp +contextual [ SimpleGraph.incidenceSet ];
    · unfold lapMatrix; simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ] ;
      unfold degMatrix; simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ] ;
  · -- For any edge $e$, if $v$ and $w$ are adjacent, then $e$ contributes $-1$ to the sum. Otherwise, it contributes $0$.
    have h_edge_contribution : ∀ e : G.edgeSet, (o.signedIncMatrix v e) * (o.signedIncMatrix w e) = if G.Adj v w ∧ e.val = s(v, w) then -1 else 0 := by
      intro e
      simp [signedIncMatrix];
      have := o.edge_toDart e; simp_all +decide [ SimpleGraph.Dart.edge ] ;
      split_ifs <;> simp_all +decide [ SimpleGraph.adj_comm ];
      · exact ‹¬_› ( by rw [ ← this ] ; exact Sym2.eq_swap );
      · grind +ring;
      · grind +ring;
      · grind +ring;
    simp_all +decide [ lapMatrix ];
    by_cases h : G.Adj v w <;> simp +decide [ h, degMatrix ];
    · rw [ Finset.sum_eq_single ⟨ s(v, w), by simpa using h ⟩ ] <;> aesop;
    · rw [ diagonal_apply_ne ] ; aesop


theorem deletedSignedIncMatrix_mul_transpose_eq_reducedLaplacian
    (o : G.EdgeOrientation) (q : V) :
    o.deletedSignedIncMatrix q * (o.deletedSignedIncMatrix q).transpose =
      G.reducedLaplacian ℤ q := by
  rw [reducedLaplacian, ← signedIncMatrix_mul_transpose_eq_lapMatrix o]
  ext i j
  simp [deletedSignedIncMatrix, Matrix.mul_apply, Matrix.submatrix, Matrix.transpose]

end EdgeOrientation


lemma EdgeOrientation.exists : Nonempty G.EdgeOrientation := by
  by_contra! h_contra;
  -- For each edge $e$, choose one of the two possible orientations.
  have h_orientation : ∀ e ∈ G.edgeSet, ∃ d : G.Dart, d.edge = e := by
    intro e he; cases' e with u v; simp_all +decide [ SimpleGraph.mem_edgeSet ] ;
    exact ⟨ ⟨ ( u, v ), he ⟩, rfl ⟩;
  exact h_contra.elim ⟨ fun e => Classical.choose ( h_orientation e e.2 ), fun e => Classical.choose_spec ( h_orientation e e.2 ) ⟩ ;


set_option maxHeartbeats 800000 in
lemma det_of_atMostOnePosOneNeg
    (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hcol : ∀ j : Fin n,
      (Finset.univ.filter (fun i => A i j = 1)).card ≤ 1 ∧
      (Finset.univ.filter (fun i => A i j = -1)).card ≤ 1 ∧
      (∀ i, A i j = 0 ∨ A i j = 1 ∨ A i j = -1)) :
    A.det = 0 ∨ A.det = 1 ∨ A.det = -1 := by
  -- By induction on $n$.
  induction' n with n ih;
  · norm_num +zetaDelta at *;
  · by_cases h : ∃ j, ∀ i, A i j = 0;
    · exact Or.inl <| Matrix.det_eq_zero_of_column_eq_zero _ h.choose_spec;
    · by_cases h : ∃ j, ∃! i, A i j ≠ 0;
      · obtain ⟨ j, ⟨ i, hi₁, hi₂ ⟩ ⟩ := h
        have h_det : Matrix.det A = (-1) ^ (i.val + j.val) * A i j * Matrix.det (Matrix.submatrix A (Fin.succAbove i) (Fin.succAbove j)) := by
          rw [ Matrix.det_succ_column _ j ];
          rw [ Finset.sum_eq_single i ] <;> simp +contextual [ hi₁, hi₂ ];
          exact fun k hk => Or.inl <| Classical.not_not.1 fun hk' => hk <| hi₂ k hk' ▸ rfl;
        specialize ih ( Matrix.submatrix A ( Fin.succAbove i ) ( Fin.succAbove j ) ) ; simp_all +decide [ Finset.card_image_of_injective, Function.Injective ] ;
        specialize ih ( fun k => ?_ ) ; rcases hcol ( Fin.succAbove j k ) with ⟨ hk₁, hk₂, hk₃ ⟩ ; simp_all +decide [ Finset.card_image_of_injective, Function.Injective ] ;
        · constructor
          · refine le_trans ?_ (hcol (Fin.succAbove j k)).1
            rw [← Finset.card_image_of_injective
              (Finset.univ.filter (fun x : Fin n => A (Fin.succAbove i x) (Fin.succAbove j k) = 1))
              (Fin.succAbove_right_injective (p := i))]
            apply Finset.card_mono
            intro x hx
            obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
          · refine le_trans ?_ (hcol (Fin.succAbove j k)).2.1
            rw [← Finset.card_image_of_injective
              (Finset.univ.filter (fun x : Fin n => A (Fin.succAbove i x) (Fin.succAbove j k) = -1))
              (Fin.succAbove_right_injective (p := i))]
            apply Finset.card_mono
            intro x hx
            obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
        · rcases hcol j with ⟨ hj₁, hj₂, hj₃ ⟩ ; rcases hj₃ i with ha | ha | ha <;> simp_all +decide [ pow_add ] ;
          · rcases ih with ( ih | ih | ih ) <;> norm_num [ ih ];
            · cases' Nat.even_or_odd ( i : ℕ ) with hi hi <;> cases' Nat.even_or_odd ( j : ℕ ) with hj hj <;> rw [ hi.neg_one_pow, hj.neg_one_pow ] <;> norm_num;
            · cases' Nat.even_or_odd ( i : ℕ ) with hi hi <;> cases' Nat.even_or_odd ( j : ℕ ) with hj hj <;> rw [ hi.neg_one_pow, hj.neg_one_pow ] <;> norm_num;
          · rcases ih with ( ih | ih | ih ) <;> norm_num [ ih ];
            · by_cases hi : Even ( i : ℕ ) <;> by_cases hj : Even ( j : ℕ ) <;> simp_all +decide [ Nat.even_add ];
            · by_cases hi : Even ( i : ℕ ) <;> by_cases hj : Even ( j : ℕ ) <;> simp_all +decide [ Nat.even_add ];
      · -- Since every column has at least two non-zero entries, each column must have exactly one +1 and one -1.
        have h_col_sum : ∀ j, ∑ i, A i j = 0 := by
          intro j
          have h_col_sum : ∑ i, A i j = ∑ i ∈ Finset.univ.filter (fun i => A i j = 1), 1 + ∑ i ∈ Finset.univ.filter (fun i => A i j = -1), -1 := by
            rw [ Finset.sum_filter, Finset.sum_filter ] ; rw [ ← Finset.sum_add_distrib ] ; exact Finset.sum_congr rfl fun i hi => by rcases hcol j |>.2.2 i with h | h | h <;> norm_num [ h ] ;
          have h_col_sum : Finset.card (Finset.univ.filter (fun i => A i j = 1)) = 1 ∧ Finset.card (Finset.univ.filter (fun i => A i j = -1)) = 1 := by
            have h_col_sum : Finset.card (Finset.univ.filter (fun i => A i j = 1)) + Finset.card (Finset.univ.filter (fun i => A i j = -1)) ≥ 2 := by
              have h_col_sum : Finset.card (Finset.univ.filter (fun i => A i j ≠ 0)) ≥ 2 := by
                contrapose! h;
                interval_cases _ : Finset.card _ <;> simp_all +decide [ Finset.card_eq_one ];
                · exact absurd ( h j ) ( by tauto );
                · obtain ⟨ i, hi ⟩ := ‹∃ i, _›; use j, i; simp_all +decide [ Finset.eq_singleton_iff_unique_mem ] ;
              rw [ ← Finset.card_union_of_disjoint ];
              · exact h_col_sum.trans ( Finset.card_mono <| fun i hi => by specialize hcol j; rcases hcol.2.2 i with h | h | h <;> aesop );
              · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
            exact ⟨ by linarith [ hcol j ], by linarith [ hcol j ] ⟩;
          aesop;
        -- Since the sum of the rows is zero, the rows are linearly dependent.
        have h_lin_dep : ∃ v : Fin (n + 1) → ℤ, v ≠ 0 ∧ ∑ i, v i • A i = 0 := by
          refine ⟨fun _ => 1, fun h => by simpa using congr_fun h 0, ?_⟩
          funext j
          simp only [Pi.zero_apply, Pi.smul_apply, one_smul]
          exact (Finset.sum_apply j Finset.univ (fun i => A i)).trans (h_col_sum j)
        obtain ⟨ v, hv_ne_zero, hv_sum ⟩ := h_lin_dep;
        rw [ ← Matrix.exists_vecMul_eq_zero_iff ];
        exact Or.inl ⟨ v, hv_ne_zero, by simpa [ funext_iff, Matrix.vecMul, dotProduct ] using hv_sum ⟩


lemma reducedLaplacian_det_ne_zero_of_connected
    (hconn : G.Connected) (q : V) :
    (G.reducedLaplacian ℝ q).det ≠ 0 := by
  by_contra h_det_zero
  obtain ⟨x, hx_nonzero, hx_zero⟩ : ∃ x : G.DelVert q → ℝ, x ≠ 0 ∧ (G.reducedLaplacian ℝ q).mulVec x = 0 := by
    exact Matrix.exists_mulVec_eq_zero_iff.mpr h_det_zero
  set x_tilde : V → ℝ := fun v => if h : v = q then 0 else x ⟨v, h⟩
  have hx_tilde_zero : (G.lapMatrix ℝ).mulVec x_tilde = 0 := by
    ext v; by_cases hv : v = q <;> simp_all +decide [ Matrix.mulVec, dotProduct ] ;
    · -- Since $L * 1 = 0$, we have $1ᵀ * (L * x_tilde) = 0$.
      have h_sum_zero : ∑ v, (G.lapMatrix ℝ).mulVec x_tilde v = 0 := by
        have h_sum_zero : ∑ v, (G.lapMatrix ℝ).mulVec x_tilde v = ∑ v, (G.lapMatrix ℝ).mulVec (fun _ => 1) v * x_tilde v := by
          simp +decide [ Matrix.mulVec, dotProduct ];
          rw [ Finset.sum_comm ] ; simp +decide [ Finset.sum_mul _ _ _ ] ; ring_nf;
          simp +decide [ lapMatrix, SimpleGraph.adjMatrix ] ; ring_nf;
          simp +decide [ degMatrix, SimpleGraph.adj_comm ];
          simp +decide [ diagonal ];
        have h_sum_zero : ∀ v, (G.lapMatrix ℝ).mulVec (fun _ => 1) v = 0 := by
          simp +decide [ Matrix.mulVec, dotProduct, SimpleGraph.lapMatrix ];
          simp +decide [ degMatrix ];
          simp +decide [ diagonal, SimpleGraph.degree, SimpleGraph.neighborFinset ]
        simp_all +decide [ Matrix.mulVec, dotProduct ] ;
      -- Since the sum of the entries of the Laplacian matrix multiplied by x_tilde is zero, and x_tilde is zero at q, the sum over all vertices except q must also be zero.
      have h_sum_zero_except_q : ∑ v ∈ Finset.univ.erase q, (G.lapMatrix ℝ).mulVec x_tilde v = 0 := by
        convert congr_arg ( fun f : G.DelVert q → ℝ => ∑ i : G.DelVert q, f i ) hx_zero using 1;
        · refine' Finset.sum_bij ( fun v hv => ⟨ v, by aesop ⟩ ) _ _ _ _ <;> simp +decide [ SimpleGraph.lapMatrix, Matrix.mulVec, dotProduct ];
          intro a ha; rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun x : G.DelVert q => ( x : V ) ) Finset.univ ) ) ] ; simp +decide [ Finset.sum_image, ha ] ;
          · exact Finset.sum_congr rfl fun i hi => by aesop;
          · aesop;
        · norm_num +zetaDelta at *
      generalize_proofs at *; (
      simp_all +decide [ Finset.sum_erase, Matrix.mulVec, dotProduct ]);
    · convert congr_fun hx_zero ⟨ v, hv ⟩ using 1
      generalize_proofs at *; (
      simp +decide [ Matrix.mulVec, dotProduct, hv ] ; ring_nf!; (
      rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun i : G.DelVert q => ( i : V ) ) Finset.univ ) ) ] <;> simp +decide [ Finset.sum_image, hv ] ; ring_nf!; (
      exact Finset.sum_congr rfl fun i hi => ite_eq_right i.2;));)
  have hx_tilde_const : ∀ v : V, x_tilde v = x_tilde q := by
    have hx_tilde_const : ∀ v : V, G.Reachable q v → x_tilde q = x_tilde v := by
      intro v hv
      have := SimpleGraph.lapMatrix_mulVec_eq_zero_iff_forall_reachable (G := G) (x := x_tilde) |>.1 hx_tilde_zero q v hv
      aesop;
    exact fun v => Eq.symm ( hx_tilde_const v ( hconn q v ) )
  have hx_tilde_zero_all : ∀ v : V, x_tilde v = 0 := by
    aesop ( simp_config := { singlePass := true } ) ;
  have hx_zero_all : ∀ v : G.DelVert q, x v = 0 := by
    intro v; specialize hx_tilde_zero_all v; aesop;
  have hx_zero : x = 0 := by
    exact funext hx_zero_all
  exact hx_nonzero hx_zero

private def selectedEdgeGraph (s : Finset G.edgeSet) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet ((↑) '' (s : Set G.edgeSet))

private theorem selectedEdgeGraph_edgeSet (s : Finset G.edgeSet) :
    (selectedEdgeGraph (G := G) s).edgeSet = ((↑) '' (s : Set G.edgeSet)) := by
  ext e
  constructor
  · intro he
    have h :
        e ∈ ((↑) '' (s : Set G.edgeSet)) \ Sym2.diagSet := by
      simpa [selectedEdgeGraph, SimpleGraph.edgeSet_fromEdgeSet] using he
    exact h.1
  · intro he
    have hnd : e ∉ Sym2.diagSet := by
      rcases he with ⟨e', he', rfl⟩
      exact G.edgeSet_subset_compl_diagSet e'.property
    simpa [selectedEdgeGraph, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, hnd] using he

private theorem selectedEdgeGraph_le (s : Finset G.edgeSet) :
    selectedEdgeGraph (G := G) s ≤ G := by
  intro v w hvw
  have hs : s(v, w) ∈ (selectedEdgeGraph (G := G) s).edgeSet := by
    simpa [SimpleGraph.mem_edgeSet] using hvw
  rw [selectedEdgeGraph_edgeSet] at hs
  rcases hs with ⟨e, he, hEq⟩
  exact G.mem_edgeSet.mp (hEq ▸ e.property)

private theorem selectedEdgeGraph_edgeSet_card (s : Finset G.edgeSet) :
    Nat.card (selectedEdgeGraph (G := G) s).edgeSet = s.card := by
  rw [selectedEdgeGraph_edgeSet]
  let f : ↥s → ↥(((↑) '' (s : Set G.edgeSet) : Set (Sym2 V))) :=
    fun x => ⟨x.1.1, ⟨x.1, x.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val h
    · intro x
      rcases x with ⟨x, hx⟩
      rcases hx with ⟨e, he, hEq⟩
      refine ⟨⟨e, he⟩, ?_⟩
      apply Subtype.ext
      exact hEq
  let e : ↥s ≃ ↥(((↑) '' (s : Set G.edgeSet) : Set (Sym2 V))) :=
    Equiv.ofBijective f hf
  simpa [Nat.card_eq_fintype_card] using (Nat.card_congr e).symm

private theorem card_delVert_add_one (q : V) :
    Fintype.card (G.DelVert q) + 1 = Fintype.card V := by
  classical
  have hsingle : Fintype.card {v : V // v = q} = 1 := by
    simpa using Fintype.card_ofSubsingleton (⟨q, rfl⟩ : {v : V // v = q})
  have hcard : Fintype.card (G.DelVert q) = Fintype.card V - 1 := by
    simpa [SimpleGraph.DelVert, hsingle] using
      (Fintype.card_subtype_compl (fun v : V => v = q))
  have hpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨q⟩
  calc
    Fintype.card (G.DelVert q) + 1 = (Fintype.card V - 1) + 1 := by rw [hcard]
    _ = Fintype.card V := Nat.sub_add_cancel hpos

private theorem selectedEdgeGraph_isTree_iff_connected
    (q : V) (s : Finset G.edgeSet)
    (hs : s.card = Fintype.card (G.DelVert q)) :
    (selectedEdgeGraph (G := G) s).IsTree ↔ (selectedEdgeGraph (G := G) s).Connected := by
  have hcard :
      Nat.card (selectedEdgeGraph (G := G) s).edgeSet + 1 = Nat.card V := by
    rw [selectedEdgeGraph_edgeSet_card, hs, Nat.card_eq_fintype_card]
    simpa [Nat.card_eq_fintype_card] using card_delVert_add_one (G := G) q
  constructor
  · intro h
    exact h.1
  · intro hc
    exact (SimpleGraph.isTree_iff_connected_and_card (G := selectedEdgeGraph (G := G) s)).2
      ⟨hc, hcard⟩

private theorem selectedEdgeGraph_adj_toDart
    (o : G.EdgeOrientation) {s : Finset G.edgeSet} {e : G.edgeSet}
    (he : e ∈ s) :
    (selectedEdgeGraph (G := G) s).Adj (o.toDart e).fst (o.toDart e).snd := by
  have hs : e.1 ∈ (selectedEdgeGraph (G := G) s).edgeSet := by
    rw [selectedEdgeGraph_edgeSet]
    exact ⟨e, he, rfl⟩
  have hs' :
      (o.toDart e).edge ∈ (selectedEdgeGraph (G := G) s).edgeSet := by
    simpa [o.edge_toDart e] using hs
  have hs'' :
      s((o.toDart e).fst, (o.toDart e).snd) ∈
        (selectedEdgeGraph (G := G) s).edgeSet := by
    simpa [SimpleGraph.Dart.edge] using hs'
  exact (selectedEdgeGraph (G := G) s).mem_edgeSet.mp hs''

private abbrev EdgeSetType (q : V) : Type _ :=
  {s : Finset G.edgeSet // s.card = Fintype.card (G.DelVert q)}

private noncomputable def edgeSetRep (q : V) (s : EdgeSetType (G := G) q) :
    G.DelVert q ≃ s.1 :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_coe]
    exact s.2.symm)

private def edgeSetEmbeddingOfRep (q : V) (s : EdgeSetType (G := G) q) :
    G.DelVert q ↪ G.edgeSet :=
  (edgeSetRep (G := G) q s).toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩

private def selectedMinor
    (o : G.EdgeOrientation) (q : V) (s : EdgeSetType (G := G) q) :
    Matrix (G.DelVert q) (G.DelVert q) ℤ :=
  (o.deletedSignedIncMatrix q).submatrix id (edgeSetEmbeddingOfRep (G := G) q s)

@[simp]
private theorem selectedMinor_apply
    (o : G.EdgeOrientation) (q : V) (s : EdgeSetType (G := G) q)
    (i j : G.DelVert q) :
    selectedMinor (G := G) o q s i j =
      o.deletedSignedIncMatrix q i (edgeSetEmbeddingOfRep (G := G) q s j) := rfl

private theorem selectedMinor_hcol
    (o : G.EdgeOrientation) (q : V) (s : EdgeSetType (G := G) q) :
    ∀ j : G.DelVert q,
      (Finset.univ.filter (fun i => selectedMinor (G := G) o q s i j = 1)).card ≤ 1 ∧
      (Finset.univ.filter (fun i => selectedMinor (G := G) o q s i j = -1)).card ≤ 1 ∧
      (∀ i,
        selectedMinor (G := G) o q s i j = 0 ∨
          selectedMinor (G := G) o q s i j = 1 ∨
            selectedMinor (G := G) o q s i j = -1) := by
  intro j
  constructor
  · rw [Finset.card_le_one_iff]
    intro a b ha hb
    apply Subtype.ext
    have haEq : selectedMinor (G := G) o q s a j = 1 := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha
    have hbEq : selectedMinor (G := G) o q s b j = 1 := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hb
    have ha' : (a : V) = (o.toDart (edgeSetEmbeddingOfRep (G := G) q s j)).fst := by
      by_contra hfa
      by_cases hsa : (a : V) = (o.toDart (edgeSetEmbeddingOfRep (G := G) q s j)).snd
      · have : (-1 : ℤ) = 1 := by
          simpa [selectedMinor, SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
            SimpleGraph.EdgeOrientation.signedIncMatrix, hfa, hsa] using haEq
        norm_num at this
      · have : (0 : ℤ) = 1 := by
          simpa [selectedMinor, SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
            SimpleGraph.EdgeOrientation.signedIncMatrix, hfa, hsa] using haEq
        norm_num at this
    have hb' : (b : V) = (o.toDart (edgeSetEmbeddingOfRep (G := G) q s j)).fst := by
      by_contra hfb
      by_cases hsb : (b : V) = (o.toDart (edgeSetEmbeddingOfRep (G := G) q s j)).snd
      · have : (-1 : ℤ) = 1 := by
          simpa [selectedMinor, SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
            SimpleGraph.EdgeOrientation.signedIncMatrix, hfb, hsb] using hbEq
        norm_num at this
      · have : (0 : ℤ) = 1 := by
          simpa [selectedMinor, SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
            SimpleGraph.EdgeOrientation.signedIncMatrix, hfb, hsb] using hbEq
        norm_num at this
    simpa [ha', hb']
  constructor
  · rw [Finset.card_le_one_iff]
    intro a b ha hb
    apply Subtype.ext
    have haEq : selectedMinor (G := G) o q s a j = -1 := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha
    have hbEq : selectedMinor (G := G) o q s b j = -1 := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hb
    have ha' : (a : V) = (o.toDart (edgeSetEmbeddingOfRep (G := G) q s j)).snd := by
      by_cases hfa : (a : V) = (o.toDart (edgeSetEmbeddingOfRep (G := G) q s j)).fst
      · have : (1 : ℤ) = -1 := by
          simpa [selectedMinor, SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
            SimpleGraph.EdgeOrientation.signedIncMatrix, hfa] using haEq
        norm_num at this
      · by_contra hsa
        have : (0 : ℤ) = -1 := by
          simpa [selectedMinor, SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
            SimpleGraph.EdgeOrientation.signedIncMatrix, hfa, hsa] using haEq
        norm_num at this
    have hb' : (b : V) = (o.toDart (edgeSetEmbeddingOfRep (G := G) q s j)).snd := by
      by_cases hfb : (b : V) = (o.toDart (edgeSetEmbeddingOfRep (G := G) q s j)).fst
      · have : (1 : ℤ) = -1 := by
          simpa [selectedMinor, SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
            SimpleGraph.EdgeOrientation.signedIncMatrix, hfb] using hbEq
        norm_num at this
      · by_contra hsb
        have : (0 : ℤ) = -1 := by
          simpa [selectedMinor, SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
            SimpleGraph.EdgeOrientation.signedIncMatrix, hfb, hsb] using hbEq
        norm_num at this
    simpa [ha', hb']
  · intro i
    by_cases hfst : (i : V) = (o.toDart (edgeSetEmbeddingOfRep (G := G) q s j)).fst
    · right
      left
      simp [selectedMinor, SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
        SimpleGraph.EdgeOrientation.signedIncMatrix, hfst]
    · by_cases hsnd : (i : V) = (o.toDart (edgeSetEmbeddingOfRep (G := G) q s j)).snd
      · right
        right
        simp [selectedMinor, SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
          SimpleGraph.EdgeOrientation.signedIncMatrix, hfst, hsnd]
      · left
        simp [selectedMinor, SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
          SimpleGraph.EdgeOrientation.signedIncMatrix, hfst, hsnd]

private theorem selectedMinor_det_mem_zero_one_negOne
    (o : G.EdgeOrientation) (q : V) (s : EdgeSetType (G := G) q) :
    (selectedMinor (G := G) o q s).det = 0 ∨
      (selectedMinor (G := G) o q s).det = 1 ∨
        (selectedMinor (G := G) o q s).det = -1 := by
  let e : G.DelVert q ≃ Fin (Fintype.card (G.DelVert q)) := Fintype.equivFin (G.DelVert q)
  let A : Matrix (Fin (Fintype.card (G.DelVert q))) (Fin (Fintype.card (G.DelVert q))) ℤ :=
    Matrix.reindex e e (selectedMinor (G := G) o q s)
  have hA :
      A.det = (selectedMinor (G := G) o q s).det := by
    simpa [A, e] using Matrix.det_reindex_self e (selectedMinor (G := G) o q s)
  have hcol :
      ∀ j : Fin (Fintype.card (G.DelVert q)),
        (Finset.univ.filter (fun i => A i j = 1)).card ≤ 1 ∧
        (Finset.univ.filter (fun i => A i j = -1)).card ≤ 1 ∧
        (∀ i, A i j = 0 ∨ A i j = 1 ∨ A i j = -1) := by
    intro j
    constructor
    · rw [Finset.card_le_one_iff]
      intro a b ha hb
      have haEq : A a j = 1 := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha
      have hbEq : A b j = 1 := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hb
      have ha' :
          (e.symm a : V) = (o.toDart (edgeSetEmbeddingOfRep (G := G) q s (e.symm j))).fst := by
        by_contra hfa
        by_cases hsa : (e.symm a : V) = (o.toDart (edgeSetEmbeddingOfRep (G := G) q s (e.symm j))).snd
        · have : (-1 : ℤ) = 1 := by
            simpa [A, Matrix.reindex_apply, selectedMinor,
              SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
              SimpleGraph.EdgeOrientation.signedIncMatrix, hfa, hsa] using haEq
          norm_num at this
        · have : (0 : ℤ) = 1 := by
            simpa [A, Matrix.reindex_apply, selectedMinor,
              SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
              SimpleGraph.EdgeOrientation.signedIncMatrix, hfa, hsa] using haEq
          norm_num at this
      have hb' :
          (e.symm b : V) = (o.toDart (edgeSetEmbeddingOfRep (G := G) q s (e.symm j))).fst := by
        by_contra hfb
        by_cases hsb : (e.symm b : V) = (o.toDart (edgeSetEmbeddingOfRep (G := G) q s (e.symm j))).snd
        · have : (-1 : ℤ) = 1 := by
            simpa [A, Matrix.reindex_apply, selectedMinor,
              SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
              SimpleGraph.EdgeOrientation.signedIncMatrix, hfb, hsb] using hbEq
          norm_num at this
        · have : (0 : ℤ) = 1 := by
            simpa [A, Matrix.reindex_apply, selectedMinor,
              SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
              SimpleGraph.EdgeOrientation.signedIncMatrix, hfb, hsb] using hbEq
          norm_num at this
      exact e.symm.injective <| Subtype.ext <| ha'.trans hb'.symm
    constructor
    · rw [Finset.card_le_one_iff]
      intro a b ha hb
      have haEq : A a j = -1 := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha
      have hbEq : A b j = -1 := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hb
      have ha' :
          (e.symm a : V) = (o.toDart (edgeSetEmbeddingOfRep (G := G) q s (e.symm j))).snd := by
        by_cases hfa : (e.symm a : V) = (o.toDart (edgeSetEmbeddingOfRep (G := G) q s (e.symm j))).fst
        · have : (1 : ℤ) = -1 := by
            simpa [A, Matrix.reindex_apply, selectedMinor,
              SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
              SimpleGraph.EdgeOrientation.signedIncMatrix, hfa] using haEq
          norm_num at this
        · by_contra hsa
          have : (0 : ℤ) = -1 := by
            simpa [A, Matrix.reindex_apply, selectedMinor,
              SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
              SimpleGraph.EdgeOrientation.signedIncMatrix, hfa, hsa] using haEq
          norm_num at this
      have hb' :
          (e.symm b : V) = (o.toDart (edgeSetEmbeddingOfRep (G := G) q s (e.symm j))).snd := by
        by_cases hfb : (e.symm b : V) = (o.toDart (edgeSetEmbeddingOfRep (G := G) q s (e.symm j))).fst
        · have : (1 : ℤ) = -1 := by
            simpa [A, Matrix.reindex_apply, selectedMinor,
              SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
              SimpleGraph.EdgeOrientation.signedIncMatrix, hfb] using hbEq
          norm_num at this
        · by_contra hsb
          have : (0 : ℤ) = -1 := by
            simpa [A, Matrix.reindex_apply, selectedMinor,
              SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
              SimpleGraph.EdgeOrientation.signedIncMatrix, hfb, hsb] using hbEq
          norm_num at this
      exact e.symm.injective <| Subtype.ext <| ha'.trans hb'.symm
    · intro i
      have h := (selectedMinor_hcol (G := G) o q s (e.symm j)).2.2 (e.symm i)
      simpa [A, Matrix.reindex_apply] using h
  rcases det_of_atMostOnePosOneNeg (Fintype.card (G.DelVert q)) A hcol with h | h | h
  · left
    simpa [hA] using h
  · right
    left
    simpa [hA] using h
  · right
    right
    simpa [hA] using h

private def extendZero (q : V) (x : G.DelVert q → ℤ) : V → ℤ :=
  fun v => if h : v = q then 0 else x ⟨v, h⟩

private theorem deletedSignedIncMatrix_eq_zero_of_ne_fst_ne_snd
    (o : G.EdgeOrientation) (q : V) (i : G.DelVert q) (e : G.edgeSet)
    (hfst : (i : V) ≠ (o.toDart e).fst) (hsnd : (i : V) ≠ (o.toDart e).snd) :
    o.deletedSignedIncMatrix q i e = 0 := by
  simp [SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
    SimpleGraph.EdgeOrientation.signedIncMatrix, hfst, hsnd]

private theorem deletedSignedIncMatrix_eq_one_of_eq_fst
    (o : G.EdgeOrientation) (q : V) (i : G.DelVert q) (e : G.edgeSet)
    (hfst : (i : V) = (o.toDart e).fst) :
    o.deletedSignedIncMatrix q i e = 1 := by
  simp [SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
    SimpleGraph.EdgeOrientation.signedIncMatrix, hfst]

private theorem deletedSignedIncMatrix_eq_neg_one_of_eq_snd
    (o : G.EdgeOrientation) (q : V) (i : G.DelVert q) (e : G.edgeSet)
    (hsnd : (i : V) = (o.toDart e).snd) :
    o.deletedSignedIncMatrix q i e = -1 := by
  have hfst : (i : V) ≠ (o.toDart e).fst := by
    intro hi
    exact (o.toDart e).fst_ne_snd (hi.symm.trans hsnd)
  simp [SimpleGraph.EdgeOrientation.deletedSignedIncMatrix,
    SimpleGraph.EdgeOrientation.signedIncMatrix, hfst, hsnd]

private theorem selectedMinor_transpose_mulVec_apply
    (o : G.EdgeOrientation) (q : V) (s : EdgeSetType (G := G) q)
    (x : G.DelVert q → ℤ) (j : G.DelVert q) :
    ((selectedMinor (G := G) o q s).transpose.mulVec x) j =
      extendZero (G := G) q x (o.toDart (edgeSetEmbeddingOfRep (G := G) q s j)).fst -
        extendZero (G := G) q x (o.toDart (edgeSetEmbeddingOfRep (G := G) q s j)).snd := by
  classical
  let d := o.toDart (edgeSetEmbeddingOfRep (G := G) q s j)
  rw [Matrix.mulVec, dotProduct]
  simp_rw [Matrix.transpose_apply]
  by_cases hfst : d.fst = q
  · have hsnd : d.snd ≠ q := by
      intro hsnd
      exact d.fst_ne_snd (hfst.trans hsnd.symm)
    let isnd : G.DelVert q := ⟨d.snd, hsnd⟩
    have hsum :
        ∑ i : G.DelVert q, selectedMinor (G := G) o q s i j * x i =
          selectedMinor (G := G) o q s isnd j * x isnd := by
      rw [Finset.sum_eq_single isnd]
      · intro i hi hisnd
        have hnefst : (i : V) ≠ d.fst := by
          intro hi'
          exact i.2 (hi'.trans hfst)
        have hnesnd : (i : V) ≠ d.snd := by
          intro hi'
          exact hisnd (Subtype.ext hi')
        have hzero : selectedMinor (G := G) o q s i j = 0 := by
          rw [selectedMinor_apply]
          exact deletedSignedIncMatrix_eq_zero_of_ne_fst_ne_snd
            (G := G) o q i (edgeSetEmbeddingOfRep (G := G) q s j) hnefst hnesnd
        rw [hzero]
        simp
      · simp
    rw [hsum]
    have hentry : selectedMinor (G := G) o q s isnd j = -1 := by
      rw [selectedMinor_apply]
      exact deletedSignedIncMatrix_eq_neg_one_of_eq_snd
        (G := G) o q isnd (edgeSetEmbeddingOfRep (G := G) q s j) rfl
    rw [hentry]
    simp [extendZero, isnd, d, hfst, hsnd]
  · by_cases hsnd : d.snd = q
    · have hfst' : d.fst ≠ q := hfst
      let ifst : G.DelVert q := ⟨d.fst, hfst'⟩
      have hsum :
          ∑ i : G.DelVert q, selectedMinor (G := G) o q s i j * x i =
            selectedMinor (G := G) o q s ifst j * x ifst := by
        rw [Finset.sum_eq_single ifst]
        · intro i hi hifst
          have hnefst : (i : V) ≠ d.fst := by
            intro hi'
            exact hifst (Subtype.ext hi')
          have hnesnd : (i : V) ≠ d.snd := by
            intro hi'
            exact i.2 (hi'.trans hsnd)
          have hzero : selectedMinor (G := G) o q s i j = 0 := by
            rw [selectedMinor_apply]
            exact deletedSignedIncMatrix_eq_zero_of_ne_fst_ne_snd
              (G := G) o q i (edgeSetEmbeddingOfRep (G := G) q s j) hnefst hnesnd
          rw [hzero]
          simp
        · simp
      rw [hsum]
      have hentry : selectedMinor (G := G) o q s ifst j = 1 := by
        rw [selectedMinor_apply]
        exact deletedSignedIncMatrix_eq_one_of_eq_fst
          (G := G) o q ifst (edgeSetEmbeddingOfRep (G := G) q s j) rfl
      rw [hentry]
      simp [extendZero, ifst, d, hfst, hsnd]
    · let ifst : G.DelVert q := ⟨d.fst, hfst⟩
      let isnd : G.DelVert q := ⟨d.snd, hsnd⟩
      have hneq : ifst ≠ isnd := by
        intro h
        exact d.fst_ne_snd (congrArg Subtype.val h)
      let f : G.DelVert q → ℤ := fun i =>
        selectedMinor (G := G) o q s i j * x i
      have hsum' :
          Finset.sum (Finset.univ : Finset (G.DelVert q)) f = f ifst + f isnd := by
        have h_ifst_mem : ifst ∈ (Finset.univ : Finset (G.DelVert q)) := Finset.mem_univ ifst
        rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (s := (Finset.univ : Finset (G.DelVert q)))
          h_ifst_mem]
        have h_isnd_mem : isnd ∈ (Finset.univ : Finset (G.DelVert q)) \ {ifst} := by
          refine Finset.mem_sdiff.mpr ?_
          constructor
          · exact Finset.mem_univ isnd
          · intro h
            have his : isnd = ifst := by simpa [Finset.mem_singleton] using h
            exact hneq his.symm
        rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem
          (s := (Finset.univ : Finset (G.DelVert q)) \ {ifst}) h_isnd_mem]
        · suffices hrest :
              Finset.sum (((Finset.univ : Finset (G.DelVert q)) \ {ifst}) \ {isnd}) f = 0 by
            rw [hrest]
            simp [f, add_assoc, add_left_comm, add_comm]
          apply Finset.sum_eq_zero
          intro i hi
          have hi_left : i ∈ (Finset.univ : Finset (G.DelVert q)) \ {ifst} :=
            (Finset.mem_sdiff.mp hi).1
          have hi_ne_ifst : i ≠ ifst := by
            simpa [Finset.mem_singleton] using (Finset.mem_sdiff.mp hi_left).2
          have hi_ne_isnd : i ≠ isnd := by
            simpa [Finset.mem_singleton] using (Finset.mem_sdiff.mp hi).2
          have hnefst : (i : V) ≠ d.fst := by
            intro hi'
            exact hi_ne_ifst (Subtype.ext hi')
          have hnesnd : (i : V) ≠ d.snd := by
            intro hi'
            exact hi_ne_isnd (Subtype.ext hi')
          have hzero : selectedMinor (G := G) o q s i j = 0 := by
            rw [selectedMinor_apply]
            exact deletedSignedIncMatrix_eq_zero_of_ne_fst_ne_snd
              (G := G) o q i (edgeSetEmbeddingOfRep (G := G) q s j) hnefst hnesnd
          rw [hzero]
          simp
      have hsum :
          ∑ i : G.DelVert q, selectedMinor (G := G) o q s i j * x i =
            selectedMinor (G := G) o q s ifst j * x ifst +
              selectedMinor (G := G) o q s isnd j * x isnd := by
        unfold f at hsum'
        simpa using hsum'
      rw [hsum]
      have hfstEntry : selectedMinor (G := G) o q s ifst j = 1 := by
        rw [selectedMinor_apply]
        exact deletedSignedIncMatrix_eq_one_of_eq_fst
          (G := G) o q ifst (edgeSetEmbeddingOfRep (G := G) q s j) rfl
      have hsndEntry : selectedMinor (G := G) o q s isnd j = -1 := by
        rw [selectedMinor_apply]
        exact deletedSignedIncMatrix_eq_neg_one_of_eq_snd
          (G := G) o q isnd (edgeSetEmbeddingOfRep (G := G) q s j) rfl
      rw [hfstEntry, hsndEntry]
      simp [extendZero, ifst, isnd, d, hfst, hsnd, sub_eq_add_neg]

/-- Kirchhoff's matrix-tree theorem over `ℤ`. -/
private theorem edgeSetEmbeddingOfRep_mem
    (q : V) (s : EdgeSetType (G := G) q) (j : G.DelVert q) :
    edgeSetEmbeddingOfRep (G := G) q s j ∈ s.1 := by
  change (((edgeSetRep (G := G) q s) j : s.1) : G.edgeSet) ∈ s.1
  exact ((edgeSetRep (G := G) q s j) : s.1).property

private theorem extendZero_eq_of_selectedEdgeGraph_adj_of_mulVec_zero
    (o : G.EdgeOrientation) (q : V) (s : EdgeSetType (G := G) q)
    (x : G.DelVert q → ℤ)
    (hx_zero : (selectedMinor (G := G) o q s).transpose.mulVec x = 0)
    {u v : V} (hAdj : (selectedEdgeGraph (G := G) s.1).Adj u v) :
    extendZero (G := G) q x u = extendZero (G := G) q x v := by
  have hs : s(u, v) ∈ (selectedEdgeGraph (G := G) s.1).edgeSet := by
    simpa [SimpleGraph.mem_edgeSet] using hAdj
  rw [selectedEdgeGraph_edgeSet] at hs
  rcases hs with ⟨e, he, hEq⟩
  let j : G.DelVert q := (edgeSetRep (G := G) q s).symm ⟨e, he⟩
  have hj : edgeSetEmbeddingOfRep (G := G) q s j = e := by
    simp [j, edgeSetEmbeddingOfRep, edgeSetRep]
  have hz : ((selectedMinor (G := G) o q s).transpose.mulVec x) j = 0 := by
    simpa using congrFun hx_zero j
  rw [selectedMinor_transpose_mulVec_apply (G := G) o q s x j, hj] at hz
  have hstep :
      extendZero (G := G) q x (o.toDart e).fst =
        extendZero (G := G) q x (o.toDart e).snd := by
    linarith
  have hdart : s((o.toDart e).fst, (o.toDart e).snd) = s(u, v) := by
    simpa [SimpleGraph.Dart.edge] using (o.edge_toDart e).trans hEq
  rw [Sym2.eq_iff] at hdart
  rcases hdart with hpair | hpair
  · simpa [hpair.1, hpair.2] using hstep
  · simpa [hpair.1, hpair.2] using hstep.symm

private theorem selectedMinor_det_eq_zero_of_not_connected
    (o : G.EdgeOrientation) (q : V) (s : EdgeSetType (G := G) q)
    (hdisc : ¬ (selectedEdgeGraph (G := G) s.1).Connected) :
    (selectedMinor (G := G) o q s).det = 0 := by
  classical
  have hq : ∃ v : V, ¬ (selectedEdgeGraph (G := G) s.1).Reachable q v := by
    by_contra hq
    push Not at hq
    apply hdisc
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    exact ⟨q, hq⟩
  rcases hq with ⟨v, hv⟩
  have hvq : v ≠ q := by
    intro h
    have hqq : (selectedEdgeGraph (G := G) s.1).Reachable q q := Reachable.refl q
    exact hv (h ▸ hqq)
  let x : G.DelVert q → ℤ := fun i =>
    if (selectedEdgeGraph (G := G) s.1).Reachable q (i : V) then 0 else 1
  let iv : G.DelVert q := ⟨v, hvq⟩
  have hx_nonzero : x ≠ 0 := by
    intro hx
    have hiv : x iv = 1 := by
      simp [x, iv, hv]
    have hzero : x iv = 0 := by
      simpa [hx] using congrFun hx iv
    linarith
  have hx_zero : (selectedMinor (G := G) o q s).transpose.mulVec x = 0 := by
    funext j
    let d := o.toDart (edgeSetEmbeddingOfRep (G := G) q s j)
    have he : edgeSetEmbeddingOfRep (G := G) q s j ∈ s.1 :=
      edgeSetEmbeddingOfRep_mem (G := G) q s j
    have hadj : (selectedEdgeGraph (G := G) s.1).Adj d.fst d.snd := by
      simpa [d] using selectedEdgeGraph_adj_toDart (G := G) o he
    have hvals :
        extendZero (G := G) q x d.fst = extendZero (G := G) q x d.snd := by
      by_cases hfst : d.fst = q
      · have hreach : (selectedEdgeGraph (G := G) s.1).Reachable q d.snd := by
          simpa [hfst] using (Adj.reachable hadj :
            (selectedEdgeGraph (G := G) s.1).Reachable d.fst d.snd)
        have hsnd_ne : d.snd ≠ q := by
          intro hsnd
          exact d.fst_ne_snd (hfst.trans hsnd.symm)
        simp [extendZero, x, d, hfst, hsnd_ne, hreach]
      · by_cases hsnd : d.snd = q
        · have hreach : (selectedEdgeGraph (G := G) s.1).Reachable q d.fst := by
            simpa [hsnd] using (Adj.reachable hadj.symm :
              (selectedEdgeGraph (G := G) s.1).Reachable d.snd d.fst)
          simp [extendZero, x, d, hfst, hsnd, hreach]
        · have hiff :
              (selectedEdgeGraph (G := G) s.1).Reachable q d.fst ↔
                (selectedEdgeGraph (G := G) s.1).Reachable q d.snd := by
            constructor
            · intro hreach
              exact Reachable.trans hreach (Adj.reachable hadj)
            · intro hreach
              exact Reachable.trans hreach (Adj.reachable hadj.symm)
          by_cases hreach : (selectedEdgeGraph (G := G) s.1).Reachable q d.fst
          · have hreach' : (selectedEdgeGraph (G := G) s.1).Reachable q d.snd := hiff.mp hreach
            simp [extendZero, x, d, hfst, hsnd, hreach, hreach']
          · have hreach' : ¬ (selectedEdgeGraph (G := G) s.1).Reachable q d.snd := by
              intro hs
              exact hreach (hiff.mpr hs)
            simp [extendZero, x, d, hfst, hsnd, hreach, hreach']
    rw [selectedMinor_transpose_mulVec_apply (G := G) o q s x j]
    exact sub_eq_zero.mpr hvals
  have hdetT : (selectedMinor (G := G) o q s).transpose.det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨x, hx_nonzero, hx_zero⟩
  simpa [Matrix.det_transpose] using hdetT

private theorem selectedMinor_det_ne_zero_of_connected
    (o : G.EdgeOrientation) (q : V) (s : EdgeSetType (G := G) q)
    (hconn : (selectedEdgeGraph (G := G) s.1).Connected) :
    (selectedMinor (G := G) o q s).det ≠ 0 := by
  classical
  intro hdet
  have hdetT : (selectedMinor (G := G) o q s).transpose.det = 0 := by
    simpa [Matrix.det_transpose] using hdet
  obtain ⟨x, hx_nonzero, hx_zero⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
  let xt : V → ℤ := extendZero (G := G) q x
  have hconstAdj :
      ∀ {u v : V}, (selectedEdgeGraph (G := G) s.1).Adj u v → xt u = xt v := by
    intro u v hadj
    simpa [xt] using
      extendZero_eq_of_selectedEdgeGraph_adj_of_mulVec_zero
        (G := G) o q s x hx_zero hadj
  have hconstWalk :
      ∀ {u v : V}, (selectedEdgeGraph (G := G) s.1).Walk u v → xt u = xt v := by
    intro u v p
    induction p with
    | nil =>
        rfl
    | cons ha p ih =>
        exact (hconstAdj ha).trans ih
  have hzero_all : ∀ v : V, xt v = 0 := by
    intro v
    obtain ⟨p⟩ := hconn q v
    have hp : xt q = xt v := hconstWalk p
    have hp0 : xt v = 0 := by
      calc
        xt v = xt q := hp.symm
        _ = 0 := by simp [xt, extendZero]
    exact hp0
  have hx_zero_all : ∀ i : G.DelVert q, x i = 0 := by
    intro i
    simpa [xt, extendZero, i.2] using hzero_all (i : V)
  have hx_eq_zero : x = 0 := funext hx_zero_all
  exact hx_nonzero hx_eq_zero

private theorem selectedMinor_det_ne_zero_iff_connected
    (o : G.EdgeOrientation) (q : V) (s : EdgeSetType (G := G) q) :
    (selectedMinor (G := G) o q s).det ≠ 0 ↔
      (selectedEdgeGraph (G := G) s.1).Connected := by
  constructor
  · intro h
    by_contra hdisc
    exact h <| selectedMinor_det_eq_zero_of_not_connected (G := G) o q s hdisc
  · exact selectedMinor_det_ne_zero_of_connected (G := G) o q s

private noncomputable def edgeImageType
    (q : V) (f : G.DelVert q ↪ G.edgeSet) :
    EdgeSetType (G := G) q :=
  ⟨Finset.univ.image f, by
    simpa using
      Finset.card_image_of_injective (s := (Finset.univ : Finset (G.DelVert q))) f.injective⟩

private abbrev EmbeddingFiber (q : V) (s : EdgeSetType (G := G) q) :=
  {f : G.DelVert q ↪ G.edgeSet // Finset.univ.image f = s.1}

private noncomputable def embeddingSigmaFiberEquiv (q : V) :
    (G.DelVert q ↪ G.edgeSet) ≃ Σ s : EdgeSetType (G := G) q, EmbeddingFiber (G := G) q s where
  toFun f := ⟨edgeImageType (G := G) q f, ⟨f, rfl⟩⟩
  invFun x := x.2.1
  left_inv f := rfl
  right_inv x := by
    rcases x with ⟨s, ⟨f, hf⟩⟩
    have hs : edgeImageType (G := G) q f = s := by
      apply Subtype.ext
      exact hf
    cases hs
    rfl

private noncomputable def embeddingFiberEquivToSet
    (q : V) (s : EdgeSetType (G := G) q) (f : EmbeddingFiber (G := G) q s) :
    G.DelVert q ≃ s.1 :=
  Equiv.ofBijective
    (fun i => ⟨f.1 i, by
      have hi : f.1 i ∈ (Finset.univ.image fun j : G.DelVert q => f.1 j) := by
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      simpa [f.2] using hi⟩)
    (by
      constructor
      · intro i j h
        exact f.1.injective <| congrArg Subtype.val h
      · intro e
        have he : (e : G.edgeSet) ∈ (Finset.univ.image fun i : G.DelVert q => f.1 i) := by
          simpa [f.2] using e.2
        rcases Finset.mem_image.mp he with ⟨i, -, hi⟩
        refine ⟨i, ?_⟩
        exact Subtype.ext hi)

private noncomputable def embeddingFiberPerm
    (q : V) (s : EdgeSetType (G := G) q) (f : EmbeddingFiber (G := G) q s) :
    Equiv.Perm (G.DelVert q) :=
  (embeddingFiberEquivToSet (G := G) q s f).trans (edgeSetRep (G := G) q s).symm

private theorem edgeSetEmbeddingOfRep_embeddingFiberPerm
    (q : V) (s : EdgeSetType (G := G) q) (f : EmbeddingFiber (G := G) q s)
    (i : G.DelVert q) :
    edgeSetEmbeddingOfRep (G := G) q s (embeddingFiberPerm (G := G) q s f i) = f.1 i := by
  change (((edgeSetRep (G := G) q s) (embeddingFiberPerm (G := G) q s f i) : s.1) : G.edgeSet) = f.1 i
  simp [embeddingFiberPerm, embeddingFiberEquivToSet]

private noncomputable def fiberEmbeddingOfPerm
    (q : V) (s : EdgeSetType (G := G) q) (σ : Equiv.Perm (G.DelVert q)) :
    EmbeddingFiber (G := G) q s := by
  refine ⟨σ.toEmbedding.trans (edgeSetEmbeddingOfRep (G := G) q s), ?_⟩
  ext e
  constructor
  · intro he
    rcases Finset.mem_image.mp he with ⟨i, -, rfl⟩
    exact edgeSetEmbeddingOfRep_mem (G := G) q s (σ i)
  · intro he
    refine Finset.mem_image.mpr ?_
    refine ⟨σ.symm ((edgeSetRep (G := G) q s).symm ⟨e, he⟩), Finset.mem_univ _, ?_⟩
    simp [edgeSetEmbeddingOfRep, edgeSetRep]

private theorem fiberEmbeddingOfPerm_injective
    (q : V) (s : EdgeSetType (G := G) q) :
    Function.Injective (fiberEmbeddingOfPerm (G := G) q s) := by
  intro σ τ h
  ext i
  have hfun :
      ((fiberEmbeddingOfPerm (G := G) q s σ).1 : G.DelVert q → G.edgeSet) =
        ((fiberEmbeddingOfPerm (G := G) q s τ).1 : G.DelVert q → G.edgeSet) := by
    exact congrArg
      (fun x : G.DelVert q ↪ G.edgeSet => (x : G.DelVert q → G.edgeSet))
      (congrArg (fun x : EmbeddingFiber (G := G) q s => x.1) h)
  have hi :
      (fiberEmbeddingOfPerm (G := G) q s σ).1 i =
        (fiberEmbeddingOfPerm (G := G) q s τ).1 i := by
    exact congrFun hfun i
  exact congrArg Subtype.val <| (edgeSetEmbeddingOfRep (G := G) q s).injective hi

private noncomputable def permEquivEmbeddingFiber
    (q : V) (s : EdgeSetType (G := G) q) :
    Equiv.Perm (G.DelVert q) ≃ EmbeddingFiber (G := G) q s :=
  Equiv.ofBijective
    (fiberEmbeddingOfPerm (G := G) q s)
    (by
      constructor
      · exact fiberEmbeddingOfPerm_injective (G := G) q s
      · intro f
        refine ⟨embeddingFiberPerm (G := G) q s f, ?_⟩
        apply Subtype.ext
        apply DFunLike.ext
        intro i
        exact edgeSetEmbeddingOfRep_embeddingFiberPerm (G := G) q s f i)

private def cauchyBinetTerm
    (o : G.EdgeOrientation) (q : V) (f : G.DelVert q ↪ G.edgeSet) : ℤ :=
  (∏ i, o.deletedSignedIncMatrix q i (f i)) *
    (((o.deletedSignedIncMatrix q).transpose).submatrix (⇑f) id).det

private theorem cauchyBinetTerm_of_perm
    (o : G.EdgeOrientation) (q : V) (s : EdgeSetType (G := G) q)
    (σ : Equiv.Perm (G.DelVert q)) :
    cauchyBinetTerm (G := G) o q (fiberEmbeddingOfPerm (G := G) q s σ).1 =
      (((Equiv.Perm.sign σ : ℤ) * ∏ i, selectedMinor (G := G) o q s i (σ i)) *
        (selectedMinor (G := G) o q s).det) := by
  let M := selectedMinor (G := G) o q s
  have hprod :
      ∏ i, o.deletedSignedIncMatrix q i ((fiberEmbeddingOfPerm (G := G) q s σ).1 i) =
        ∏ i, M i (σ i) := by
    simp [fiberEmbeddingOfPerm, M, selectedMinor, edgeSetEmbeddingOfRep]
  have hdet :
      (((o.deletedSignedIncMatrix q).transpose).submatrix
          (⇑(fiberEmbeddingOfPerm (G := G) q s σ).1) id).det =
        (Equiv.Perm.sign σ : ℤ) * M.det := by
    calc
      (((o.deletedSignedIncMatrix q).transpose).submatrix
          (⇑(fiberEmbeddingOfPerm (G := G) q s σ).1) id).det
          = ((M.submatrix id σ).transpose).det := by
              apply congrArg Matrix.det
              ext i j
              simp [fiberEmbeddingOfPerm, M, selectedMinor, edgeSetEmbeddingOfRep]
      _ = (M.submatrix id σ).det := by rw [Matrix.det_transpose]
      _ = (Equiv.Perm.sign σ : ℤ) * M.det := Matrix.det_permute' σ M
  rw [cauchyBinetTerm, hprod, hdet]
  simp [M, mul_assoc, mul_left_comm, mul_comm]

private theorem sum_cauchyBinetTerm_over_fiber_eq_det_sq
    (o : G.EdgeOrientation) (q : V) (s : EdgeSetType (G := G) q) :
    ∑ f : EmbeddingFiber (G := G) q s, cauchyBinetTerm (G := G) o q f.1 =
      (selectedMinor (G := G) o q s).det ^ 2 := by
  let M := selectedMinor (G := G) o q s
  have hdetcol :
      ∑ σ : Equiv.Perm (G.DelVert q), (Equiv.Perm.sign σ : ℤ) * ∏ i, M i (σ i) = M.det := by
    symm
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  calc
    ∑ f : EmbeddingFiber (G := G) q s, cauchyBinetTerm (G := G) o q f.1
      = ∑ σ : Equiv.Perm (G.DelVert q),
          cauchyBinetTerm (G := G) o q (fiberEmbeddingOfPerm (G := G) q s σ).1 := by
            exact Fintype.sum_equiv (permEquivEmbeddingFiber (G := G) q s).symm
              (fun f => cauchyBinetTerm (G := G) o q f.1)
              (fun σ => cauchyBinetTerm (G := G) o q
                (fiberEmbeddingOfPerm (G := G) q s σ).1)
              (fun f => by
                have hf :
                    (fiberEmbeddingOfPerm (G := G) q s
                      ((permEquivEmbeddingFiber (G := G) q s).symm f)).1 = f.1 := by
                  exact congrArg (fun x : EmbeddingFiber (G := G) q s => x.1)
                    ((permEquivEmbeddingFiber (G := G) q s).apply_symm_apply f)
                simpa using
                  congrArg (fun g : G.DelVert q ↪ G.edgeSet =>
                    cauchyBinetTerm (G := G) o q g) hf.symm)
    _ = ∑ σ : Equiv.Perm (G.DelVert q),
          (((Equiv.Perm.sign σ : ℤ) * ∏ i, M i (σ i)) * M.det) := by
            simp_rw [cauchyBinetTerm_of_perm (G := G) o q s]
            rfl
    _ = (∑ σ : Equiv.Perm (G.DelVert q),
          (Equiv.Perm.sign σ : ℤ) * ∏ i, M i (σ i)) * M.det := by
            rw [Finset.sum_mul]
    _ = M.det * M.det := by rw [hdetcol]
    _ = (selectedMinor (G := G) o q s).det ^ 2 := by
          simp [M, pow_two]

private theorem selectedMinor_det_sq_eq_if_isTree
    (o : G.EdgeOrientation) (q : V) (s : EdgeSetType (G := G) q) :
    (selectedMinor (G := G) o q s).det ^ 2 =
      (by
        classical
        exact if (selectedEdgeGraph (G := G) s.1).IsTree then 1 else 0) := by
  classical
  by_cases hconn : (selectedEdgeGraph (G := G) s.1).Connected
  · have htree : (selectedEdgeGraph (G := G) s.1).IsTree := by
      exact (selectedEdgeGraph_isTree_iff_connected (G := G) q s.1 s.2).2 hconn
    have hdet_ne :
        (selectedMinor (G := G) o q s).det ≠ 0 :=
      (selectedMinor_det_ne_zero_iff_connected (G := G) o q s).2 hconn
    rcases selectedMinor_det_mem_zero_one_negOne (G := G) o q s with h0 | h1 | hneg
    · exact False.elim (hdet_ne h0)
    · norm_num [h1, htree]
    · norm_num [hneg, htree]
  · have hdet0 :
      (selectedMinor (G := G) o q s).det = 0 :=
        selectedMinor_det_eq_zero_of_not_connected (G := G) o q s hconn
    have hnotree : ¬ (selectedEdgeGraph (G := G) s.1).IsTree := by
      intro ht
      exact hconn ht.1
    norm_num [hnotree, hdet0]

private theorem selectedEdgeGraph_injective :
    Function.Injective (selectedEdgeGraph (G := G)) := by
  intro s t h
  apply Finset.ext
  intro e
  constructor
  · intro he
    have hs : (e : Sym2 V) ∈ (selectedEdgeGraph (G := G) s).edgeSet := by
      rw [selectedEdgeGraph_edgeSet]
      exact ⟨e, he, rfl⟩
    have ht : (e : Sym2 V) ∈ (selectedEdgeGraph (G := G) t).edgeSet := by
      simpa [h] using hs
    rw [selectedEdgeGraph_edgeSet] at ht
    rcases ht with ⟨e', he', hEq⟩
    exact (Subtype.ext hEq.symm) ▸ he'
  · intro he
    have ht : (e : Sym2 V) ∈ (selectedEdgeGraph (G := G) t).edgeSet := by
      rw [selectedEdgeGraph_edgeSet]
      exact ⟨e, he, rfl⟩
    have hs : (e : Sym2 V) ∈ (selectedEdgeGraph (G := G) s).edgeSet := by
      simpa [h] using ht
    rw [selectedEdgeGraph_edgeSet] at hs
    rcases hs with ⟨e', he', hEq⟩
    exact (Subtype.ext hEq.symm) ▸ he'

private def spanningTreeEdgeEmbedding (T : G.SpanningTree) :
    T.1.edgeSet ↪ G.edgeSet where
  toFun e := ⟨e.1, ((SimpleGraph.edgeSet_subset_edgeSet).2 T.2.1) e.2⟩
  inj' := by
    intro e₁ e₂ h
    apply Subtype.ext
    simpa using congrArg (fun x : G.edgeSet => (x : Sym2 V)) h

private noncomputable def spanningTreeEdgeSetType
    (q : V) (T : G.SpanningTree) :
    EdgeSetType (G := G) q := by
  letI := Fintype.ofFinite T.1.edgeSet
  refine ⟨(Finset.univ : Finset T.1.edgeSet).map (spanningTreeEdgeEmbedding (G := G) T), ?_⟩
  have htreeCard : Fintype.card T.1.edgeSet + 1 = Fintype.card V := by
    simpa [Nat.card_eq_fintype_card] using
      ((SimpleGraph.isTree_iff_connected_and_card (G := T.1)).1 T.2.2).2
  have hdel := card_delVert_add_one (G := G) q
  have hcardEq : Fintype.card T.1.edgeSet = Fintype.card (G.DelVert q) := by
    omega
  simpa [Finset.card_map] using hcardEq

private theorem spanningTreeEdgeSetType_mem_iff
    (q : V) (T : G.SpanningTree) {e : G.edgeSet} :
    e ∈ (spanningTreeEdgeSetType (G := G) q T).1 ↔ (e : Sym2 V) ∈ T.1.edgeSet := by
  let := Fintype.ofFinite T.1.edgeSet
  constructor
  · intro he
    change e ∈ (Finset.univ : Finset T.1.edgeSet).map (spanningTreeEdgeEmbedding (G := G) T) at he
    rcases Finset.mem_map.mp he with ⟨eT, -, hEq⟩
    exact hEq ▸ eT.2
  · intro he
    change e ∈ (Finset.univ : Finset T.1.edgeSet).map (spanningTreeEdgeEmbedding (G := G) T)
    exact Finset.mem_map.mpr ⟨⟨e, he⟩, Finset.mem_univ _, by ext; rfl⟩

private theorem selectedEdgeGraph_spanningTreeEdgeSetType_eq
    (q : V) (T : G.SpanningTree) :
    selectedEdgeGraph (G := G) (spanningTreeEdgeSetType (G := G) q T).1 = T.1 := by
  apply SimpleGraph.edgeSet_injective
  ext e
  constructor
  · intro he
    rw [selectedEdgeGraph_edgeSet] at he
    rcases he with ⟨eG, heG, hEq⟩
    exact hEq ▸ (spanningTreeEdgeSetType_mem_iff (G := G) q T).1 heG
  · intro he
    rw [selectedEdgeGraph_edgeSet]
    refine ⟨⟨e, ((SimpleGraph.edgeSet_subset_edgeSet).2 T.2.1) he⟩, ?_, rfl⟩
    exact (spanningTreeEdgeSetType_mem_iff (G := G) q T).2 he

private noncomputable def treeEdgeSetTypeEquivSpanningTree
    (q : V) :
    {s : EdgeSetType (G := G) q // (selectedEdgeGraph (G := G) s.1).IsTree} ≃ G.SpanningTree :=
  Equiv.ofBijective
    (fun s => ⟨selectedEdgeGraph (G := G) s.1.1, selectedEdgeGraph_le (G := G) s.1.1, s.2⟩)
    (by
      constructor
      · intro s t h
        have hgraphs :
            selectedEdgeGraph (G := G) s.1.1 = selectedEdgeGraph (G := G) t.1.1 := by
          exact congrArg (fun T : G.SpanningTree => T.1) h
        have hsEq : s.1.1 = t.1.1 := selectedEdgeGraph_injective (G := G) hgraphs
        exact Subtype.ext (Subtype.ext hsEq)
      · intro T
        refine ⟨⟨spanningTreeEdgeSetType (G := G) q T, ?_⟩, ?_⟩
        · simpa [selectedEdgeGraph_spanningTreeEdgeSetType_eq (G := G) q T] using T.2.2
        · apply Subtype.ext
          exact selectedEdgeGraph_spanningTreeEdgeSetType_eq (G := G) q T)

theorem kirchhoff_matrix_tree_int (q : V) :
    (G.reducedLaplacian ℤ q).det = (G.spanningTreeCount : ℤ) := by
  classical
  let o : G.EdgeOrientation := Classical.choice (EdgeOrientation.exists (G := G))
  let Nq : Matrix (G.DelVert q) G.edgeSet ℤ := o.deletedSignedIncMatrix q
  have hcb :
      (G.reducedLaplacian ℤ q).det =
        ∑ f : G.DelVert q ↪ G.edgeSet, cauchyBinetTerm (G := G) o q f := by
    rw [← o.deletedSignedIncMatrix_mul_transpose_eq_reducedLaplacian q]
    simpa [Nq, cauchyBinetTerm] using
      (cauchyBinetEmbedding Nq Nq.transpose)
  calc
    (G.reducedLaplacian ℤ q).det
      = ∑ f : G.DelVert q ↪ G.edgeSet, cauchyBinetTerm (G := G) o q f := hcb
    _ = ∑ x : Σ s : EdgeSetType (G := G) q, EmbeddingFiber (G := G) q s,
          cauchyBinetTerm (G := G) o q x.2.1 := by
            exact Fintype.sum_equiv (embeddingSigmaFiberEquiv (G := G) q)
              (fun f => cauchyBinetTerm (G := G) o q f)
              (fun x => cauchyBinetTerm (G := G) o q x.2.1)
              (fun _ => rfl)
    _ = ∑ s : EdgeSetType (G := G) q,
          ∑ f : EmbeddingFiber (G := G) q s, cauchyBinetTerm (G := G) o q f.1 := by
            simpa using
              (Fintype.sum_sigma' (fun s =>
                fun f : EmbeddingFiber (G := G) q s =>
                  cauchyBinetTerm (G := G) o q f.1))
    _ = ∑ s : EdgeSetType (G := G) q, (selectedMinor (G := G) o q s).det ^ 2 := by
            simp_rw [sum_cauchyBinetTerm_over_fiber_eq_det_sq (G := G) o q]
    _ = ∑ s : EdgeSetType (G := G) q,
          (by
            classical
            exact if (selectedEdgeGraph (G := G) s.1).IsTree then 1 else 0) := by
              simp_rw [selectedMinor_det_sq_eq_if_isTree (G := G) o q]
    _ = (Nat.card {s : EdgeSetType (G := G) q //
          (selectedEdgeGraph (G := G) s.1).IsTree} : ℤ) := by
            classical
            let p : EdgeSetType (G := G) q → Prop := fun s =>
              (selectedEdgeGraph (G := G) s.1).IsTree
            calc
              (∑ s : EdgeSetType (G := G) q, if p s then (1 : ℤ) else 0)
                  = ∑ s ∈ (Finset.univ : Finset (EdgeSetType (G := G) q)),
                      if p s then (1 : ℤ) else 0 := by
                        simp
              _ = (#{s ∈ (Finset.univ : Finset (EdgeSetType (G := G) q)) | p s} : ℤ) := by
                    simpa using (Finset.sum_boole (p := p) (s := (Finset.univ : Finset _)) : _)
              _ = (Fintype.card {s : EdgeSetType (G := G) q // p s} : ℤ) := by
                    simp [p, Fintype.card_subtype]
              _ = (Nat.card {s : EdgeSetType (G := G) q // p s} : ℤ) := by
                    exact congrArg (fun n : ℕ => (n : ℤ)) Nat.card_eq_fintype_card.symm
    _ = (Nat.card G.SpanningTree : ℤ) := by
          exact congrArg (fun n : ℕ => (n : ℤ))
            (Nat.card_congr (treeEdgeSetTypeEquivSpanningTree (G := G) q))
    _ = (G.spanningTreeCount : ℤ) := by rw [spanningTreeCount]


theorem kirchhoff_matrix_tree (q : V) :
    (G.reducedLaplacian ℝ q).det = (G.spanningTreeCount : ℝ) := by
  convert congr_arg ( fun x : ℤ => ( x : ℝ ) ) ( kirchhoff_matrix_tree_int G q ) using 1;
  unfold SimpleGraph.reducedLaplacian SimpleGraph.lapMatrix SimpleGraph.degMatrix SimpleGraph.adjMatrix; simp +decide [ Matrix.det_apply' ] ; ring_nf;
  simp +decide [ Matrix.diagonal ]

end

end SimpleGraph
