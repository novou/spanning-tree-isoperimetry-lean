module

public import SpanningTreeIsoperimetry.Grid
public import SquareMaximality.Boundary.SpectralBound
public import Mathlib.LinearAlgebra.Matrix.Reindex

@[expose] public section

/-! Strict adjacency and holding-kernel spectral bounds for arbitrary finite
integer-lattice domains, including disconnected and empty domains. -/
namespace SpanningTreeIsoperimetry.DomainSpectral

open SquareMaximality.Boundary
open scoped Classical

/-- A uniform absolute-coordinate bound, also defined for the empty domain. -/
def coordinateRadius (S : Domain) : ℕ := S.sup (fun p => p.1.natAbs + p.2.natAbs)

/-- Move the whole finite domain into natural coordinates. -/
def naturalPoint (S : Domain) (p : Vertex) : LatticePoint :=
  ((p.1 + coordinateRadius S).toNat, (p.2 + coordinateRadius S).toNat)

def naturalDomain (S : Domain) : Finset LatticePoint := S.image (naturalPoint S)

theorem coordinate_bounds (S : Domain) {p : Vertex} (hp : p ∈ S) :
    -(coordinateRadius S : ℤ) ≤ p.1 ∧ p.1 ≤ coordinateRadius S ∧
    -(coordinateRadius S : ℤ) ≤ p.2 ∧ p.2 ≤ coordinateRadius S := by
  have hsup : p.1.natAbs + p.2.natAbs ≤ coordinateRadius S :=
    Finset.le_sup (f := fun p : Vertex => p.1.natAbs + p.2.natAbs) hp
  have hx : (p.1.natAbs : ℤ) ≤ coordinateRadius S := by exact_mod_cast (show p.1.natAbs ≤ coordinateRadius S by omega)
  have hy : (p.2.natAbs : ℤ) ≤ coordinateRadius S := by exact_mod_cast (show p.2.natAbs ≤ coordinateRadius S by omega)
  rw [Int.natCast_natAbs, abs_le] at hx hy
  exact ⟨hx.1, hx.2, hy.1, hy.2⟩

theorem naturalPoint_cast (S : Domain) (p : (S : Set Vertex)) :
    ((naturalPoint S p).1 : ℤ) = p.1.1 + coordinateRadius S ∧
    ((naturalPoint S p).2 : ℤ) = p.1.2 + coordinateRadius S := by
  have hb := coordinate_bounds S p.2
  exact ⟨Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)⟩

theorem naturalPoint_injective (S : Domain) :
    Function.Injective (fun p : (S : Set Vertex) => naturalPoint S p) := by
  intro p q hpq
  have hp := naturalPoint_cast S p
  have hq := naturalPoint_cast S q
  have hx := congrArg (fun z : LatticePoint => (z.1 : ℤ)) hpq
  have hy := congrArg (fun z : LatticePoint => (z.2 : ℤ)) hpq
  change ((naturalPoint S p).1 : ℤ) = ((naturalPoint S q).1 : ℤ) at hx
  change ((naturalPoint S p).2 : ℤ) = ((naturalPoint S q).2 : ℤ) at hy
  apply Subtype.ext
  apply Prod.ext <;> omega

theorem naturalDomain_subset_faces (S : Domain) :
    naturalDomain S ⊆ faceIndices (2 * coordinateRadius S + 1) (2 * coordinateRadius S + 1) := by
  intro z hz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
  have hb := coordinate_bounds S hp
  have hc := naturalPoint_cast S ⟨p, hp⟩
  change ((naturalPoint S p).1 : ℤ) = p.1 + coordinateRadius S ∧
    ((naturalPoint S p).2 : ℤ) = p.2 + coordinateRadius S at hc
  rw [mem_faceIndices]
  omega

theorem naturalPoint_adj_iff (S : Domain) (p q : (S : Set Vertex)) :
    faceLattice.Adj (naturalPoint S p) (naturalPoint S q) ↔ lattice.Adj p q := by
  have hp := naturalPoint_cast S p
  have hq := naturalPoint_cast S q
  change Nat.dist (naturalPoint S p).1 (naturalPoint S q).1 +
      Nat.dist (naturalPoint S p).2 (naturalPoint S q).2 = 1 ↔
    (p.1.1 = q.1.1 ∧ |p.1.2 - q.1.2| = 1) ∨
      (p.1.2 = q.1.2 ∧ |p.1.1 - q.1.1| = 1)
  rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1), abs_eq (by norm_num : (0 : ℤ) ≤ 1)]
  unfold Nat.dist
  omega

/-- The finite natural-coordinate face graph is exactly the original domain graph. -/
noncomputable def naturalGraphIso (S : Domain) :
    domainGraph S ≃g faceGraph (naturalDomain S) :=
  { Equiv.ofBijective
      (fun p => ⟨naturalPoint S p, Finset.mem_image_of_mem _ p.2⟩)
      ⟨by
        intro p q h
        exact naturalPoint_injective S (congrArg Subtype.val h),
       by
        intro z
        obtain ⟨p, hp, he⟩ := Finset.mem_image.mp z.2
        exact ⟨⟨p, hp⟩, Subtype.ext he⟩⟩ with
    map_rel_iff' := by intro p q; exact naturalPoint_adj_iff S p q }

theorem adjacency_reindex (S : Domain) :
    Matrix.reindexAlgEquiv ℝ ℝ (naturalGraphIso S).toEquiv ((domainGraph S).adjMatrix ℝ) =
      (faceGraph (naturalDomain S)).adjMatrix ℝ := by
  let e := naturalGraphIso S
  ext i j
  change ((domainGraph S).adjMatrix ℝ) (e.symm i) (e.symm j) =
    ((faceGraph (naturalDomain S)).adjMatrix ℝ) i j
  simp only [SimpleGraph.adjMatrix, Matrix.of_apply, e.symm.map_adj_iff]

/-- Every real spectral value of a finite lattice adjacency matrix lies in
`(-4,4)`. The construction works unchanged for an empty domain. -/
theorem adjacency_spectrum_bound (S : Domain) {x : ℝ}
    (hx : x ∈ spectrum ℝ ((domainGraph S).adjMatrix ℝ)) : |x| < 4 := by
  have hspec := AlgEquiv.spectrum_eq (Matrix.reindexAlgEquiv ℝ ℝ (naturalGraphIso S).toEquiv)
    ((domainGraph S).adjMatrix ℝ)
  rw [adjacency_reindex] at hspec
  have hmem : x ∈ spectrum ℝ ((faceGraph (naturalDomain S)).adjMatrix ℝ) := by
    rw [hspec]
    exact hx
  rw [((faceGraph (naturalDomain S)).isHermitian_adjMatrix ℝ).spectrum_real_eq_range_eigenvalues] at hmem
  obtain ⟨i, rfl⟩ := hmem
  exact SpectralBound.faceAdjacencySpectralBound_of_subset (naturalDomain_subset_faces S) i

theorem adjacency_isHermitian (S : Domain) : ((domainGraph S).adjMatrix ℝ).IsHermitian :=
  (domainGraph S).isHermitian_adjMatrix ℝ

theorem adjacency_eigenvalues_bound (S : Domain) (i : (S : Set Vertex)) :
    |(adjacency_isHermitian S).eigenvalues i| < 4 :=
  adjacency_spectrum_bound S ((adjacency_isHermitian S).eigenvalues_mem_spectrum_real i)

/-- Adding one holding loop shifts the spectrum by one. -/
theorem holding_spectrum_bound (S : Domain) {x : ℝ}
    (hx : x ∈ spectrum ℝ (1 + (domainGraph S).adjMatrix ℝ)) : |x| < 5 := by
  have hmem : x - 1 ∈ spectrum ℝ ((domainGraph S).adjMatrix ℝ) :=
    (spectrum.add_mem_add_iff (a := (domainGraph S).adjMatrix ℝ) (r := x - 1) (s := (1 : ℝ))).mp
      (by simpa using hx)
  have hb := adjacency_spectrum_bound S hmem
  rw [abs_lt] at hb ⊢
  constructor <;> linarith

theorem holding_isHermitian (S : Domain) : (1 + (domainGraph S).adjMatrix ℝ).IsHermitian :=
  Matrix.isHermitian_one.add (adjacency_isHermitian S)

theorem holding_eigenvalues_bound (S : Domain) (i : (S : Set Vertex)) :
    |(holding_isHermitian S).eigenvalues i| < 5 :=
  holding_spectrum_bound S ((holding_isHermitian S).eigenvalues_mem_spectrum_real i)

end SpanningTreeIsoperimetry.DomainSpectral
