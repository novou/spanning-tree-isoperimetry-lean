module

public import SpanningTreeIsoperimetry.DomainSpectral
public import SquareMaximality.Boundary.DeterminantSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

/-! Finite Dirichlet Green matrices as convergent adjacency-walk series.
Strict spectral control is used; the maximum row sum may equal four. -/
namespace SpanningTreeIsoperimetry.MatrixGreenSeries

open scoped BigOperators Matrix Classical
open SquareMaximality.Boundary
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The scalar geometric series at any eigenvalue strictly between -4 and 4. -/
theorem eigenvalue_hasSum {x : ℝ} (hx : |x| < 4) :
    HasSum (fun n : ℕ => x ^ n / 4 ^ (n + 1)) (4 - x)⁻¹ := by
  have hr : |x / 4| < 1 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact (div_lt_one (by norm_num : (0 : ℝ) < 4)).mpr hx
  have hx4 : 4 - x ≠ 0 := by
    have h := (abs_lt.mp hx).2
    linarith
  have h := (hasSum_geometric_of_abs_lt_one hr).div_const 4
  have he : (1 - x / 4)⁻¹ / 4 = (4 - x)⁻¹ := by
    field_simp
    <;> ring
  rw [he] at h
  refine h.congr_fun fun n => ?_
  rw [div_pow, pow_succ]
  ring

/-- A strict eigenvalue bound gives the actual inverse matrix as an adjacency
power series, including finite domains whose interior row sums equal four. -/
theorem inverse_hasSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hspec : ∀ i, |hA.eigenvalues i| < 4) :
    HasSum (fun n : ℕ => (4 : ℝ)⁻¹ ^ (n + 1) • A ^ n)
      ((4 : ℝ) • (1 : Matrix ι ι ℝ) - A)⁻¹ := by
  let D : Matrix ι ι ℝ := Matrix.diagonal hA.eigenvalues
  let T : Matrix ι ι ℝ := Matrix.diagonal (fun i => (4 - hA.eigenvalues i)⁻¹)
  let φ := Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
  have hspecA : φ D = A := by
    simpa [φ, D, Function.comp_def] using hA.spectral_theorem.symm
  have hs : HasSum (fun n : ℕ => Matrix.diagonal
      (fun i => hA.eigenvalues i ^ n / 4 ^ (n + 1))) T := by
    apply HasSum.matrix_diagonal
    exact Pi.hasSum.mpr (fun i => eigenvalue_hasSum (hspec i))
  have hsum : HasSum (fun n : ℕ => φ (Matrix.diagonal
      (fun i => hA.eigenvalues i ^ n / 4 ^ (n + 1)))) (φ T) := by
    simpa only [φ, Unitary.conjStarAlgAut_apply] using
      (hs.mul_left (hA.eigenvectorUnitary : Matrix ι ι ℝ)).mul_right
        (star (hA.eigenvectorUnitary : Matrix ι ι ℝ))
  have hdiag : ((4 : ℝ) • (1 : Matrix ι ι ℝ) - D) * T = 1 := by
    have he : (4 : ℝ) • (1 : Matrix ι ι ℝ) - D =
        Matrix.diagonal (fun i => 4 - hA.eigenvalues i) := by
      ext i j
      by_cases hij : i = j <;> simp [D, hij, Matrix.diagonal_apply, Matrix.one_apply]
    rw [he]
    dsimp only [T]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      have hi := (abs_lt.mp (hspec i)).2
      simp [Matrix.one_apply, show 4 - hA.eigenvalues i ≠ 0 by linarith]
    · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hinv : ((4 : ℝ) • (1 : Matrix ι ι ℝ) - A)⁻¹ = φ T := by
    apply Matrix.inv_eq_right_inv
    have he : (4 : ℝ) • (1 : Matrix ι ι ℝ) - A = φ ((4 : ℝ) • 1 - D) := by
      simp [map_sub, map_smul, hspecA]
    rw [he, ← map_mul, hdiag, map_one]
  rw [hinv]
  refine hsum.congr_fun fun n => ?_
  have he : Matrix.diagonal (fun i => hA.eigenvalues i ^ n / 4 ^ (n + 1)) =
      (4 : ℝ)⁻¹ ^ (n + 1) • D ^ n := by
    dsimp only [D]
    rw [Matrix.diagonal_pow]
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.diagonal_apply, hij, div_eq_mul_inv, inv_pow, mul_comm]
  rw [he, map_smul, map_pow, hspecA]

/-- Entrywise form suitable for counting finite walks. -/
theorem inverse_entry_hasSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hspec : ∀ i, |hA.eigenvalues i| < 4) (i j : ι) :
    HasSum (fun n : ℕ => (A ^ n) i j / 4 ^ (n + 1))
      (((4 : ℝ) • (1 : Matrix ι ι ℝ) - A)⁻¹ i j) := by
  have h := Pi.hasSum.mp (Pi.hasSum.mp (inverse_hasSum hA hspec) i) j
  simpa only [Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv, inv_pow, mul_comm] using h

/-- The finite lattice spectral estimate discharges the generic hypothesis. -/
theorem domain_inverse_entry_hasSum (S : Domain) (i j : (S : Set Vertex)) :
    HasSum (fun n : ℕ => (((domainGraph S).adjMatrix ℝ) ^ n) i j / 4 ^ (n + 1))
      (((4 : ℝ) • (1 : Matrix (S : Set Vertex) (S : Set Vertex) ℝ) -
        (domainGraph S).adjMatrix ℝ)⁻¹ i j) :=
  inverse_entry_hasSum (DomainSpectral.adjacency_isHermitian S)
    (DomainSpectral.adjacency_eigenvalues_bound S) i j

/-- Natural-coordinate face windows satisfy the same actual Green series. -/
theorem face_inverse_entry_hasSum {R S : ℕ} {U : Finset LatticePoint}
    (hU : U ⊆ faceIndices R S) (i j : {p // p ∈ U}) :
    HasSum (fun n : ℕ => (((faceGraph U).adjMatrix ℝ) ^ n) i j / 4 ^ (n + 1))
      ((fourIminusAdjacency U)⁻¹ i j) :=
  inverse_entry_hasSum ((faceGraph U).isHermitian_adjMatrix ℝ)
    (SpectralBound.faceAdjacencySpectralBound_of_subset hU) i j

/-- Each Green entry is the weighted count of actual finite graph walks. -/
theorem face_inverse_walk_hasSum {R S : ℕ} {U : Finset LatticePoint}
    (hU : U ⊆ faceIndices R S) (i j : {p // p ∈ U}) :
    HasSum (fun n : ℕ =>
      (Fintype.card {p : (faceGraph U).Walk i j // p.length = n} : ℝ) / 4 ^ (n + 1))
      ((fourIminusAdjacency U)⁻¹ i j) := by
  refine (face_inverse_entry_hasSum hU i j).congr_fun fun n => ?_
  rw [SimpleGraph.adjMatrix_pow_apply_eq_card_walk]
  congr 1

end SpanningTreeIsoperimetry.MatrixGreenSeries
