import SpanningTreeIsoperimetry.BoundaryGreenBounds
import SpanningTreeIsoperimetry.DeterminantComparison

/-! Actual finite Green matrices at every spectral parameter z≥4.
The coefficients count actual finite face walks. Their comparison with the
critical inverse gives a uniform bound for the future quadrant exhaustion. -/
namespace SpanningTreeIsoperimetry.RegularizedGreenSeries
open Ferrers CornerEnergy BoundaryGreenLoss BoundaryGreenBounds SquareMaximality.Boundary
open scoped Matrix BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem eigenvalue_hasSum {c x : ℝ} (hc : 0<c) (hx : |x|<c) :
    HasSum (fun n : ℕ => x^n/c^(n+1)) (c-x)⁻¹ := by
  have hr : |x/c|<1 := by
    rw [abs_div,abs_of_pos hc]
    exact (div_lt_one hc).mpr hx
  have hcx : c-x≠0 := by have h := (abs_lt.mp hx).2; linarith
  have h := (hasSum_geometric_of_abs_lt_one hr).div_const c
  have he : (1-x/c)⁻¹/c=(c-x)⁻¹ := by
    field_simp [hc.ne',hcx]
    <;> ring
  rw [he] at h
  refine h.congr_fun fun n => ?_
  rw [div_pow,pow_succ]
  ring

theorem inverse_hasSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {c : ℝ} (hc : 0<c)
    (hspec : ∀ i,|hA.eigenvalues i|<c) :
    HasSum (fun n : ℕ => c⁻¹^(n+1) • A^n)
      (c • (1 : Matrix ι ι ℝ)-A)⁻¹ := by
  let D : Matrix ι ι ℝ := Matrix.diagonal hA.eigenvalues
  let T : Matrix ι ι ℝ := Matrix.diagonal (fun i => (c-hA.eigenvalues i)⁻¹)
  let φ := Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
  have hspecA : φ D=A := by simpa [φ,D,Function.comp_def] using hA.spectral_theorem.symm
  have hs : HasSum (fun n : ℕ => Matrix.diagonal
      (fun i => hA.eigenvalues i^n/c^(n+1))) T := by
    apply HasSum.matrix_diagonal
    exact Pi.hasSum.mpr (fun i => eigenvalue_hasSum hc (hspec i))
  have hsum : HasSum (fun n : ℕ => φ (Matrix.diagonal
      (fun i => hA.eigenvalues i^n/c^(n+1)))) (φ T) := by
    simpa only [φ,Unitary.conjStarAlgAut_apply] using
      (hs.mul_left (hA.eigenvectorUnitary : Matrix ι ι ℝ)).mul_right
        (star (hA.eigenvectorUnitary : Matrix ι ι ℝ))
  have hdiag : (c • (1 : Matrix ι ι ℝ)-D)*T=1 := by
    have he : c • (1 : Matrix ι ι ℝ)-D=Matrix.diagonal (fun i => c-hA.eigenvalues i) := by
      ext i j
      by_cases hij : i=j <;> simp [D,hij,Matrix.diagonal_apply,Matrix.one_apply]
    rw [he]
    dsimp only [T]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i=j
    · subst j
      have hi := (abs_lt.mp (hspec i)).2
      simp [Matrix.one_apply,show c-hA.eigenvalues i≠0 by linarith]
    · simp [Matrix.diagonal_apply,Matrix.one_apply,hij]
  have hinv : (c • (1 : Matrix ι ι ℝ)-A)⁻¹=φ T := by
    apply Matrix.inv_eq_right_inv
    have he : c • (1 : Matrix ι ι ℝ)-A=φ (c • 1-D) := by simp [map_sub,map_smul,hspecA]
    rw [he,← map_mul,hdiag,map_one]
  rw [hinv]
  refine hsum.congr_fun fun n => ?_
  have he : Matrix.diagonal (fun i => hA.eigenvalues i^n/c^(n+1))=c⁻¹^(n+1) • D^n := by
    dsimp only [D]
    rw [Matrix.diagonal_pow]
    ext i j
    by_cases hij : i=j <;>
      simp [Matrix.diagonal_apply,hij,div_eq_mul_inv,inv_pow,mul_comm]
  rw [he,map_smul,map_pow,hspecA]

theorem inverse_entry_hasSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {c : ℝ} (hc : 0<c)
    (hspec : ∀ i,|hA.eigenvalues i|<c) (i j : ι) :
    HasSum (fun n : ℕ => (A^n) i j/c^(n+1))
      ((c • (1 : Matrix ι ι ℝ)-A)⁻¹ i j) := by
  have h := Pi.hasSum.mp (Pi.hasSum.mp (inverse_hasSum hA hc hspec) i) j
  simpa only [Matrix.smul_apply,smul_eq_mul,div_eq_mul_inv,inv_pow,mul_comm] using h

def dirichletZ (z : ℝ) (U : Diagram) : Matrix {p // p∈U} {p // p∈U} ℝ :=
  z • (1 : Matrix {p // p∈U} {p // p∈U} ℝ)-(faceGraph U).adjMatrix ℝ

theorem dirichletZ_det_pos {z : ℝ} (hz : 4≤z) {R S : ℕ} {U : Diagram}
    (hU : U⊆faceRectangle R S) : 0<(dirichletZ z U).det := by
  have hs := SpectralBound.faceAdjacencySpectralBound_of_subset ((foundation_faceIndices R S).symm ▸ hU)
  exact DeterminantComparison.det_shift_pos ((faceGraph U).isHermitian_adjMatrix ℝ)
    (fun i => (hs i).trans_le hz)

theorem face_inverse_walk_hasSum {z : ℝ} (hz : 4≤z) {R S : ℕ} {U : Diagram}
    (hU : U⊆faceRectangle R S) (i j : {p // p∈U}) :
    HasSum (fun n : ℕ =>
      (Fintype.card {w : (faceGraph U).Walk i j // w.length=n} : ℝ)/z^(n+1))
      ((dirichletZ z U)⁻¹ i j) := by
  have hs := SpectralBound.faceAdjacencySpectralBound_of_subset ((foundation_faceIndices R S).symm ▸ hU)
  have h := inverse_entry_hasSum ((faceGraph U).isHermitian_adjMatrix ℝ)
    (by linarith : 0<z) (fun i => (hs i).trans_le hz) i j
  refine h.congr_fun fun n => ?_
  rw [SimpleGraph.adjMatrix_pow_apply_eq_card_walk]
  congr 1

def greenZ (z : ℝ) (U : Diagram) (p q : Point) : ℝ :=
  if hp : p∈U then if hq : q∈U then (dirichletZ z U)⁻¹ ⟨p,hp⟩ ⟨q,hq⟩ else 0 else 0

@[simp] theorem greenZ_mem {z : ℝ} {U : Diagram} {p q : Point} (hp : p∈U) (hq : q∈U) :
    greenZ z U p q=(dirichletZ z U)⁻¹ ⟨p,hp⟩ ⟨q,hq⟩ := by simp [greenZ,hp,hq]

theorem greenZ_four (U : Diagram) (p q : Point) : greenZ 4 U p q=green U p q := rfl

theorem greenZ_nonneg {z : ℝ} (hz : 4≤z) {R S : ℕ} {U : Diagram}
    (hU : U⊆faceRectangle R S) (p q : Point) : 0≤greenZ z U p q := by
  have hz0 : 0<z := by linarith
  unfold greenZ
  split_ifs with hp hq
  · have h := face_inverse_walk_hasSum hz hU ⟨p,hp⟩ ⟨q,hq⟩
    exact hasSum_le (fun n => by positivity) (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0) h
  all_goals exact le_rfl

/-- Regularization decreases every actual finite inverse entry. -/
theorem greenZ_le_critical {z : ℝ} (hz : 4≤z) {R S : ℕ} {U : Diagram}
    (hU : U⊆faceRectangle R S) (p q : Point) : greenZ z U p q≤green U p q := by
  by_cases hp : p∈U
  · by_cases hq : q∈U
    · have hZ := face_inverse_walk_hasSum hz hU ⟨p,hp⟩ ⟨q,hq⟩
      have h4 := MatrixGreenSeries.face_inverse_walk_hasSum ((foundation_faceIndices R S).symm ▸ hU) ⟨p,hp⟩ ⟨q,hq⟩
      have hc (n : ℕ) :
          (Fintype.card {w : (faceGraph U).Walk ⟨p,hp⟩ ⟨q,hq⟩ // w.length=n} : ℝ)/z^(n+1)≤
          (Fintype.card {w : (faceGraph U).Walk ⟨p,hp⟩ ⟨q,hq⟩ // w.length=n} : ℝ)/4^(n+1) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤4) hz (n+1)
      simpa only [greenZ_mem hp hq,green_mem hp hq] using hasSum_le hc hZ h4
    · simp [greenZ,green,hp,hq]
  · simp [greenZ,green,hp]

theorem greenZ_le_tent {z : ℝ} (hz : 4≤z) {R S : ℕ} {U : Diagram}
    (hU : U⊆faceRectangle R S) (p q : Point) :
    greenZ z U p q≤min ((p.1 : ℝ)+1) ((q.1 : ℝ)+1) :=
  (greenZ_le_critical hz hU p q).trans (green_le_tent hU p q)

end
end SpanningTreeIsoperimetry.RegularizedGreenSeries
