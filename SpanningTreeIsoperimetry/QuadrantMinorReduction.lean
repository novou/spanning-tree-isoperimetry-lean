import SpanningTreeIsoperimetry.QuadrantMinorEnergy

/-! Determinant reduction by the interior Dirichlet rows. The hypotheses are
explicit matrix-product certificates, proved from the actual kernel for each
small corner obstruction; no inverse of the boundary minor is required. -/
namespace SpanningTreeIsoperimetry.QuadrantMinorReduction
open Matrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem det_from_interior_rows
    (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (G₁₁ : Matrix ι ι ℝ) (G₁₂ : Matrix ι κ ℝ)
    (G₂₁ : Matrix κ ι ℝ) (G₂₂ : Matrix κ κ ℝ)
    (h₁ : A*G₁₁+B*G₂₁=1) (h₂ : A*G₁₂+B*G₂₂=0) :
    A.det*(fromBlocks G₁₁ G₁₂ G₂₁ G₂₂).det=G₂₂.det := by
  have hT : (fromBlocks A B (0 : Matrix κ ι ℝ) (1 : Matrix κ κ ℝ)).det=A.det := by
    rw [det_fromBlocks_zero₂₁,det_one,mul_one]
  rw [← hT,← det_mul,fromBlocks_multiply,h₁,h₂]
  simp only [Matrix.zero_mul,Matrix.one_mul,zero_add]
  rw [det_fromBlocks_zero₁₂,det_one,one_mul]

theorem det_eq_boundary_div
    (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (G₁₁ : Matrix ι ι ℝ) (G₁₂ : Matrix ι κ ℝ)
    (G₂₁ : Matrix κ ι ℝ) (G₂₂ : Matrix κ κ ℝ)
    (hA : A.det≠0) (h₁ : A*G₁₁+B*G₂₁=1) (h₂ : A*G₁₂+B*G₂₂=0) :
    (fromBlocks G₁₁ G₁₂ G₂₁ G₂₂).det=G₂₂.det/A.det := by
  apply (eq_div_iff hA).mpr
  simpa only [mul_comm] using det_from_interior_rows A B G₁₁ G₁₂ G₂₁ G₂₂ h₁ h₂

end SpanningTreeIsoperimetry.QuadrantMinorReduction
