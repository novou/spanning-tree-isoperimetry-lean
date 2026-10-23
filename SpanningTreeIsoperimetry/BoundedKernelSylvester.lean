module

public import SpanningTreeIsoperimetry.BoundedKernelProductTail
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

/-! Sylvester's identity for actual finite-section determinant limits with
one summable factor and one row/column-bounded multiplier. -/
namespace SpanningTreeIsoperimetry.BoundedKernelSylvester
open BoundedKernelProduct BoundedKernelProductTail SummableKernelProduct
open AbsolutelySummableDeterminant FiniteSectionPadding SummableKernelDeterminant Filter
open scoped Topology
noncomputable section

theorem finiteSection_transpose (A : Kernel) (n : ℕ) :
    finiteSection (transpose A) n=(finiteSection A n).transpose := rfl

theorem detLimit_transpose {A : Kernel} (hA : Summable (entryNorm A)) :
    detLimit (transpose A) (transpose_summable hA)=detLimit A hA := by
  have ht := detLimit_tendsto A hA
  have he (n : ℕ) : (1+finiteSection (transpose A) n).det=(1+finiteSection A n).det := by
    rw [finiteSection_transpose,← Matrix.transpose_one,← Matrix.transpose_add,Matrix.det_transpose]
    simp only [Matrix.transpose_one]
  exact tendsto_nhds_unique (detLimit_tendsto (transpose A) (transpose_summable hA))
    (by simpa only [he] using ht)

theorem finite_sylvester_transpose (A B : Kernel) (n : ℕ) :
    (1+finiteSection (transpose A) n*finiteSection (transpose B) n).det=
      (1+finiteSection A n*finiteSection B n).det := by
  rw [finiteSection_transpose,finiteSection_transpose,← Matrix.transpose_mul,
    ← Matrix.transpose_one,← Matrix.transpose_add,Matrix.det_transpose,Matrix.det_one_add_mul_comm]
  simp only [Matrix.transpose_one]

theorem determinant_sylvester {A B : Kernel} (hA : Summable (entryNorm A))
    {C D : ℝ} (hBr : RowBound B C) (hBc : ColumnBound B D) :
    detLimit (product A B) (right_summable hA hBr)=
      detLimit (product B A) (left_summable hBc hA) := by
  have ht := finite_product_det_tendsto (transpose_summable hA) hBc
  have ht' : Tendsto (fun n => (1+finiteSection A n*finiteSection B n).det) atTop
      (𝓝 (detLimit (product (transpose A) (transpose B))
        (right_summable (transpose_summable hA) hBc))) := by
    simpa only [finite_sylvester_transpose] using ht
  have he := tendsto_nhds_unique (finite_product_det_tendsto hA hBr) ht'
  have hc := detLimit_congr (right_summable (transpose_summable hA) hBc)
    (transpose_summable (left_summable hBc hA)) (transpose_product B A).symm
  exact he.trans (hc.trans (detLimit_transpose (left_summable hBc hA)))

end
end SpanningTreeIsoperimetry.BoundedKernelSylvester
