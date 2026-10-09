import SpanningTreeIsoperimetry.BoundedKernelAlgebra
import SpanningTreeIsoperimetry.SummableKernelTrace
import SpanningTreeIsoperimetry.OneSidedLaurentKernels

/-! Trace invariance under an actual bounded kernel inverse pair, with an
entrywise-summable middle factor. No trace of a bounded nonsummable factor
is taken separately. -/
namespace SpanningTreeIsoperimetry.SummableTraceConjugation
open BoundedKernelProduct BoundedKernelAlgebra SummableKernelProduct SummableKernelTrace
open AbsolutelySummableDeterminant ToeplitzHankelKernels LaurentConvolutionAlgebra
open OneSidedLaurentKernels
noncomputable section

theorem rowBound_of_summable {K : Kernel} (hK : Summable (entryNorm K)) :
    RowBound K (totalMass K) := by
  refine ⟨totalMass_nonneg K,row_summable hK,?_⟩
  intro i
  have h := (rowNorm_summable hK).le_tsum i (fun j _ => rowNorm_nonneg K j)
  rwa [tsum_rowNorm hK] at h

theorem product_unit_right (K : Kernel) : product K (T unitCoeff)=K := by
  ext i j
  simp only [product,T_unit_apply,mul_ite,mul_one,mul_zero,tsum_ite_eq]

theorem trace_conjugation {A B K : Kernel} {c d : ℝ}
    (hA : RowBound A c) (hB : RowBound B d) (hK : Summable (entryNorm K))
    (hBA : product B A=T unitCoeff) :
    trace (product (product A K) B)=trace K := by
  have hk := rowBound_of_summable hK
  have hr := right_summable hK hB
  rw [BoundedKernelAlgebra.product_assoc hA hk hB]
  rw [← trace_product_comm hr hA.nonneg (entry_le hA)]
  rw [BoundedKernelAlgebra.product_assoc hk hB hA,hBA,product_unit_right]

end
end SpanningTreeIsoperimetry.SummableTraceConjugation
