import SpanningTreeIsoperimetry.SummableKernelProduct
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Actual diagonal traces and cyclicity with one summable factor. A bounded
multiplier need not itself have summable entries. No claim is made that an
arbitrary summable commutator of two bounded kernels has zero trace. -/
namespace SpanningTreeIsoperimetry.SummableKernelTrace
open AbsolutelySummableDeterminant SummableKernelProduct FiniteSectionPadding Filter
open scoped Topology BigOperators
noncomputable section

def trace (A : Kernel) : ℝ := ∑' i,A i i

theorem diagonal_norm_summable {A : Kernel} (hA : Summable (entryNorm A)) :
    Summable (fun i => |A i i|) := by
  exact hA.comp_injective (show Function.Injective (fun i : ℕ => (i,i)) from
    fun _ _ h => congrArg Prod.fst h)

theorem diagonal_summable {A : Kernel} (hA : Summable (entryNorm A)) :
    Summable (fun i => A i i) := by
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs] using diagonal_norm_summable hA

theorem finite_trace_tendsto {A : Kernel} (hA : Summable (entryNorm A)) :
    Tendsto (fun n => Matrix.trace (finiteSection A n)) atTop (𝓝 (trace A)) := by
  have ht := (diagonal_summable hA).hasSum.tendsto_sum_nat
  simp_rw [← Fin.sum_univ_eq_sum_range] at ht
  simpa only [trace,Matrix.trace,Matrix.diag,finiteSection] using ht

theorem pairing_summable {A T : Kernel} (hA : Summable (entryNorm A))
    {C : ℝ} (hC : 0≤C) (hT : ∀ i j,|T i j|≤C) :
    Summable (fun p : ℕ×ℕ => A p.1 p.2*T p.2 p.1) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hA.mul_right C)
  intro p
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_left (hT p.2 p.1) (abs_nonneg _)

/-- Cyclicity is justified by absolute convergence of the double sum,
using the summability of A itself and a pointwise bound on T. -/
theorem trace_product_comm {A T : Kernel} (hA : Summable (entryNorm A))
    {C : ℝ} (hC : 0≤C) (hT : ∀ i j,|T i j|≤C) :
    trace (product A T)=trace (product T A) := by
  let f : ℕ×ℕ → ℝ := fun p => A p.1 p.2*T p.2 p.1
  have hf : Summable f := pairing_summable hA hC hT
  have he : (∑' p : ℕ×ℕ,f p.swap)=∑' p : ℕ×ℕ,f p :=
    (Equiv.prodComm ℕ ℕ).tsum_eq f
  calc
    trace (product A T)=(∑' p : ℕ×ℕ,f p) := hf.tsum_prod.symm
    _=(∑' p : ℕ×ℕ,f p.swap) := he.symm
    _=(∑' i,∑' j,f (j,i)) := hf.prod_symm.tsum_prod
    _=trace (product T A) := by
      unfold trace product f
      simp only [mul_comm]

end
end SpanningTreeIsoperimetry.SummableKernelTrace
