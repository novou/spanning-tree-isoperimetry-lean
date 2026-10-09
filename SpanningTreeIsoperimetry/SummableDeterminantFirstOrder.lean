import SpanningTreeIsoperimetry.SummableKernelDeterminant
import SpanningTreeIsoperimetry.SummableKernelTrace
import SpanningTreeIsoperimetry.FiniteDeterminantFirstOrder
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Passing the dimension-free determinant remainder to the actual
finite-section limit. This supplies a local determinant derivative without
an external operator determinant theorem. -/
namespace SpanningTreeIsoperimetry.SummableDeterminantFirstOrder
open SummableKernelProduct SummableKernelDeterminant SummableKernelTrace
open AbsolutelySummableDeterminant FiniteSectionPadding FiniteDeterminantContinuity
open Filter Asymptotics
open scoped Topology BigOperators
noncomputable section

def truncatedNorm (K : Kernel) (n : ℕ) (p : ℕ×ℕ) : ℝ :=
  if p.1<n ∧ p.2<n then entryNorm K p else 0

theorem tsum_truncatedNorm (K : Kernel) (n : ℕ) :
    (∑' p : ℕ×ℕ,truncatedNorm K n p)=mass (finiteSection K n) := by
  rw [tsum_eq_sum (s := Finset.range n ×ˢ Finset.range n)]
  · rw [Finset.sum_product]
    simp_rw [← Fin.sum_univ_eq_sum_range]
    unfold mass rowMass finiteSection
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp [truncatedNorm,entryNorm,i.isLt,j.isLt]
  · intro p hp
    simp only [Finset.mem_product,Finset.mem_range] at hp
    exact if_neg hp

theorem mass_tendsto {K : Kernel} (hK : Summable (entryNorm K)) :
    Tendsto (fun n => mass (finiteSection K n)) atTop (𝓝 (totalMass K)) := by
  have ht := tendsto_tsum_of_dominated_convergence hK
    (f := truncatedNorm K) (g := entryNorm K)
    (fun p => by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (max p.1 p.2+1)] with n hn
      simp [truncatedNorm,show p.1<n ∧ p.2<n by omega])
    (Eventually.of_forall (fun n p => by
      unfold truncatedNorm
      split_ifs
      · simp only [Real.norm_eq_abs,entryNorm,abs_abs]
        exact le_rfl
      · simpa only [norm_zero,entryNorm] using abs_nonneg (K p.1 p.2)))
  simpa only [tsum_truncatedNorm,totalMass] using ht

theorem determinant_first_order {K : Kernel} (hK : Summable (entryNorm K)) :
    |detLimit K hK-1-trace K|≤Real.exp (totalMass K)-1-totalMass K := by
  have hd := ((detLimit_tendsto K hK).sub_const 1).sub (finite_trace_tendsto hK)
  have hm := mass_tendsto hK
  exact le_of_tendsto_of_tendsto hd.abs ((hm.rexp.sub_const 1).sub hm)
    (Eventually.of_forall (fun n => FiniteDeterminantFirstOrder.determinant_first_order (finiteSection K n)))

def scale (t : ℝ) (K : Kernel) : Kernel := fun i j => t*K i j

theorem scale_summable (t : ℝ) {K : Kernel} (hK : Summable (entryNorm K)) :
    Summable (entryNorm (scale t K)) := by
  change Summable (fun p : ℕ×ℕ => |t*K p.1 p.2|)
  simpa only [entryNorm,abs_mul] using hK.mul_left |t|

theorem scale_mass (t : ℝ) (K : Kernel) : totalMass (scale t K)=|t| * totalMass K := by
  simp only [totalMass,entryNorm,scale,abs_mul,tsum_mul_left]

theorem scale_trace (t : ℝ) (K : Kernel) : trace (scale t K)=t*trace K := by
  simp only [trace,scale,tsum_mul_left]

def scalarDeterminant (K : Kernel) (hK : Summable (entryNorm K)) (t : ℝ) : ℝ :=
  detLimit (scale t K) (scale_summable t hK)

theorem scalar_zero (K : Kernel) (hK : Summable (entryNorm K)) : scalarDeterminant K hK 0=1 := by
  have he : scale 0 K=0 := by ext i j; simp [scale]
  exact (detLimit_congr (scale_summable 0 hK) zero_summable he).trans detLimit_zero

theorem scalar_remainder (K : Kernel) (hK : Summable (entryNorm K)) (t : ℝ) :
    |scalarDeterminant K hK t-1-t*trace K|≤
      Real.exp (|t| * totalMass K)-1-|t| * totalMass K := by
  simpa only [scalarDeterminant,scale_mass,scale_trace] using determinant_first_order (scale_summable t hK)


theorem hasDerivAt_scalar_zero (K : Kernel) (hK : Summable (entryNorm K)) :
    HasDerivAt (scalarDeterminant K hK) (trace K) 0 := by
  let M := totalMass K
  have hM : 0≤M := totalMass_nonneg K
  have ht : Tendsto (fun t : ℝ => |t| * M) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.continuousAt.tendsto.mul_const M :
      Tendsto (fun t : ℝ => |t| * M) (𝓝 0) (𝓝 (|0| * M)))
  have he : (fun t : ℝ => Real.exp (|t| * M)-1-|t| * M) =o[𝓝 0] (fun t => |t| * M) := by
    have h := (Real.exp_sub_sum_range_succ_isLittleO_pow 1).comp_tendsto ht
    simpa [Function.comp_def,Finset.sum_range_succ,sub_add_eq_sub_sub] using h
  have hb : (fun t : ℝ => |t| * M) =O[𝓝 0] (fun t => t) := by
    apply IsBigO.of_bound M
    exact Eventually.of_forall (fun t => by
      simp only [Real.norm_eq_abs,abs_mul,abs_abs,abs_of_nonneg hM]
      exact le_of_eq (mul_comm _ _))
  have hr : (fun t : ℝ => scalarDeterminant K hK t-1-t*trace K) =O[𝓝 0]
      (fun t => Real.exp (|t| * M)-1-|t| * M) := by
    apply IsBigO.of_bound 1
    apply Eventually.of_forall
    intro t
    simp only [Real.norm_eq_abs,one_mul]
    exact (scalar_remainder K hK t).trans (le_abs_self _)
  have ho := hr.trans_isLittleO (he.trans_isBigO hb)
  apply HasDerivAt.of_isLittleO
  simpa only [scalar_zero,sub_zero,smul_eq_mul] using ho

end
end SpanningTreeIsoperimetry.SummableDeterminantFirstOrder
