import SpanningTreeIsoperimetry.SummableDeterminantAffine
import SpanningTreeIsoperimetry.SummableDeterminantContinuity

/-! Trace linearity, an absolute entry-mass bound, and differentiation along
summable kernel paths. Every trace in these statements is justified by actual
absolute summability; no trace is assigned to a nonsummable Toeplitz factor. -/
namespace SpanningTreeIsoperimetry.SummableTracePath
open SummableKernelProduct SummableKernelAlgebra SummableKernelTrace
open SummableDeterminantFirstOrder SummableDeterminantAffine
open SummableDeterminantContinuity AbsolutelySummableDeterminant Filter Asymptotics
open scoped Topology
noncomputable section

theorem trace_add {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) : trace (A+B)=trace A+trace B := by
  change (tsum (fun i : ℕ => A i i+B i i))=(tsum (fun i : ℕ => A i i))+(tsum (fun i : ℕ => B i i))
  exact (diagonal_summable hA).tsum_add (diagonal_summable hB)

theorem trace_sub {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) : trace (A-B)=trace A-trace B := by
  change (tsum (fun i : ℕ => A i i-B i i))=(tsum (fun i : ℕ => A i i))-(tsum (fun i : ℕ => B i i))
  exact (diagonal_summable hA).tsum_sub (diagonal_summable hB)

theorem abs_trace_le_mass {A : Kernel} (hA : Summable (entryNorm A)) :
    |trace A|≤totalMass A := by
  have hn : |trace A|≤∑' i,|A i i| := by
    simpa only [trace,Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun i => A i i)
        (by simpa only [Real.norm_eq_abs] using diagonal_norm_summable hA)
  have hi : Function.Injective (fun i : ℕ => (i,i)) := fun _ _ h => congrArg Prod.fst h
  exact hn.trans (tsum_comp_le_tsum_of_inj hA (fun _ => abs_nonneg _) hi)

/-- A mass-small remainder is trace-small, without any exchange of a
conditionally convergent diagonal sum and a derivative. -/
theorem trace_isLittleO_of_mass {R : ℝ → Kernel} (hR : ∀ t,Summable (entryNorm (R t)))
    (hrem : (fun t => totalMass (R t)) =o[𝓝 0] fun t => t) :
    (fun t => trace (R t)) =o[𝓝 0] fun t => t := by
  have hbig : (fun t => trace (R t)) =O[𝓝 0] (fun t => totalMass (R t)) := by
    apply isBigO_iff.mpr
    refine ⟨1,Eventually.of_forall (fun t => ?_)⟩
    simpa only [Real.norm_eq_abs,abs_of_nonneg (totalMass_nonneg _),one_mul] using
      abs_trace_le_mass (hR t)
  exact hbig.trans_isLittleO hrem

/-- The ordinary derivative of the actual trace along a mass-differentiable
path. There is no Banach-space structure on the kernel type in this proof. -/
theorem hasDerivAt_trace_zero {K : ℝ → Kernel} {H : Kernel}
    (hK : ∀ t,Summable (entryNorm (K t))) (hH : Summable (entryNorm H))
    (hrem : (fun t => totalMass (K t-affine (K 0) H t)) =o[𝓝 0] fun t => t) :
    HasDerivAt (fun t => trace (K t)) (trace H) 0 := by
  have hr := trace_isLittleO_of_mass
    (fun t => difference_summable (hK t) (affine_summable (hK 0) hH t)) hrem
  apply HasDerivAt.of_isLittleO
  convert hr using 1
  · funext t
    rw [trace_sub (hK t) (affine_summable (hK 0) hH t)]
    unfold affine
    rw [trace_add (hK 0) (scale_summable t hH),scale_trace]
    simp only [sub_zero,smul_eq_mul]
    ring
  · funext t
    exact sub_zero t

end
end SpanningTreeIsoperimetry.SummableTracePath
