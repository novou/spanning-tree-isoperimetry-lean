import SpanningTreeIsoperimetry.ToeplitzHankelTraceConstants
import SpanningTreeIsoperimetry.RegularizedCircleFactorization
import SpanningTreeIsoperimetry.EvenExponentialPath
import SpanningTreeIsoperimetry.RegularizedFourierQuadraticLimit

/-! The actual logarithmic strip coefficients evaluate the linear and
quadratic trace constants in the determinant deformation. -/
namespace SpanningTreeIsoperimetry.RegularizedTraceValues
open RegularizedCircleFactorization RegularizedStripSymbol RegularizedFourierWeighted
open OneSidedToeplitz EvenExponentialPath ToeplitzHankelKernels ToeplitzHankelTraceConstants
open SummableKernelProduct SummableKernelTrace
noncomputable section

theorem positive_log_coefficient (z : ℝ) {n : ℕ} (hn : 0<n) :
    lift (logSeries z) (n : ℤ)=coefficientZ z n := by
  rw [lift_nat,logSeries_coefficient,positivePart,if_neg (by omega : n≠0)]

theorem even_log_coefficient (z : ℝ) {n : ℕ} (hn : 0<n) :
    evenGenerator (logSeries z) (n : ℤ)=coefficientZ z n := by
  have hnz : (0 : ℤ)<(n : ℤ) := by exact_mod_cast hn
  change lift (logSeries z) (n : ℤ)+lift (logSeries z) (-(n : ℤ))=coefficientZ z n
  rw [lift_negative (logSeries z) (n := -(n : ℤ)) (by omega),add_zero,positive_log_coefficient z hn]

def linearTrace (z : ℝ) : ℝ :=
  trace (M (evenGenerator (logSeries z))-T (evenGenerator (logSeries z)))

def quadraticTrace (z : ℝ) : ℝ :=
  trace (product (H (lift (logSeries z))) (H (lift (logSeries z))))

theorem linearTrace_eq {z : ℝ} (hz : 4<z) :
    linearTrace z= -RegularizedFourierQuadraticLimit.evenSum z := by
  rw [linearTrace,trace_M_sub_T (generator_weighted (logSeries_weighted hz))]
  unfold RegularizedFourierQuadraticLimit.evenSum
  congr 1
  apply tsum_congr
  intro n
  exact even_log_coefficient z (by omega : 0<2*(n+1))

theorem quadraticTrace_eq {z : ℝ} (hz : 4<z) :
    quadraticTrace z=RegularizedFourierQuadratic.quadratic z := by
  rw [quadraticTrace,trace_H_product (weighted_lift (logSeries_weighted hz))]
  unfold RegularizedFourierQuadratic.quadratic
  apply tsum_congr
  intro n
  rw [positive_log_coefficient z (by omega : 0<n+1)]

end
end SpanningTreeIsoperimetry.RegularizedTraceValues
