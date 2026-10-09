import SpanningTreeIsoperimetry.NormalizedExponentialNonzero
import SpanningTreeIsoperimetry.RegularizedMatrixNormalization
import SpanningTreeIsoperimetry.RegularizedStripMonotonicity

/-! Actual finite-section normalization, independently of the value of the
Toeplitz--Hankel constant. The nonzero determinant limit identifies the bulk
coefficient and the regularized strip-energy supremum. -/
namespace SpanningTreeIsoperimetry.RegularizedFiniteSectionLimit
open RegularizedCircleFactorization OneSidedLaurentCompatibility OneSidedToeplitz
open OneSidedLaurentKernels ToeplitzHankelKernels LaurentConvolutionAlgebra
open NormalizedToeplitzFactorization NormalizedExponentialNonzero
open RegularizedMatrixNormalization RegularizedStripSymbol RegularizedStripNormalization
open RegularizedBoundaryKernel RegularizedCornerDeterminant StripSpectralRegularization
open SummableKernelProduct AbsolutelySummableDeterminant SummableKernelDeterminant
open FiniteSectionPadding Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def determinant (z : ℝ) (hz : 4<z) : ℝ :=
  detLimit (perturbation (logSeries z) 1)
    (perturbation_summable (logSeries_constant z) (logSeries_weighted hz) 1)

private theorem section_identity_sub (A : Kernel) (k : ℕ) :
    1+finiteSection (A-T unitCoeff) k=finiteSection A k := by
  ext i j
  change (if i=j then (1 : ℝ) else 0)+(A i.val j.val-T unitCoeff i.val j.val)=A i.val j.val
  rw [T_unit_apply]
  by_cases hij : i=j
  · subst j
    simp
  · have hv : i.val≠j.val := fun h => hij (Fin.ext h)
    simp [hij,hv]

/-- The lower/upper factors have determinant one in every finite section. -/
theorem sandwich_det_eq {z : ℝ} (hz : 4<z) (k : ℕ) :
    (finiteSection (F (positiveExponential (logSeries z) 1)
      (positiveExponential (logSeries z) (-1))) k).det=(normalizedMatrix z k).det := by
  let a := positiveExponential (logSeries z) 1
  let c := positiveExponential (logSeries z) (-1)
  have hc0 : c 0=1 := by
    change PowerSeries.coeff 0 (PositiveFrequencyExponential.exponential (logSeries z) (-1))=1
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      exponential_constant (logSeries_constant z) (-1)
  have hl := T_lower (positive_support (logSeries z) (-1))
  have hu := T_upper (flip_nonnegative (positive_support (logSeries z) (-1)))
  have hld (i : ℕ) : T c i i=1 := by simp only [T,sub_self,hc0]
  have hud (i : ℕ) : T (flip c) i i=1 := by
    simp only [T,ToeplitzHankelKernels.flip,sub_self,neg_zero,hc0]
  have he := TriangularCompression.sandwich_det hl hu hld hud (M (NormalizedToeplitzFactorization.symbol a)) k
  change (finiteSection (F a c) k).det=
    (finiteSection (M (NormalizedToeplitzFactorization.symbol a)) k).det
  simpa only [one_mul,one_pow,F] using he

/-- Convergence of the actual normalized finite Green determinants. -/
theorem normalized_det_tendsto {z : ℝ} (hz : 4<z) :
    Tendsto (fun k : ℕ => (normalizedMatrix z k).det) atTop (𝓝 (determinant z hz)) := by
  let a := positiveExponential (logSeries z) 1
  let c := positiveExponential (logSeries z) (-1)
  have ha := positive_weighted (logSeries_constant z) (logSeries_weighted hz) 1
  have hc := positive_weighted (logSeries_constant z) (logSeries_weighted hz) (-1)
  have has := positive_support (logSeries z) 1
  have hcs := positive_support (logSeries z) (-1)
  have hinv := positive_inverse (logSeries_constant z) (logSeries_weighted hz) 1
  have hf := detLimit_tendsto (F a c-T unitCoeff) (F_difference_summable ha hc has hinv)
  have he := determinant_normalization ha hc has hcs hinv
  rw [he] at hf
  have hs (k : ℕ) : (1+finiteSection (F a c-T unitCoeff) k).det=(normalizedMatrix z k).det := by
    rw [section_identity_sub]
    exact sandwich_det_eq hz k
  simpa only [hs,determinant,perturbation,NormalizedExponentialInverse.C,
    NormalizedExponentialInverse.identity,a,c] using hf

theorem determinant_ne_zero {z : ℝ} (hz : 4<z) : determinant z hz≠0 :=
  NormalizedExponentialNonzero.determinant_ne_zero (logSeries_constant z) (logSeries_weighted hz) 1

theorem determinant_pos {z : ℝ} (hz : 4<z) : 0<determinant z hz := by
  have hnonneg : 0≤determinant z hz :=
    le_of_tendsto_of_tendsto tendsto_const_nhds (normalized_det_tendsto hz)
      (Eventually.of_forall (fun k => (normalized_det_pos hz k).le))
  exact lt_of_le_of_ne hnonneg (Ne.symm (determinant_ne_zero hz))

theorem normalized_logdet_tendsto {z : ℝ} (hz : 4<z) :
    Tendsto (fun k : ℕ => Real.log (normalizedMatrix z k).det) atTop
      (𝓝 (Real.log (determinant z hz))) :=
  (Real.continuousAt_log (determinant_ne_zero hz)).tendsto.comp (normalized_det_tendsto hz)

theorem normalized_logdet_div_length {z : ℝ} (hz : 4<z) :
    Tendsto (fun k : ℕ => Real.log (normalizedMatrix z k).det/(k : ℝ)) atTop (𝓝 0) :=
  (normalized_logdet_tendsto hz).div_atTop tendsto_natCast_atTop_atTop

/-- The first-order log determinant coefficient comes from the independent
finite-section limit and is not assumed from the loop energy. -/
theorem raw_logdet_div_length {z : ℝ} (hz : 4<z) :
    Tendsto (fun k : ℕ => Real.log (boundaryMatrix z k).det/(k : ℝ)) atTop
      (𝓝 (coefficientZ z 0)) := by
  have h := (normalized_logdet_div_length hz).add_const (coefficientZ z 0)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk0 : (k : ℝ)≠0 := by exact_mod_cast (by omega : k≠0)
  rw [normalized_logdet hz]
  field_simp
  <;> ring

/-- Actual bulk-to-symbol normalization, with the independent determinant
limit premise fully discharged. -/
theorem bulkEntropy_eq_neg_coefficient {z : ℝ} (hz : 4<z) :
    bulkEntropy z= -coefficientZ z 0 := by
  apply bulkEntropy_eq_neg_coefficient_of_limit hz
  simpa only [boundaryMatrix_eq_toeplitzHankel hz] using raw_logdet_div_length hz

theorem spectralEnergy_eq_neg_log_normalized {z : ℝ} (hz : 4<z) (k : ℕ) :
    spectralEnergy (Ferrers.horizontalStrip k) z= -Real.log (normalizedMatrix z k).det := by
  rw [strip_energy_normalized hz,bulkEntropy_eq_neg_coefficient hz]
  ring

theorem spectralEnergy_tendsto {z : ℝ} (hz : 4<z) :
    Tendsto (fun k : ℕ => spectralEnergy (Ferrers.horizontalStrip k) z) atTop
      (𝓝 (-Real.log (determinant z hz))) := by
  simpa only [spectralEnergy_eq_neg_log_normalized hz] using (normalized_logdet_tendsto hz).neg

/-- The actual regularized strip supremum is the negative logarithm of the
positive normalized determinant limit. The explicit Fourier constant is
still a separate calculation. -/
theorem stripSupremum_eq_neg_log_determinant {z : ℝ} (hz : 4<z) :
    stripSupremum z= -Real.log (determinant z hz) :=
  RegularizedStripMonotonicity.stripSupremum_eq_of_limit hz.le (spectralEnergy_tendsto hz)

end
end SpanningTreeIsoperimetry.RegularizedFiniteSectionLimit
