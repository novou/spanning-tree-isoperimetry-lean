module

public import SpanningTreeIsoperimetry.NormalizedExponentialDerivativeAlgebra
public import SpanningTreeIsoperimetry.ConjugationTrace
public import SpanningTreeIsoperimetry.SummableTraceConjugation
public import SpanningTreeIsoperimetry.SummableTracePath
public import SpanningTreeIsoperimetry.ToeplitzHankelTraceConstants

@[expose] public section

/-! Reduction of the actual normalized log-determinant derivative to two
summable traces. All inverse/factor identities are actual kernel identities;
no trace is assigned to an individual bounded nonsummable Toeplitz kernel. -/
namespace SpanningTreeIsoperimetry.NormalizedLogDerivativeTrace
open OneSidedToeplitz OneSidedLaurentCompatibility EvenExponentialPath
open NormalizedExponentialInverse NormalizedExponentialNonzero NormalizedExponentialPath
open NormalizedExponentialDerivativeAlgebra ToeplitzHankelKernels ToeplitzHankelConvolution
open LaurentConvolutionAlgebra LaurentWeightedConvolution OneSidedLaurentKernels
open ToeplitzHankelMassBounds WeightedPowerSeries SummableKernelProduct
open BoundedKernelProduct BoundedKernelAlgebra SummableKernelTrace AbsolutelySummableDeterminant
open SummableTraceConjugation SummableTracePath SummableDeterminantContinuity
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def conjugatedQ (V : PowerSeries ℝ) (s : ℝ) : Kernel := product (product (L V s) (Q V)) (L V (-s))
def middle (V : PowerSeries ℝ) (s : ℝ) : Kernel := B V-P V-conjugatedQ V s

theorem middle_eq_difference (V : PowerSeries ℝ) (s : ℝ) :
    middle V s=(M (evenGenerator V)-T (evenGenerator V))-ConjugationTrace.D V s := by
  have hg : T (evenGenerator V)=P V+Q V := rfl
  rw [hg]
  change B V-P V-conjugatedQ V s=(B V-(P V+Q V))-(conjugatedQ V s-Q V)
  abel

theorem middle_summable {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) : Summable (entryNorm (middle V s)) := by
  rw [middle_eq_difference]
  exact difference_summable (ToeplitzHankelTraceConstants.M_sub_T_summable (generator_weighted hV))
    (ConjugationTrace.D_summable hV0 hV s)

theorem row_conjugatedQ {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    RowBound (conjugatedQ V s)
      ((weightedMass (positiveExponential V s)*weightedMass (flip (lift V)))*
        weightedMass (positiveExponential V (-s))) :=
  rowBound_product (rowBound_product (row_L hV0 hV s) (row_Q hV)) (row_L hV0 hV (-s))

theorem U_Q_commute {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) : product (U V s) (Q V)=product (Q V) (U V s) := by
  have hu := weighted_flip (positive_weighted hV0 hV s)
  have hq := weighted_flip (weighted_lift hV)
  change product (T (flip (positiveExponential V s))) (T (flip (lift V)))=
    product (T (flip (lift V))) (T (flip (positiveExponential V s)))
  rw [← T_convolution_of_left_nonpositive (summable_abs hu) (summable_abs hq)
    (flip_nonnegative (positive_support V s)),convolution_comm,
    T_convolution_of_left_nonpositive (summable_abs hq) (summable_abs hu)
      (flip_nonnegative (lift_nonnegative V))]

/-- Cancellation of the two actual upper factors leaves the lower conjugate. -/
theorem Ninv_Q_N {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    product (product (Ninv V s) (Q V)) (N V s)=conjugatedQ V s := by
  rw [Ninv,N_factor hV0 hV,
    BoundedKernelAlgebra.product_assoc (row_L hV0 hV s) (row_U hV0 hV s) (row_Q hV),
    U_Q_commute hV0 hV s,
    ← BoundedKernelAlgebra.product_assoc (row_L hV0 hV s) (row_Q hV) (row_U hV0 hV s),
    BoundedKernelAlgebra.product_assoc (rowBound_product (row_L hV0 hV s) (row_Q hV))
      (row_U hV0 hV s) (rowBound_product (row_U hV0 hV (-s)) (row_L hV0 hV (-s))),
    ← BoundedKernelAlgebra.product_assoc (row_U hV0 hV s) (row_U hV0 hV (-s)) (row_L hV0 hV (-s)),
    U_inverse hV0 s,NormalizedExponentialInverse.unit_left]
  rfl

private theorem inverse_N_product {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) {X : Kernel} {c : ℝ} (hX : RowBound X c) :
    product (inverse V s) (product (product (N V s) X) (W V s))=
      product (product (W V (-s)) X) (W V s) := by
  rw [inverse,
    BoundedKernelAlgebra.product_assoc (row_W hV0 hV (-s)) (row_Ninv hV0 hV s)
      (rowBound_product (rowBound_product (row_N hV0 hV s) hX) (row_W hV0 hV s)),
    ← BoundedKernelAlgebra.product_assoc (row_Ninv hV0 hV s) (rowBound_product (row_N hV0 hV s) hX)
      (row_W hV0 hV s),
    ← BoundedKernelAlgebra.product_assoc (row_Ninv hV0 hV s) (row_N hV0 hV s) hX,
    N_left_inverse hV0 hV s,NormalizedExponentialInverse.unit_left,
    ← BoundedKernelAlgebra.product_assoc (row_W hV0 hV (-s)) hX (row_W hV0 hV s)]

private theorem inverse_Q_product {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    product (inverse V s) (product (product (Q V) (N V s)) (W V s))=
      product (product (W V (-s)) (conjugatedQ V s)) (W V s) := by
  rw [inverse,
    BoundedKernelAlgebra.product_assoc (row_W hV0 hV (-s)) (row_Ninv hV0 hV s)
      (rowBound_product (rowBound_product (row_Q hV) (row_N hV0 hV s)) (row_W hV0 hV s)),
    ← BoundedKernelAlgebra.product_assoc (row_Ninv hV0 hV s) (rowBound_product (row_Q hV) (row_N hV0 hV s))
      (row_W hV0 hV s),
    ← BoundedKernelAlgebra.product_assoc (row_Ninv hV0 hV s) (row_Q hV) (row_N hV0 hV s),
    Ninv_Q_N hV0 hV s,
    ← BoundedKernelAlgebra.product_assoc (row_W hV0 hV (-s)) (row_conjugatedQ hV0 hV s) (row_W hV0 hV s)]

/-- Actual inverse times actual derivative is a bounded conjugate of one
entrywise summable middle kernel. -/
theorem inverse_direction_eq {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    product (inverse V s) (direction V s)=
      product (product (W V (-s)) (middle V s)) (W V s) := by
  have rN := row_N hV0 hV s
  have rW := row_W hV0 hV s
  have rWi := row_W hV0 hV (-s)
  have rI := row_inverse hV0 hV s
  have rP := row_P hV
  have rQ := row_Q hV
  have rB := row_B hV
  have rConj := row_conjugatedQ hV0 hV s
  have hd : direction V s=product (product (N V s) (B V)) (W V s)-
      (product (product (N V s) (P V)) (W V s)+product (product (Q V) (N V s)) (W V s)) := by
    rw [direction_eq_factored hV0 hV s]
    abel
  rw [hd,BoundedKernelLinear.product_sub_right rI (rowBound_product (rowBound_product rN rB) rW)
    (BoundedKernelLinear.rowBound_add (rowBound_product (rowBound_product rN rP) rW)
      (rowBound_product (rowBound_product rQ rN) rW)),
    BoundedKernelLinear.product_add_right rI (rowBound_product (rowBound_product rN rP) rW)
      (rowBound_product (rowBound_product rQ rN) rW),
    inverse_N_product hV0 hV s rB,inverse_N_product hV0 hV s rP,inverse_Q_product hV0 hV s]
  unfold middle
  rw [BoundedKernelLinear.product_sub_right rWi (BoundedKernelLinear.rowBound_sub rB rP) rConj,
    BoundedKernelLinear.product_sub_right rWi rB rP,
    BoundedKernelLinear.product_sub_left
      (BoundedKernelLinear.rowBound_sub (rowBound_product rWi rB) (rowBound_product rWi rP))
      (rowBound_product rWi rConj) rW,
    BoundedKernelLinear.product_sub_left (rowBound_product rWi rB) (rowBound_product rWi rP) rW]
  abel

theorem relativeDirection_eq_inverse_product {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    NormalizedExponentialPath.relativeDirection V s=product (inverse V s) (direction V s) := by
  have rd := rowBound_of_summable (direction_summable hV0 hV s)
  unfold NormalizedExponentialPath.relativeDirection
  rw [inversePerturbation_eq hV0 hV s,
    BoundedKernelLinear.product_sub_left (row_inverse hV0 hV s) (rowBound_T_weighted weighted_unit) rd,
    NormalizedExponentialInverse.unit_left]
  abel

/-- The requested trace reduction contains only two proved summable kernels. -/
theorem relative_trace_eq {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    trace (NormalizedExponentialPath.relativeDirection V s)=
      trace (M (evenGenerator V)-T (evenGenerator V))-trace (ConjugationTrace.D V s) := by
  rw [relativeDirection_eq_inverse_product hV0 hV s,inverse_direction_eq hV0 hV s,
    trace_conjugation (row_W hV0 hV (-s)) (row_W hV0 hV s)
      (middle_summable hV0 hV s) (W_inverse hV0 hV s),middle_eq_difference]
  exact trace_sub (ToeplitzHankelTraceConstants.M_sub_T_summable (generator_weighted hV))
    (ConjugationTrace.D_summable hV0 hV s)

/-- The actual log-determinant derivative is affine in the deformation
parameter, after the actual conjugation trace has been evaluated. -/
theorem hasDerivAt_log_affine {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    HasDerivAt (fun t => Real.log (determinant V hV0 hV t))
      (trace (M (evenGenerator V)-T (evenGenerator V))+
        trace (product (H (lift V)) (H (lift V)))*s) s := by
  have hd := hasDerivAt_log_determinant hV0 hV s
  rw [relative_trace_eq hV0 hV s,ConjugationTrace.trace_D hV0 hV s] at hd
  convert hd using 1
  ring

end
end SpanningTreeIsoperimetry.NormalizedLogDerivativeTrace
