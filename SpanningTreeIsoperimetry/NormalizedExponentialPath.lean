module

public import SpanningTreeIsoperimetry.EvenExponentialSignedPath
public import SpanningTreeIsoperimetry.WeightedKernelProductPath
public import SpanningTreeIsoperimetry.NormalizedExponentialNonzero
public import SpanningTreeIsoperimetry.SummableDeterminantPath

@[expose] public section

/-! Actual mass differentiation of the normalized exponential perturbation.
The proof uses its two summable Toeplitz/Hankel product terms, then the checked
explicit inverse to differentiate the actual determinant limit. -/
namespace SpanningTreeIsoperimetry.NormalizedExponentialPath
open OneSidedLaurentCompatibility EvenExponentialSignedPath NormalizedExponentialInverse
open NormalizedExponentialNonzero ToeplitzHankelKernels ToeplitzHankelConvolution
open LaurentConvolutionAlgebra LaurentWeightedConvolution ToeplitzHankelMassBounds
open WeightedPowerSeries SummableKernelProduct SummableKernelAlgebra BoundedKernelProduct
open SummableKernelDeterminant SummableDeterminantFirstOrder SummableDeterminantAffine
open SummableDeterminantContinuity SummableDeterminantPath SummableKernelTrace
open AbsolutelySummableDeterminant WeightedKernelProductPath Filter Asymptotics
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def thPart (V : PowerSeries ℝ) (s : ℝ) : Kernel :=
  product (T (evenExponential V (-s))) (Hshift (evenExponential V s))
def hhPart (V : PowerSeries ℝ) (s : ℝ) : Kernel :=
  product (H (evenExponential V (-s))) (H (evenExponential V s))
def thDirection (V : PowerSeries ℝ) (s : ℝ) : Kernel :=
  product (T (negativeDirection V s)) (Hshift (evenExponential V s))+
    product (T (evenExponential V (-s))) (Hshift (positiveDirection V s))
def hhDirection (V : PowerSeries ℝ) (s : ℝ) : Kernel :=
  product (H (negativeDirection V s)) (H (evenExponential V s))+
    product (H (evenExponential V (-s))) (H (positiveDirection V s))
def direction (V : PowerSeries ℝ) (s : ℝ) : Kernel := -thDirection V s-hhDirection V s

private theorem neg_summable {A : Kernel} (hA : Summable (entryNorm A)) :
    Summable (entryNorm (-A)) := by
  change Summable (fun p : ℕ×ℕ => |A p.1 p.2|) at hA
  change Summable (fun p : ℕ×ℕ => |-A p.1 p.2|)
  simpa only [abs_neg] using hA

private theorem mass_neg (A : Kernel) : totalMass (-A)=totalMass A := by
  apply tsum_congr
  intro p
  exact abs_neg (A p.1 p.2)

private theorem mass_neg_sub_le {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) : totalMass (-A-B)≤totalMass A+totalMass B := by
  rw [show -A-B= -(A+B) by abel,mass_neg]
  exact mass_add_le hA hB

private theorem product_sub_right_rows {A B D : Kernel} {a b d : ℝ}
    (hA : RowBound A a) (hB : RowBound B b) (hD : RowBound D d) :
    product A (B-D)=product A B-product A D := by
  ext i j
  simp only [product,Pi.sub_apply,mul_sub]
  exact ((BoundedKernelAlgebra.entry_product_summable hA hB i j).of_abs).tsum_sub
    ((BoundedKernelAlgebra.entry_product_summable hA hD i j).of_abs)

/-- The actual C-I is a sum of two entrywise summable product terms. -/
theorem perturbation_eq_parts {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) : perturbation V s= -thPart V s-hhPart V s := by
  have hm := even_weighted hV0 hV (-s)
  have hp := even_weighted hV0 hV s
  have hf : flip (evenExponential V s)=evenExponential V s :=
    (flip_eq_iff_even _).mpr (even_even V s)
  have hi : convolution (evenExponential V (-s)) (evenExponential V s)=unitCoeff := by
    simpa only [neg_neg] using even_inverse hV0 hV (-s)
  have ht := toeplitz_convolution_weighted hm hp
  rw [hf,hi] at ht
  have htt : product (T (evenExponential V (-s))) (T (evenExponential V s))=
      identity-product (H (evenExponential V (-s))) (H (evenExponential V s)) :=
    eq_sub_iff_add_eq.mpr ht.symm
  rw [perturbation,C_eq]
  change product (T (evenExponential V (-s))) (M (evenExponential V s))-identity=_
  rw [M,Hshift,product_sub_right_rows (rowBound_T_weighted hm) (rowBound_T_weighted hp)
    (rowBound_hankelOffset_weighted hp 2),htt]
  unfold thPart hhPart
  abel

theorem thPart_summable {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) : Summable (entryNorm (thPart V s)) := by
  unfold thPart
  exact left_summable (columnBound_T_weighted (even_weighted hV0 hV (-s)))
    (Hshift_summable (even_weighted hV0 hV s))

theorem hhPart_summable {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) : Summable (entryNorm (hhPart V s)) := by
  unfold hhPart
  exact product_summable (H_summable (even_weighted hV0 hV (-s)))
    (H_summable (even_weighted hV0 hV s))

theorem thDirection_summable {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) : Summable (entryNorm (thDirection V s)) := by
  unfold thDirection
  exact add_summable
    (left_summable (columnBound_T_weighted (negativeDirection_weighted hV0 hV s))
      (Hshift_summable (even_weighted hV0 hV s)))
    (left_summable (columnBound_T_weighted (even_weighted hV0 hV (-s)))
      (Hshift_summable (positiveDirection_weighted hV0 hV s)))

theorem hhDirection_summable {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) : Summable (entryNorm (hhDirection V s)) := by
  unfold hhDirection
  exact add_summable
    (product_summable (H_summable (negativeDirection_weighted hV0 hV s))
      (H_summable (even_weighted hV0 hV s)))
    (product_summable (H_summable (even_weighted hV0 hV (-s)))
      (H_summable (positiveDirection_weighted hV0 hV s)))

theorem direction_summable {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) : Summable (entryNorm (direction V s)) :=
  difference_summable (neg_summable (thDirection_summable hV0 hV s)) (hhDirection_summable hV0 hV s)

theorem thPart_remainder {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    (fun t : ℝ => totalMass (thPart V (s+t)-thPart V s-t • thDirection V s)) =o[𝓝 0] fun t => t := by
  have h := toeplitz_hankel_remainder_isLittleO 2
    (fun t => even_weighted hV0 hV (-(s+t))) (fun t => even_weighted hV0 hV (s+t))
    (negativeDirection_weighted hV0 hV s) (positiveDirection_weighted hV0 hV s)
    (by simpa only [add_zero] using negative_remainder hV0 hV s)
    (by simpa only [add_zero] using positive_remainder hV0 hV s)
  simpa only [thPart,thDirection,Hshift,add_zero] using h

theorem hhPart_remainder {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    (fun t : ℝ => totalMass (hhPart V (s+t)-hhPart V s-t • hhDirection V s)) =o[𝓝 0] fun t => t := by
  have h := hankel_hankel_remainder_isLittleO 1 1
    (fun t => even_weighted hV0 hV (-(s+t))) (fun t => even_weighted hV0 hV (s+t))
    (negativeDirection_weighted hV0 hV s) (positiveDirection_weighted hV0 hV s)
    (by simpa only [add_zero] using negative_remainder hV0 hV s)
    (by simpa only [add_zero] using positive_remainder hV0 hV s)
  simpa only [hhPart,hhDirection,H,add_zero] using h

/-- Actual total-entry-mass differentiability of C(s+t)-I. -/
theorem perturbation_remainder_isLittleO {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    (fun t : ℝ => totalMass (perturbation V (s+t)-perturbation V s-t • direction V s))
      =o[𝓝 0] fun t => t := by
  let rT : ℝ → Kernel := fun t => thPart V (s+t)-thPart V s-t • thDirection V s
  let rH : ℝ → Kernel := fun t => hhPart V (s+t)-hhPart V s-t • hhDirection V s
  have hrT (t : ℝ) : Summable (entryNorm (rT t)) :=
    difference_summable (difference_summable (thPart_summable hV0 hV (s+t))
      (thPart_summable hV0 hV s)) (scale_summable t (thDirection_summable hV0 hV s))
  have hrH (t : ℝ) : Summable (entryNorm (rH t)) :=
    difference_summable (difference_summable (hhPart_summable hV0 hV (s+t))
      (hhPart_summable hV0 hV s)) (scale_summable t (hhDirection_summable hV0 hV s))
  have he (t : ℝ) : perturbation V (s+t)-perturbation V s-t • direction V s= -rT t-rH t := by
    rw [perturbation_eq_parts hV0 hV (s+t),perturbation_eq_parts hV0 hV s]
    dsimp only [rT,rH,direction]
    simp only [smul_sub,smul_neg]
    abel
  have hbig : (fun t => totalMass (perturbation V (s+t)-perturbation V s-t • direction V s))
      =O[𝓝 0] (fun t => totalMass (rT t)+totalMass (rH t)) := by
    apply isBigO_iff.mpr
    refine ⟨1,Eventually.of_forall (fun t => ?_)⟩
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (totalMass_nonneg _),
      abs_of_nonneg (add_nonneg (totalMass_nonneg _) (totalMass_nonneg _)),one_mul,he]
    exact mass_neg_sub_le (hrT t) (hrH t)
  exact hbig.trans_isLittleO ((thPart_remainder hV0 hV s).add (hhPart_remainder hV0 hV s))

def determinant (V : PowerSeries ℝ) (hV0 : V.constantCoeff=0) (hV : SummableWeighted V) (s : ℝ) : ℝ :=
  detLimit (perturbation V s) (perturbation_summable hV0 hV s)

def relativeDirection (V : PowerSeries ℝ) (s : ℝ) : Kernel :=
  direction V s+product (inversePerturbation V s) (direction V s)

/-- Derivative of the actual normalized determinant, using the explicit
summable inverse perturbation. -/
theorem hasDerivAt_determinant {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    HasDerivAt (determinant V hV0 hV)
      (determinant V hV0 hV s*trace (relativeDirection V s)) s := by
  let K : ℝ → Kernel := fun t => perturbation V (s+t)
  have hK (t : ℝ) : Summable (entryNorm (K t)) := perturbation_summable hV0 hV (s+t)
  have hrem : (fun t => totalMass (K t-affine (K 0) (direction V s) t)) =o[𝓝 0] fun t => t := by
    have he (t : ℝ) : K t-affine (K 0) (direction V s) t=
        perturbation V (s+t)-perturbation V s-t • direction V s := by
      change perturbation V (s+t)-(perturbation V (s+0)+t • direction V s)=_
      rw [add_zero]
      abel
    simpa only [he] using perturbation_remainder_isLittleO hV0 hV s
  have hinv : composePerturbation (K 0) (inversePerturbation V s)=0 := by
    simpa only [K,add_zero] using compose_inverse hV0 hV s
  have hd := SummableDeterminantPath.hasDerivAt_path_zero hK
    (inversePerturbation_summable hV0 hV s) (direction_summable hV0 hV s) hinv hrem
  apply hasDerivAt_iff_isLittleO_nhds_zero.mpr
  simpa only [pathDeterminant,K,add_zero,sub_zero,determinant,relativeDirection,
    SummableDeterminantAffine.relativeDirection] using hd.isLittleO

/-- No trace of a nonsummable Toeplitz factor occurs in this logarithmic
formula: the relative direction is an actual summable kernel. -/
theorem hasDerivAt_log_determinant {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (s : ℝ) :
    HasDerivAt (fun t => Real.log (determinant V hV0 hV t)) (trace (relativeDirection V s)) s := by
  have hn := determinant_ne_zero hV0 hV s
  have hd := (hasDerivAt_determinant hV0 hV s).log hn
  convert hd using 1
  change _=(_* _)/detLimit (perturbation V s) (perturbation_summable hV0 hV s)
  unfold determinant
  field_simp

end
end SpanningTreeIsoperimetry.NormalizedExponentialPath
