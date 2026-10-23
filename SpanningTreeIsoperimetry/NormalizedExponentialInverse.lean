module

public import SpanningTreeIsoperimetry.OneSidedLaurentCompatibility
public import SpanningTreeIsoperimetry.NormalizedToeplitzFactorization

@[expose] public section

/-! Explicit bounded two-sided inverse of the actual normalized even
exponential kernel. All factors and cancellations use their actual sums. -/
namespace SpanningTreeIsoperimetry.NormalizedExponentialInverse
open OneSidedLaurentCompatibility OneSidedToeplitz OneSidedLaurentKernels
open ToeplitzHankelKernels ToeplitzHankelConvolution LaurentConvolutionAlgebra
open LaurentWeightedConvolution ToeplitzHankelMassBounds WeightedPowerSeries
open SummableKernelProduct BoundedKernelProduct BoundedKernelAlgebra
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev identity : Kernel := T unitCoeff

def L (V : PowerSeries ℝ) (t : ℝ) : Kernel := T (positiveExponential V t)
def U (V : PowerSeries ℝ) (t : ℝ) : Kernel := T (flip (positiveExponential V t))
def W (V : PowerSeries ℝ) (t : ℝ) : Kernel := M (evenExponential V t)
def N (V : PowerSeries ℝ) (t : ℝ) : Kernel := T (evenExponential V (-t))
def Ninv (V : PowerSeries ℝ) (t : ℝ) : Kernel := product (L V t) (U V t)
def C (V : PowerSeries ℝ) (t : ℝ) : Kernel :=
  NormalizedToeplitzFactorization.C (positiveExponential V t) (positiveExponential V (-t))
def inverse (V : PowerSeries ℝ) (t : ℝ) : Kernel := product (W V (-t)) (Ninv V t)

theorem C_eq (V : PowerSeries ℝ) (t : ℝ) : C V t=product (N V t) (W V t) := rfl

theorem unit_left (A : Kernel) : product identity A=A := by
  ext i j
  simp [product,T_unit_apply]

theorem unit_right (A : Kernel) : product A identity=A := by
  ext i j
  simp [product,T_unit_apply]

theorem columnBound_product {A B : Kernel} {a b : ℝ}
    (hA : ColumnBound A a) (hB : ColumnBound B b) : ColumnBound (product A B) (a*b) := by
  change RowBound (transpose (product A B)) (a*b)
  rw [transpose_product]
  simpa only [mul_comm] using rowBound_product hB hA

theorem row_L {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (hV : SummableWeighted V) (t : ℝ) :
    RowBound (L V t) (weightedMass (positiveExponential V t)) :=
  rowBound_T_weighted (positive_weighted hV0 hV t)

theorem column_L {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (hV : SummableWeighted V) (t : ℝ) :
    ColumnBound (L V t) (weightedMass (positiveExponential V t)) :=
  columnBound_T_weighted (positive_weighted hV0 hV t)

theorem row_U {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (hV : SummableWeighted V) (t : ℝ) :
    RowBound (U V t) (weightedMass (flip (positiveExponential V t))) :=
  rowBound_T_weighted (weighted_flip (positive_weighted hV0 hV t))

theorem column_U {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (hV : SummableWeighted V) (t : ℝ) :
    ColumnBound (U V t) (weightedMass (flip (positiveExponential V t))) :=
  columnBound_T_weighted (weighted_flip (positive_weighted hV0 hV t))

theorem row_W {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (hV : SummableWeighted V) (t : ℝ) :
    RowBound (W V t) (2*weightedMass (evenExponential V t)) :=
  rowBound_M_weighted (even_weighted hV0 hV t)

theorem column_W {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (hV : SummableWeighted V) (t : ℝ) :
    ColumnBound (W V t) (2*weightedMass (evenExponential V t)) :=
  columnBound_M_weighted (even_weighted hV0 hV t)

theorem row_N {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (hV : SummableWeighted V) (t : ℝ) :
    RowBound (N V t) (weightedMass (evenExponential V (-t))) :=
  rowBound_T_weighted (even_weighted hV0 hV (-t))

theorem row_Ninv {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (hV : SummableWeighted V) (t : ℝ) :
    RowBound (Ninv V t)
      (weightedMass (positiveExponential V t)*weightedMass (flip (positiveExponential V t))) :=
  rowBound_product (row_L hV0 hV t) (row_U hV0 hV t)

def inverseBound (V : PowerSeries ℝ) (t : ℝ) : ℝ :=
  (2*weightedMass (evenExponential V (-t)))*
    (weightedMass (positiveExponential V t)*weightedMass (flip (positiveExponential V t)))

theorem row_inverse {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (hV : SummableWeighted V) (t : ℝ) :
    RowBound (inverse V t) (inverseBound V t) :=
  rowBound_product (row_W hV0 hV (-t)) (row_Ninv hV0 hV t)

theorem column_inverse {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (hV : SummableWeighted V) (t : ℝ) :
    ColumnBound (inverse V t) (inverseBound V t) :=
  columnBound_product (column_W hV0 hV (-t))
    (columnBound_product (column_L hV0 hV t) (column_U hV0 hV t))

theorem row_C {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (hV : SummableWeighted V) (t : ℝ) :
    RowBound (C V t)
      (weightedMass (evenExponential V (-t))*(2*weightedMass (evenExponential V t))) :=
  rowBound_product (row_N hV0 hV t) (row_W hV0 hV t)

theorem L_inverse {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (t : ℝ) :
    product (L V t) (L V (-t))=identity := by
  unfold L positiveExponential
  rw [T_lift,T_lift,lower_exponential_inverse hV0]
  ext i j
  simp only [OneSidedToeplitz.identity,T_unit_apply]

theorem U_inverse {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (t : ℝ) :
    product (U V t) (U V (-t))=identity := by
  unfold U positiveExponential
  rw [T_flip,T_flip,T_lift,T_lift]
  change product (upper (PositiveFrequencyExponential.exponential V t))
    (upper (PositiveFrequencyExponential.exponential V (-t)))=identity
  rw [upper_exponential_inverse hV0]
  ext i j
  simp only [OneSidedToeplitz.identity,T_unit_apply]

theorem W_inverse {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (hV : SummableWeighted V) (t : ℝ) :
    product (W V t) (W V (-t))=identity := by
  ext i j
  exact (M_inverse (even_weighted hV0 hV t) (even_weighted hV0 hV (-t))
    (even_even V (-t)) (even_inverse hV0 hV t) i j).trans (T_unit_apply i j).symm

theorem N_factor {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0) (hV : SummableWeighted V) (t : ℝ) :
    N V t=product (U V (-t)) (L V (-t)) :=
  NormalizedToeplitzFactorization.T_symbol_factor (positive_weighted hV0 hV (-t)) (positive_support V (-t))

private theorem paired_inverse {A B Ai Bi : Kernel} {a b ai bi : ℝ}
    (hA : RowBound A a) (hB : RowBound B b) (hAi : RowBound Ai ai) (hBi : RowBound Bi bi)
    (hAA : product A Ai=identity) (hBB : product B Bi=identity) :
    product (product A B) (product Bi Ai)=identity := by
  rw [BoundedKernelAlgebra.product_assoc hA hB (rowBound_product hBi hAi),
    ← BoundedKernelAlgebra.product_assoc hB hBi hAi,hBB,unit_left,hAA]

theorem N_right_inverse {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (t : ℝ) : product (N V t) (Ninv V t)=identity := by
  rw [N_factor hV0 hV,Ninv]
  apply paired_inverse (row_U hV0 hV (-t)) (row_L hV0 hV (-t))
    (row_U hV0 hV t) (row_L hV0 hV t)
  · simpa only [neg_neg] using U_inverse hV0 (-t)
  · simpa only [neg_neg] using L_inverse hV0 (-t)

theorem N_left_inverse {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (t : ℝ) : product (Ninv V t) (N V t)=identity := by
  rw [N_factor hV0 hV,Ninv]
  exact paired_inverse (row_L hV0 hV t) (row_U hV0 hV t)
    (row_L hV0 hV (-t)) (row_U hV0 hV (-t)) (L_inverse hV0 t) (U_inverse hV0 t)

/-- The inverse order is W(-t), then L(t), then U(t). -/
theorem right_inverse {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (t : ℝ) : product (C V t) (inverse V t)=identity := by
  rw [C_eq,inverse]
  exact paired_inverse (row_N hV0 hV t) (row_W hV0 hV t)
    (row_Ninv hV0 hV t) (row_W hV0 hV (-t))
    (N_right_inverse hV0 hV t) (W_inverse hV0 hV t)

theorem left_inverse {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (t : ℝ) : product (inverse V t) (C V t)=identity := by
  rw [C_eq,inverse]
  apply paired_inverse (row_W hV0 hV (-t)) (row_Ninv hV0 hV t)
    (row_W hV0 hV t) (row_N hV0 hV t)
  · simpa only [neg_neg] using W_inverse hV0 hV (-t)
  · exact N_left_inverse hV0 hV t

end
end SpanningTreeIsoperimetry.NormalizedExponentialInverse
