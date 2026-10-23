module

public import SpanningTreeIsoperimetry.OneSidedLaurentKernels
public import SpanningTreeIsoperimetry.ToeplitzHankelMassBounds
public import SpanningTreeIsoperimetry.BoundedKernelAlgebra
public import SpanningTreeIsoperimetry.BoundedKernelSylvester

@[expose] public section

/-! Exact normalized Toeplitz-minus-Hankel factorization. The two actual
normalizations differ by the order of one summable remainder and one
bounded triangular factor, so the checked Sylvester theorem identifies
their finite-section determinant limits. -/
namespace SpanningTreeIsoperimetry.NormalizedToeplitzFactorization
open ToeplitzHankelKernels ToeplitzHankelConvolution LaurentWeightedConvolution
open LaurentConvolutionAlgebra OneSidedLaurentKernels ToeplitzHankelMassBounds
open SummableKernelProduct AbsolutelySummableDeterminant BoundedKernelProduct
open BoundedKernelAlgebra SummableKernelDeterminant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def symbol (a : Laurent) : Laurent := convolution a (flip a)
def K (a : Laurent) : Kernel := product (H a) (H a)-Hshift (symbol a)
def R (a c : Laurent) : Kernel := product (T c) (K a)
def F (a c : Laurent) : Kernel := product (product (T c) (M (symbol a))) (T (flip c))
def C (a c : Laurent) : Kernel := product (T (symbol c)) (M (symbol a))

private theorem kernel_sub_summable {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) : Summable (entryNorm (A-B)) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ (hA.add hB)
  intro p
  change |A p.1 p.2-B p.1 p.2|≤|A p.1 p.2|+|B p.1 p.2|
  simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (A p.1 p.2) (-B p.1 p.2)

private theorem rowBound_of_summable {A : Kernel} (hA : Summable (entryNorm A)) :
    RowBound A (totalMass A) := by
  refine ⟨totalMass_nonneg A,row_summable hA,?_⟩
  intro i
  exact tsum_comp_le_tsum_of_inj hA (fun _ => abs_nonneg _)
    (show Function.Injective (fun j : ℕ => (i,j)) by intro j k h; exact congrArg Prod.snd h)

private theorem entry_summable {A B : Kernel} {c d : ℝ} (hA : RowBound A c) (hB : RowBound B d)
    (i j : ℕ) : Summable (fun k => A i k*B k j) := by
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs] using BoundedKernelAlgebra.entry_product_summable hA hB i j

private theorem product_add_left {A B D : Kernel} {a b d : ℝ}
    (hA : RowBound A a) (hB : RowBound B b) (hD : RowBound D d) :
    product (A+B) D=product A D+product B D := by
  ext i j
  simp only [product,Pi.add_apply,add_mul]
  exact (entry_summable hA hD i j).tsum_add (entry_summable hB hD i j)

private theorem product_add_right {A B D : Kernel} {a b d : ℝ}
    (hA : RowBound A a) (hB : RowBound B b) (hD : RowBound D d) :
    product A (B+D)=product A B+product A D := by
  ext i j
  simp only [product,Pi.add_apply,mul_add]
  exact (entry_summable hA hB i j).tsum_add (entry_summable hA hD i j)

private theorem product_unit_left (A : Kernel) : product (T unitCoeff) A=A := by
  ext i j
  simp [product,T_unit_apply]

private theorem product_unit_right (A : Kernel) : product A (T unitCoeff)=A := by
  ext i j
  simp [product,T_unit_apply]

theorem symbol_weighted {a : Laurent} (ha : WeightedSummable a) : WeightedSummable (symbol a) :=
  weighted_convolution ha (weighted_flip ha)

theorem symbol_even (a : Laurent) : Function.Even (symbol a) := convolution_flip_even a

theorem K_summable {a : Laurent} (ha : WeightedSummable a) : Summable (entryNorm (K a)) :=
  kernel_sub_summable (product_summable (H_summable ha) (H_summable ha))
    (Hshift_summable (symbol_weighted ha))

theorem R_summable {a c : Laurent} (ha : WeightedSummable a) (hc : WeightedSummable c) :
    Summable (entryNorm (R a c)) :=
  left_summable (columnBound_T_weighted hc) (K_summable ha)

theorem M_decomposition {a : Laurent} (ha : WeightedSummable a) :
    M (symbol a)=product (T a) (T (flip a))+K a := by
  unfold M symbol
  rw [toeplitz_convolution_weighted ha (weighted_flip ha),LaurentConvolutionAlgebra.flip_flip]
  unfold K symbol
  abel

theorem T_symbol_factor {c : Laurent} (hc : WeightedSummable c) (hcs : NonnegativeSupport c) :
    T (symbol c)=product (T (flip c)) (T c) := by
  unfold symbol
  rw [convolution_comm]
  exact T_convolution_of_left_nonpositive (summable_abs (weighted_flip hc)) (summable_abs hc)
    (flip_nonnegative hcs)

private theorem lower_inverse {a c : Laurent} (ha : WeightedSummable a) (hc : WeightedSummable c)
    (has : NonnegativeSupport a) (hinv : convolution a c=unitCoeff) :
    product (T c) (T a)=T unitCoeff := by
  rw [← T_convolution_of_right_nonnegative (summable_abs hc) (summable_abs ha) has,
    convolution_comm c a,hinv]

private theorem upper_inverse {a c : Laurent} (ha : WeightedSummable a) (hc : WeightedSummable c)
    (has : NonnegativeSupport a) (hinv : convolution a c=unitCoeff) :
    product (T (flip a)) (T (flip c))=T unitCoeff := by
  rw [← T_convolution_of_left_nonpositive (summable_abs (weighted_flip ha))
    (summable_abs (weighted_flip hc)) (flip_nonnegative has),← flip_convolution,hinv,flip_unit]

theorem left_normalized {a c : Laurent} (ha : WeightedSummable a) (hc : WeightedSummable c)
    (has : NonnegativeSupport a) (hinv : convolution a c=unitCoeff) :
    product (T c) (M (symbol a))=T (flip a)+R a c := by
  rw [M_decomposition ha,
    product_add_right (rowBound_T_weighted hc)
      (rowBound_product (rowBound_T_weighted ha) (rowBound_T_weighted (weighted_flip ha)))
      (rowBound_of_summable (K_summable ha)),
    ← BoundedKernelAlgebra.product_assoc (rowBound_T_weighted hc) (rowBound_T_weighted ha)
      (rowBound_T_weighted (weighted_flip ha)),lower_inverse ha hc has hinv,product_unit_left]
  rfl

/-- The normalized finite-section sandwich has a summable right-factor
perturbation of the genuine Kronecker identity. -/
theorem F_difference {a c : Laurent} (ha : WeightedSummable a) (hc : WeightedSummable c)
    (has : NonnegativeSupport a) (hinv : convolution a c=unitCoeff) :
    F a c-T unitCoeff=product (R a c) (T (flip c)) := by
  unfold F
  rw [left_normalized ha hc has hinv,
    product_add_left (rowBound_T_weighted (weighted_flip ha))
      (rowBound_of_summable (R_summable ha hc)) (rowBound_T_weighted (weighted_flip hc)),
    upper_inverse ha hc has hinv]
  abel

/-- The inverse-symbol normalization is the reversed Sylvester product. -/
theorem C_difference {a c : Laurent} (ha : WeightedSummable a) (hc : WeightedSummable c)
    (has : NonnegativeSupport a) (hcs : NonnegativeSupport c) (hinv : convolution a c=unitCoeff) :
    C a c-T unitCoeff=product (T (flip c)) (R a c) := by
  have hinv' : convolution c a=unitCoeff := by rw [convolution_comm,hinv]
  unfold C
  rw [T_symbol_factor hc hcs,
    BoundedKernelAlgebra.product_assoc (rowBound_T_weighted (weighted_flip hc)) (rowBound_T_weighted hc)
      (rowBound_M_weighted (symbol_weighted ha)),
    left_normalized ha hc has hinv,
    product_add_right (rowBound_T_weighted (weighted_flip hc)) (rowBound_T_weighted (weighted_flip ha))
      (rowBound_of_summable (R_summable ha hc)),upper_inverse hc ha hcs hinv']
  abel

theorem F_difference_summable {a c : Laurent} (ha : WeightedSummable a) (hc : WeightedSummable c)
    (has : NonnegativeSupport a) (hinv : convolution a c=unitCoeff) :
    Summable (entryNorm (F a c-T unitCoeff)) := by
  rw [F_difference ha hc has hinv]
  exact right_summable (R_summable ha hc) (rowBound_T_weighted (weighted_flip hc))

theorem C_difference_summable {a c : Laurent} (ha : WeightedSummable a) (hc : WeightedSummable c)
    (has : NonnegativeSupport a) (hcs : NonnegativeSupport c) (hinv : convolution a c=unitCoeff) :
    Summable (entryNorm (C a c-T unitCoeff)) := by
  rw [C_difference ha hc has hcs hinv]
  exact left_summable (columnBound_T_weighted (weighted_flip hc)) (R_summable ha hc)

/-- Equality of actual finite-section determinant limits, obtained from
the already proved concrete Sylvester identity. -/
theorem determinant_normalization {a c : Laurent} (ha : WeightedSummable a) (hc : WeightedSummable c)
    (has : NonnegativeSupport a) (hcs : NonnegativeSupport c) (hinv : convolution a c=unitCoeff) :
    detLimit (F a c-T unitCoeff) (F_difference_summable ha hc has hinv)=
      detLimit (C a c-T unitCoeff) (C_difference_summable ha hc has hcs hinv) := by
  have hr := R_summable ha hc
  have hu := rowBound_T_weighted (weighted_flip hc)
  have huc := columnBound_T_weighted (weighted_flip hc)
  exact (detLimit_congr (F_difference_summable ha hc has hinv) (right_summable hr hu)
    (F_difference ha hc has hinv)).trans
      ((BoundedKernelSylvester.determinant_sylvester hr hu huc).trans
        (detLimit_congr (left_summable huc hr) (C_difference_summable ha hc has hcs hinv)
          (C_difference ha hc has hcs hinv).symm))

end
end SpanningTreeIsoperimetry.NormalizedToeplitzFactorization
