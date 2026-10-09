import SpanningTreeIsoperimetry.WeightedExponentialRemainder
import SpanningTreeIsoperimetry.BoundedKernelProduct
import SpanningTreeIsoperimetry.TriangularCompression
import SpanningTreeIsoperimetry.ToeplitzHankelKernels

/-! One-sided formal coefficients give actual triangular kernels. Their
multiplication is finite at every entry; weighted bounds control all rows
and columns of the exponential factors. -/
namespace SpanningTreeIsoperimetry.OneSidedToeplitz
open PositiveFrequencyExponential WeightedPowerSeries WeightedExponentialRemainder
open SummableKernelProduct BoundedKernelProduct
open scoped BigOperators
noncomputable section

def lower (p : PowerSeries ℝ) : Kernel := fun i j => if j ≤ i then PowerSeries.coeff (i-j) p else 0
def upper (p : PowerSeries ℝ) : Kernel := transpose (lower p)
def identity : Kernel := fun i j => if i=j then 1 else 0

theorem lower_triangular (p : PowerSeries ℝ) : TriangularCompression.Lower (lower p) := by
  intro i j hij
  exact if_neg (by omega)

theorem upper_triangular (p : PowerSeries ℝ) : TriangularCompression.Upper (upper p) := by
  intro i j hji
  exact if_neg (by omega)

theorem lower_diagonal (p : PowerSeries ℝ) (i : ℕ) : lower p i i=p.constantCoeff := by
  simp [lower]

theorem lower_one : lower (1 : PowerSeries ℝ)=identity := by
  ext i j
  by_cases he : i=j
  · subst j
    simp [lower,identity]
  · by_cases hji : j ≤ i
    · have hn : i-j≠0 := by omega
      simp [lower,identity,hji,he,hn]
    · simp [lower,identity,hji,he]

theorem lower_mul (p q : PowerSeries ℝ) : product (lower p) (lower q)=lower (p*q) := by
  ext i j
  by_cases hji : j ≤ i
  · have he : product (lower p) (lower q) i j=
        ∑ k∈Finset.Icc j i,PowerSeries.coeff (i-k) p*PowerSeries.coeff (k-j) q := by
      unfold product
      rw [tsum_eq_sum (s := Finset.Icc j i)]
      · apply Finset.sum_congr rfl
        intro k hk
        simp only [Finset.mem_Icc] at hk
        simp only [lower,if_pos hk.2,if_pos hk.1]
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        by_cases hki : k ≤ i
        · have hkj : ¬j ≤ k := by tauto
          simp [lower,hki,hkj]
        · simp [lower,hki]
    rw [he,lower,if_pos hji,PowerSeries.coeff_mul]
    apply Finset.sum_bij (fun k _ => (i-k,k-j))
    · intro k hk
      have hk := Finset.mem_Icc.mp hk
      exact Finset.mem_antidiagonal.mpr (by omega)
    · intro k hk l hl hkl
      have hk := Finset.mem_Icc.mp hk
      have hl := Finset.mem_Icc.mp hl
      have he := congrArg Prod.snd hkl
      dsimp only at he
      omega
    · intro r hr
      have hr := Finset.mem_antidiagonal.mp hr
      refine ⟨r.2+j,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
      apply Prod.ext <;> dsimp only <;> omega
    · intro k _
      rfl
  · have hz : ∀ k,lower p i k*lower q k j=0 := by
      intro k
      by_cases hki : k ≤ i
      · have hkj : ¬j ≤ k := by omega
        simp [lower,hki,hkj]
      · simp [lower,hki]
    have he : product (lower p) (lower q) i j=0 := by
      unfold product
      simp only [hz,tsum_zero]
    rw [he]
    simp only [lower,if_neg hji]

theorem upper_mul (p q : PowerSeries ℝ) : product (upper p) (upper q)=upper (p*q) := by
  rw [upper,upper,← transpose_product,lower_mul,mul_comm q p]
  rfl

theorem lower_row_sum (p : PowerSeries ℝ) (i : ℕ) :
    rowNorm (lower p) i=∑ n∈Finset.range (i+1),|PowerSeries.coeff n p| := by
  unfold rowNorm
  rw [tsum_eq_sum (s := Finset.range (i+1))]
  · have he : (∑ j∈Finset.range (i+1),|lower p i j|)=
        ∑ j∈Finset.range (i+1),|PowerSeries.coeff (i-j) p| := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hj
      simp only [lower,if_pos (show j ≤ i by omega)]
    rw [he]
    simpa only [Nat.add_sub_cancel] using
      Finset.sum_range_reflect (fun n => |PowerSeries.coeff n p|) (i+1)
  · intro j hj
    have hj : ¬j ≤ i := by simp only [Finset.mem_range] at hj; omega
    simp [lower,hj]

theorem lower_row_summable (p : PowerSeries ℝ) (i : ℕ) :
    Summable (fun j => |lower p i j|) := by
  apply summable_of_ne_finset_zero (s := Finset.range (i+1))
  intro j hj
  have hj : ¬j ≤ i := by simp only [Finset.mem_range] at hj; omega
  simp [lower,hj]

theorem lower_column_summable {p : PowerSeries ℝ} (hp : SummableWeighted p) (j : ℕ) :
    Summable (fun i => |lower p i j|) := by
  apply (summable_nat_add_iff j).mp
  simpa only [lower,Nat.le_add_left,if_true,Nat.add_sub_cancel] using coefficients_summable hp

theorem lower_column_sum {p : PowerSeries ℝ} (hp : SummableWeighted p) (j : ℕ) :
    (∑' i,|lower p i j|)=∑' n,|PowerSeries.coeff n p| := by
  have ht := (lower_column_summable hp j).sum_add_tsum_nat_add j
  have hz : (∑ i∈Finset.range j,|lower p i j|)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_range] at hi
    simp [lower,show ¬j ≤ i by omega]
  rw [hz,zero_add] at ht
  simpa only [lower,Nat.le_add_left,if_true,Nat.add_sub_cancel] using ht.symm

theorem rowBound_lower {p : PowerSeries ℝ} (hp : SummableWeighted p) : RowBound (lower p) (mass p) := by
  refine ⟨mass_nonneg p,lower_row_summable p,?_⟩
  intro i
  rw [lower_row_sum]
  exact ((coefficients_summable hp).sum_le_tsum _ (fun _ _ => abs_nonneg _)).trans (coefficients_mass_le hp)

theorem columnBound_lower {p : PowerSeries ℝ} (hp : SummableWeighted p) : ColumnBound (lower p) (mass p) := by
  refine ⟨mass_nonneg p,lower_column_summable hp,?_⟩
  intro j
  change (∑' i,|lower p i j|) ≤ mass p
  rw [lower_column_sum hp]
  exact coefficients_mass_le hp

theorem rowBound_upper {p : PowerSeries ℝ} (hp : SummableWeighted p) : RowBound (upper p) (mass p) :=
  columnBound_lower hp

theorem columnBound_upper {p : PowerSeries ℝ} (hp : SummableWeighted p) : ColumnBound (upper p) (mass p) := by
  simpa only [ColumnBound,upper,transpose_transpose] using rowBound_lower hp

theorem lower_exponential_add {V : PowerSeries ℝ} (hV : V.constantCoeff=0) (s t : ℝ) :
    product (lower (exponential V s)) (lower (exponential V t))=lower (exponential V (s+t)) := by
  rw [lower_mul,exponential_add hV]

theorem lower_exponential_inverse {V : PowerSeries ℝ} (hV : V.constantCoeff=0) (t : ℝ) :
    product (lower (exponential V t)) (lower (exponential V (-t)))=identity := by
  rw [lower_mul,exponential_inverse hV,lower_one]


/-- The constant coefficient is counted once; all negative modes vanish. -/
def lift (p : PowerSeries ℝ) : ToeplitzHankelKernels.Laurent
  | Int.ofNat n => PowerSeries.coeff n p
  | Int.negSucc _ => 0

theorem lift_nat (p : PowerSeries ℝ) (n : ℕ) : lift p (n : ℤ)=PowerSeries.coeff n p := rfl

theorem lift_negSucc (p : PowerSeries ℝ) (n : ℕ) : lift p (Int.negSucc n)=0 := rfl

theorem lift_negative (p : PowerSeries ℝ) {n : ℤ} (hn : n < 0) : lift p n=0 := by
  cases n with
  | ofNat n =>
    have hnonneg : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    exact ((not_lt_of_ge hnonneg) hn).elim
  | negSucc n => rfl

theorem T_lift (p : PowerSeries ℝ) : ToeplitzHankelKernels.T (lift p)=lower p := by
  ext i j
  unfold ToeplitzHankelKernels.T lower
  by_cases hji : j ≤ i
  · rw [if_pos hji,← Int.ofNat_sub hji,lift_nat]
  · rw [if_neg hji]
    exact lift_negative p (by omega)

theorem weighted_lift {p : PowerSeries ℝ} (hp : SummableWeighted p) :
    ToeplitzHankelKernels.WeightedSummable (lift p) := by
  have hpos : Summable (fun n : ℕ => ToeplitzHankelKernels.weightedTerm (lift p) (n : ℤ)) := by
    have hp' : Summable (fun n : ℕ => (1+(n : ℝ))*|PowerSeries.coeff n p|) := hp
    simpa only [ToeplitzHankelKernels.weightedTerm,lift_nat,Int.natAbs_natCast] using hp'
  have hneg : Summable (fun n : ℕ => ToeplitzHankelKernels.weightedTerm (lift p) (-(n+1 : ℤ))) := by
    have he (n : ℕ) : ToeplitzHankelKernels.weightedTerm (lift p) (-(n+1 : ℤ))=0 := by
      simp only [ToeplitzHankelKernels.weightedTerm,lift_negative p (by omega : -(n+1 : ℤ) < 0),abs_zero,mul_zero]
    simp only [he,summable_zero]
  exact hpos.of_nat_of_neg_add_one hneg

theorem weightedMass_lift {p : PowerSeries ℝ} (hp : SummableWeighted p) :
    ToeplitzHankelKernels.weightedMass (lift p)=mass p := by
  have h : (∑' n : ℕ,(ToeplitzHankelKernels.weightedTerm (lift p) (n : ℤ)+
      ToeplitzHankelKernels.weightedTerm (lift p) (-(n+1 : ℤ))))=
      ToeplitzHankelKernels.weightedMass (lift p) := by
    simpa only [Nat.cast_add,Nat.cast_one,ToeplitzHankelKernels.weightedMass] using
      tsum_nat_add_neg_add_one (weighted_lift hp)
  have he (n : ℕ) : ToeplitzHankelKernels.weightedTerm (lift p) (-(n+1 : ℤ))=0 := by
    simp only [ToeplitzHankelKernels.weightedTerm,lift_negative p (by omega : -(n+1 : ℤ) < 0),abs_zero,mul_zero]
  simp_rw [he] at h
  simpa only [add_zero,ToeplitzHankelKernels.weightedTerm,lift_nat,Int.natAbs_natCast,
    ToeplitzHankelKernels.weightedMass,mass,term] using h.symm

theorem H_flip_lift (p : PowerSeries ℝ) :
    ToeplitzHankelKernels.H (ToeplitzHankelKernels.flip (lift p))=0 := by
  ext i j
  change lift p (-((i+j+1 : ℕ) : ℤ))=0
  apply lift_negative p
  omega



theorem upper_one : upper (1 : PowerSeries ℝ)=identity := by
  rw [upper,lower_one]
  ext i j
  simp only [transpose,identity,eq_comm]

theorem upper_exponential_inverse {V : PowerSeries ℝ} (hV : V.constantCoeff=0) (t : ℝ) :
    product (upper (exponential V t)) (upper (exponential V (-t)))=identity := by
  rw [upper_mul,exponential_inverse hV,upper_one]

theorem exponential_constant {V : PowerSeries ℝ} (hV : V.constantCoeff=0) (t : ℝ) :
    (exponential V t).constantCoeff=1 := by
  have h := coefficient_finite hV t 0
  simpa [coefficient,Finset.sum_range_succ] using h

theorem lower_exponential_bounds {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (t : ℝ) :
    RowBound (lower (exponential V t)) (Real.exp (|t| * mass V)) ∧
    ColumnBound (lower (exponential V t)) (Real.exp (|t| * mass V)) := by
  obtain ⟨hs,hm⟩ := exponential_control hV0 hV t
  have hr := rowBound_lower hs
  have hc := columnBound_lower hs
  exact ⟨⟨(Real.exp_pos _).le,hr.summable,fun i => (hr.bound i).trans hm⟩,
    ⟨(Real.exp_pos _).le,hc.summable,fun i => (hc.bound i).trans hm⟩⟩

end
end SpanningTreeIsoperimetry.OneSidedToeplitz
