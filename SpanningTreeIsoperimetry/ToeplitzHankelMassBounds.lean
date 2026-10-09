import SpanningTreeIsoperimetry.LaurentWeightedConvolution

/-! Quantitative linear controls for the actual Toeplitz and Hankel maps.
These estimates also apply directly to coefficient differences and remainders. -/
namespace SpanningTreeIsoperimetry.ToeplitzHankelMassBounds
open ToeplitzHankelKernels ToeplitzHankelConvolution LaurentWeightedConvolution
open AbsolutelySummableDeterminant SummableKernelProduct BoundedKernelProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem rowBound_mono {K : Kernel} {C D : ℝ} (h : RowBound K C) (hCD : C≤D) : RowBound K D :=
  ⟨h.nonneg.trans hCD,h.summable,fun i => (h.bound i).trans hCD⟩

theorem rowBound_T_weighted {a : Laurent} (ha : WeightedSummable a) : RowBound (T a) (weightedMass a) :=
  rowBound_mono (rowBound_T (summable_abs ha)) (mass_le_weightedMass ha)

theorem columnBound_T_weighted {a : Laurent} (ha : WeightedSummable a) : ColumnBound (T a) (weightedMass a) :=
  rowBound_mono (columnBound_T (summable_abs ha)) (mass_le_weightedMass ha)

theorem rowBound_hankelOffset_weighted {a : Laurent} (ha : WeightedSummable a) (d : ℕ) :
    RowBound (hankelOffset a d) (weightedMass a) :=
  rowBound_mono (rowBound_hankelOffset (summable_abs ha) d) (mass_le_weightedMass ha)

theorem columnBound_hankelOffset_weighted {a : Laurent} (ha : WeightedSummable a) (d : ℕ) :
    ColumnBound (hankelOffset a d) (weightedMass a) :=
  rowBound_mono (columnBound_hankelOffset (summable_abs ha) d) (mass_le_weightedMass ha)

theorem rowBound_M_weighted {a : Laurent} (ha : WeightedSummable a) : RowBound (M a) (2*weightedMass a) :=
  rowBound_mono (rowBound_M (summable_abs ha)) (mul_le_mul_of_nonneg_left (mass_le_weightedMass ha) (by norm_num))

theorem columnBound_M_weighted {a : Laurent} (ha : WeightedSummable a) : ColumnBound (M a) (2*weightedMass a) :=
  rowBound_mono (columnBound_M (summable_abs ha)) (mul_le_mul_of_nonneg_left (mass_le_weightedMass ha) (by norm_num))

theorem hankelOffset_mass_le {a : Laurent} (ha : WeightedSummable a) (d : ℕ) :
    totalMass (hankelOffset a d)≤weightedMass a := by
  have hinj : Function.Injective (fun n : ℕ => ((n+d : ℕ) : ℤ)) := by
    intro m n h
    dsimp only at h
    omega
  have hs := ha.comp_injective hinj
  rw [hankelOffset_mass ha d]
  calc
    _≤∑' n : ℕ,weightedTerm a ((n+d : ℕ) : ℤ) :=
      (weighted_tail_summable ha d).tsum_le_tsum (fun n => by
        unfold weightedTerm
        simp only [Int.natAbs_natCast]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact_mod_cast (show n+1≤1+(n+d) by omega)) hs
    _≤weightedMass a := tsum_comp_le_tsum_of_inj ha (weightedTerm_nonneg a) hinj

theorem H_mass_le {a : Laurent} (ha : WeightedSummable a) : totalMass (H a)≤weightedMass a :=
  hankelOffset_mass_le ha 1

theorem Hshift_mass_le {a : Laurent} (ha : WeightedSummable a) : totalMass (Hshift a)≤weightedMass a :=
  hankelOffset_mass_le ha 2

theorem T_add (a b : Laurent) : T (a+b)=T a+T b := rfl
theorem T_sub (a b : Laurent) : T (a-b)=T a-T b := rfl
theorem T_smul (c : ℝ) (a : Laurent) : T (c • a)=c • T a := rfl
theorem hankelOffset_add (a b : Laurent) (d : ℕ) :
    hankelOffset (a+b) d=hankelOffset a d+hankelOffset b d := rfl
theorem hankelOffset_sub (a b : Laurent) (d : ℕ) :
    hankelOffset (a-b) d=hankelOffset a d-hankelOffset b d := rfl
theorem hankelOffset_smul (c : ℝ) (a : Laurent) (d : ℕ) :
    hankelOffset (c • a) d=c • hankelOffset a d := rfl

theorem M_add (a b : Laurent) : M (a+b)=M a+M b := by
  ext i j
  change (a _+b _)-(a _+b _)=(a _-a _)+(b _-b _)
  ring

theorem M_sub (a b : Laurent) : M (a-b)=M a-M b := by
  ext i j
  change (a _-b _)-(a _-b _)=(a _-a _)-(b _-b _)
  ring

theorem M_smul (c : ℝ) (a : Laurent) : M (c • a)=c • M a := by
  ext i j
  change c*a _-c*a _=c*(a _-a _)
  ring

theorem T_difference_rowBound {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b) :
    RowBound (T a-T b) (weightedMass (a-b)) := by
  rw [← T_sub]
  exact rowBound_T_weighted (weighted_sub ha hb)

theorem T_difference_columnBound {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b) :
    ColumnBound (T a-T b) (weightedMass (a-b)) := by
  rw [← T_sub]
  exact columnBound_T_weighted (weighted_sub ha hb)

theorem hankelOffset_difference_summable {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b)
    (d : ℕ) : Summable (entryNorm (hankelOffset a d-hankelOffset b d)) := by
  rw [← hankelOffset_sub]
  exact hankelOffset_summable (weighted_sub ha hb) d

theorem hankelOffset_difference_mass_le {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b)
    (d : ℕ) : totalMass (hankelOffset a d-hankelOffset b d)≤weightedMass (a-b) := by
  rw [← hankelOffset_sub]
  exact hankelOffset_mass_le (weighted_sub ha hb) d

theorem M_difference_rowBound {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b) :
    RowBound (M a-M b) (2*weightedMass (a-b)) := by
  rw [← M_sub]
  exact rowBound_M_weighted (weighted_sub ha hb)

theorem M_difference_columnBound {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b) :
    ColumnBound (M a-M b) (2*weightedMass (a-b)) := by
  rw [← M_sub]
  exact columnBound_M_weighted (weighted_sub ha hb)

/-- Quantitative version of the Hankel defect in Laurent multiplication. -/
theorem toeplitz_defect_mass_le {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b) :
    totalMass (T (convolution a b)-product (T a) (T b))≤weightedMass a*weightedMass b := by
  have he : T (convolution a b)-product (T a) (T b)=product (H a) (H (flip b)) := by
    rw [toeplitz_convolution_weighted ha hb]
    abel
  rw [he]
  have hB : RowBound (H (flip b)) (weightedMass b) := by
    simpa only [H,weightedMass_flip] using rowBound_hankelOffset_weighted (weighted_flip hb) 1
  exact (right_mass_le (H_summable ha) hB).trans
    (mul_le_mul_of_nonneg_right (H_mass_le ha) (weightedMass_nonneg b))

end
end SpanningTreeIsoperimetry.ToeplitzHankelMassBounds
