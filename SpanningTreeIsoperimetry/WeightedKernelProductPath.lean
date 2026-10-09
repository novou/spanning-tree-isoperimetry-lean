import SpanningTreeIsoperimetry.WeightedBilinearPath
import SpanningTreeIsoperimetry.ToeplitzHankelMassBounds
import SpanningTreeIsoperimetry.BoundedKernelAlgebra

/-! Actual Toeplitz/Hankel products inherit the weighted-coefficient Leibniz
rule in total entry mass. All linearity and product bounds are discharged for
the concrete kernels. No ambient operator algebra is assumed. -/
namespace SpanningTreeIsoperimetry.WeightedKernelProductPath
open ToeplitzHankelKernels ToeplitzHankelMassBounds LaurentWeightedConvolution
open SummableKernelProduct SummableKernelAlgebra BoundedKernelProduct
open SummableDeterminantFirstOrder SummableDeterminantPath AbsolutelySummableDeterminant
open WeightedLaurentPath WeightedBilinearPath Filter Asymptotics
open scoped Topology
noncomputable section

def kernelMass : MassData Kernel where
  regular := fun K => Summable (entryNorm K)
  mass := totalMass
  nonneg := totalMass_nonneg
  add_regular := add_summable
  smul_regular := fun hK t => scale_summable t hK
  add_le := mass_add_le
  smul_mass := fun t K => scale_mass t K

/-- Concrete linear maps with the row and column estimates needed by the
entrywise product. The two instances below are the actual T and H kernels. -/
structure KernelMap where
  map : Laurent → Kernel
  add : ∀ a b,map (a+b)=map a+map b
  smul : ∀ (t : ℝ) a,map (t • a)=t • map a
  rows : ∀ {a},WeightedSummable a → RowBound (map a) (weightedMass a)
  columns : ∀ {a},WeightedSummable a → ColumnBound (map a) (weightedMass a)

def toeplitzMap : KernelMap where
  map := T
  add := T_add
  smul := T_smul
  rows := rowBound_T_weighted
  columns := columnBound_T_weighted

def hankelMap (d : ℕ) : KernelMap where
  map := fun a => hankelOffset a d
  add := fun a b => hankelOffset_add a b d
  smul := fun t a => hankelOffset_smul t a d
  rows := fun ha => rowBound_hankelOffset_weighted ha d
  columns := fun ha => columnBound_hankelOffset_weighted ha d

def mixed (L : KernelMap) (d : ℕ) (a b : Laurent) : Kernel :=
  product (L.map a) (hankelOffset b d)

theorem mixed_summable (L : KernelMap) (d : ℕ) {a b : Laurent}
    (ha : WeightedSummable a) (hb : WeightedSummable b) : Summable (entryNorm (mixed L d a b)) :=
  left_summable (L.columns ha) (hankelOffset_summable hb d)

theorem mixed_mass_le (L : KernelMap) (d : ℕ) {a b : Laurent}
    (ha : WeightedSummable a) (hb : WeightedSummable b) :
    totalMass (mixed L d a b)≤weightedMass a*weightedMass b :=
  (left_mass_le (L.columns ha) (hankelOffset_summable hb d)).trans
    (mul_le_mul_of_nonneg_left (hankelOffset_mass_le hb d) (weightedMass_nonneg a))

theorem mixed_entry_summable (L : KernelMap) (d : ℕ) {a b : Laurent}
    (ha : WeightedSummable a) (hb : WeightedSummable b) (i j : ℕ) :
    Summable (fun k => L.map a i k*hankelOffset b d k j) := by
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs] using BoundedKernelAlgebra.entry_product_summable
    (L.rows ha) (rowBound_hankelOffset_weighted hb d) i j

theorem mixed_add_left (L : KernelMap) (d : ℕ) {a b c : Laurent}
    (ha : WeightedSummable a) (hb : WeightedSummable b) (hc : WeightedSummable c) :
    mixed L d (a+b) c=mixed L d a c+mixed L d b c := by
  ext i j
  simp only [mixed,L.add,product,Pi.add_apply,add_mul]
  exact (mixed_entry_summable L d ha hc i j).tsum_add (mixed_entry_summable L d hb hc i j)

theorem mixed_add_right (L : KernelMap) (d : ℕ) {a b c : Laurent}
    (ha : WeightedSummable a) (hb : WeightedSummable b) (hc : WeightedSummable c) :
    mixed L d a (b+c)=mixed L d a b+mixed L d a c := by
  ext i j
  simp only [mixed,hankelOffset_add,product,Pi.add_apply,mul_add]
  exact (mixed_entry_summable L d ha hb i j).tsum_add (mixed_entry_summable L d ha hc i j)

theorem mixed_smul_left (L : KernelMap) (d : ℕ) (t : ℝ) (a b : Laurent) :
    mixed L d (t • a) b=t • mixed L d a b := by
  rw [mixed,L.smul,product_smul_left]
  rfl

theorem mixed_smul_right (L : KernelMap) (d : ℕ) (t : ℝ) (a b : Laurent) :
    mixed L d a (t • b)=t • mixed L d a b := by
  rw [mixed,hankelOffset_smul,product_smul_right]
  rfl

def mixedData (L : KernelMap) (d : ℕ) : BilinearData kernelMass where
  map := mixed L d
  regular := mixed_summable L d
  bound := mixed_mass_le L d
  add_left := mixed_add_left L d
  add_right := mixed_add_right L d
  smul_left := mixed_smul_left L d
  smul_right := mixed_smul_right L d

/-- The actual T(a(t)) H_d(b(t)) Leibniz rule in total entry mass. -/
theorem toeplitz_hankel_remainder_isLittleO (d : ℕ) {a b : ℝ → Laurent} {a1 b1 : Laurent}
    (ha : ∀ t,WeightedSummable (a t)) (hb : ∀ t,WeightedSummable (b t))
    (ha1 : WeightedSummable a1) (hb1 : WeightedSummable b1)
    (hra : (fun t => weightedMass (a t-a 0-t • a1)) =o[𝓝 0] fun t => t)
    (hrb : (fun t => weightedMass (b t-b 0-t • b1)) =o[𝓝 0] fun t => t) :
    (fun t => totalMass (product (T (a t)) (hankelOffset (b t) d)-
      product (T (a 0)) (hankelOffset (b 0) d)-
      t • (product (T a1) (hankelOffset (b 0) d)+product (T (a 0)) (hankelOffset b1 d))))
      =o[𝓝 0] fun t => t :=
  remainder_isLittleO (mixedData toeplitzMap d) ha hb ha1 hb1 hra hrb

/-- The actual H_e(a(t)) H_d(b(t)) Leibniz rule, including e=d=1. -/
theorem hankel_hankel_remainder_isLittleO (e d : ℕ) {a b : ℝ → Laurent} {a1 b1 : Laurent}
    (ha : ∀ t,WeightedSummable (a t)) (hb : ∀ t,WeightedSummable (b t))
    (ha1 : WeightedSummable a1) (hb1 : WeightedSummable b1)
    (hra : (fun t => weightedMass (a t-a 0-t • a1)) =o[𝓝 0] fun t => t)
    (hrb : (fun t => weightedMass (b t-b 0-t • b1)) =o[𝓝 0] fun t => t) :
    (fun t => totalMass (product (hankelOffset (a t) e) (hankelOffset (b t) d)-
      product (hankelOffset (a 0) e) (hankelOffset (b 0) d)-
      t • (product (hankelOffset a1 e) (hankelOffset (b 0) d)+
        product (hankelOffset (a 0) e) (hankelOffset b1 d)))) =o[𝓝 0] fun t => t :=
  remainder_isLittleO (mixedData (hankelMap e) d) ha hb ha1 hb1 hra hrb

end
end SpanningTreeIsoperimetry.WeightedKernelProductPath
