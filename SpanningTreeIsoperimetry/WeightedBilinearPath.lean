import SpanningTreeIsoperimetry.WeightedLaurentPath
import SpanningTreeIsoperimetry.SummableDeterminantPath

/-! A concrete three-term remainder estimate shared by weighted convolution
and summable kernel products. The data below record proved scalar mass
inequalities; they install no norm, topology, or Banach-space instance. -/
namespace SpanningTreeIsoperimetry.WeightedBilinearPath
open ToeplitzHankelKernels LaurentWeightedConvolution WeightedLaurentPath
open Filter Asymptotics
open scoped Topology
noncomputable section

structure MassData (V : Type*) [AddCommGroup V] [Module ℝ V] where
  regular : V → Prop
  mass : V → ℝ
  nonneg : ∀ v,0≤mass v
  add_regular : ∀ {v w},regular v → regular w → regular (v+w)
  smul_regular : ∀ {v},regular v → ∀ t : ℝ,regular (t • v)
  add_le : ∀ {v w},regular v → regular w → mass (v+w)≤mass v+mass w
  smul_mass : ∀ (t : ℝ) v,mass (t • v)=|t| *mass v

structure BilinearData {V : Type*} [AddCommGroup V] [Module ℝ V] (D : MassData V) where
  map : Laurent → Laurent → V
  regular : ∀ {a b},WeightedSummable a → WeightedSummable b → D.regular (map a b)
  bound : ∀ {a b},WeightedSummable a → WeightedSummable b → D.mass (map a b)≤weightedMass a*weightedMass b
  add_left : ∀ {a b c},WeightedSummable a → WeightedSummable b → WeightedSummable c →
    map (a+b) c=map a c+map b c
  add_right : ∀ {a b c},WeightedSummable a → WeightedSummable b → WeightedSummable c →
    map a (b+c)=map a b+map a c
  smul_left : ∀ (t : ℝ) a b,map (t • a) b=t • map a b
  smul_right : ∀ (t : ℝ) a b,map a (t • b)=t • map a b

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {D : MassData V}

def productRemainder (F : BilinearData D) (a b : ℝ → Laurent) (a1 b1 : Laurent) (t : ℝ) : V :=
  F.map (a t) (b t)-F.map (a 0) (b 0)-t • (F.map a1 (b 0)+F.map (a 0) b1)

theorem remainder_eq (F : BilinearData D) {a b : ℝ → Laurent} {a1 b1 : Laurent}
    (ha : ∀ t,WeightedSummable (a t)) (hb : ∀ t,WeightedSummable (b t))
    (ha1 : WeightedSummable a1) (hb1 : WeightedSummable b1) (t : ℝ) :
    productRemainder F a b a1 b1 t=
      F.map (remainder a a1 t) (b t)+F.map (a 0) (remainder b b1 t)+
        t • F.map a1 (b t-b 0) := by
  have har := remainder_weighted ha ha1 t
  have hbr := remainder_weighted hb hb1 t
  have hae : a t=remainder a a1 t+(a 0+t • a1) := by unfold remainder; abel
  have hbe : b t=remainder b b1 t+(b 0+t • b1) := by unfold remainder; abel
  have hde : b t=(b t-b 0)+b 0 := by abel
  have h1 : F.map (a t) (b t)=F.map (remainder a a1 t) (b t)+
      (F.map (a 0) (b t)+t • F.map a1 (b t)) := by
    conv_lhs => rw [hae]
    rw [F.add_left har (weighted_add (ha 0) (weighted_smul ha1 t)) (hb t),
      F.add_left (ha 0) (weighted_smul ha1 t) (hb t),F.smul_left]
  have h2 : F.map (a 0) (b t)=F.map (a 0) (remainder b b1 t)+
      (F.map (a 0) (b 0)+t • F.map (a 0) b1) := by
    conv_lhs => rw [hbe]
    rw [F.add_right (ha 0) hbr (weighted_add (hb 0) (weighted_smul hb1 t)),
      F.add_right (ha 0) (hb 0) (weighted_smul hb1 t),F.smul_right]
  have h3 : F.map a1 (b t)=F.map a1 (b t-b 0)+F.map a1 (b 0) := by
    conv_lhs => rw [hde]
    exact F.add_right ha1 (weighted_sub (hb t) (hb 0)) (hb 0)
  unfold productRemainder
  rw [h1,h2,h3,smul_add,smul_add]
  abel

theorem remainder_mass_le (F : BilinearData D) {a b : ℝ → Laurent} {a1 b1 : Laurent}
    (ha : ∀ t,WeightedSummable (a t)) (hb : ∀ t,WeightedSummable (b t))
    (ha1 : WeightedSummable a1) (hb1 : WeightedSummable b1) (t : ℝ) :
    D.mass (productRemainder F a b a1 b1 t)≤
      weightedMass (remainder a a1 t)*weightedMass (b t)+
      weightedMass (a 0)*weightedMass (remainder b b1 t)+
      |t| *(weightedMass a1*weightedMass (b t-b 0)) := by
  have har := remainder_weighted ha ha1 t
  have hbr := remainder_weighted hb hb1 t
  have hdb := weighted_sub (hb t) (hb 0)
  rw [remainder_eq F ha hb ha1 hb1 t]
  have hsum := D.add_le (D.add_regular (F.regular har (hb t)) (F.regular (ha 0) hbr))
    (D.smul_regular (F.regular ha1 hdb) t)
  have hxy := D.add_le (F.regular har (hb t)) (F.regular (ha 0) hbr)
  rw [D.smul_mass] at hsum
  have hx := F.bound har (hb t)
  have hy := F.bound (ha 0) hbr
  have hz := mul_le_mul_of_nonneg_left (F.bound ha1 hdb) (abs_nonneg t)
  linarith

/-- The same ordinary Leibniz remainder estimate applies to every concrete
bilinear map satisfying these proved entry-mass bounds. -/
theorem remainder_isLittleO (F : BilinearData D) {a b : ℝ → Laurent} {a1 b1 : Laurent}
    (ha : ∀ t,WeightedSummable (a t)) (hb : ∀ t,WeightedSummable (b t))
    (ha1 : WeightedSummable a1) (hb1 : WeightedSummable b1)
    (hra : (fun t => weightedMass (remainder a a1 t)) =o[𝓝 0] fun t => t)
    (hrb : (fun t => weightedMass (remainder b b1 t)) =o[𝓝 0] fun t => t) :
    (fun t => D.mass (productRemainder F a b a1 b1 t)) =o[𝓝 0] fun t => t := by
  let C : ℝ := 1+weightedMass (b 0)+weightedMass b1
  have hC : 0≤C := by
    have h0 := weightedMass_nonneg (b 0)
    have h1 := weightedMass_nonneg b1
    dsimp [C]
    linarith
  have hdb : (fun t => weightedMass (b t-b 0)) =o[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr (difference_mass_tendsto_zero hb hb1 hrb)
  have habs : (fun t : ℝ => |t|) =O[𝓝 0] (fun t => t) := by
    apply isBigO_iff.mpr
    exact ⟨1,Eventually.of_forall (fun t => by simp only [Real.norm_eq_abs,abs_abs,one_mul]; exact le_rfl)⟩
  have hcross : (fun t : ℝ => |t| *weightedMass (b t-b 0)) =o[𝓝 0] fun t => t := by
    simpa only [mul_one] using habs.mul_isLittleO hdb
  let major : ℝ → ℝ := fun t => C*weightedMass (remainder a a1 t)+
    weightedMass (a 0)*weightedMass (remainder b b1 t)+
    weightedMass a1*(|t| *weightedMass (b t-b 0))
  have hm : major =o[𝓝 0] fun t => t :=
    ((hra.const_mul_left C).add (hrb.const_mul_left (weightedMass (a 0)))).add
      (hcross.const_mul_left (weightedMass a1))
  have hmajor0 (t : ℝ) : 0≤major t :=
    add_nonneg (add_nonneg (mul_nonneg hC (weightedMass_nonneg _))
      (mul_nonneg (weightedMass_nonneg _) (weightedMass_nonneg _)))
      (mul_nonneg (weightedMass_nonneg _) (mul_nonneg (abs_nonneg _) (weightedMass_nonneg _)))
  have hbig : (fun t => D.mass (productRemainder F a b a1 b1 t)) =O[𝓝 0] major := by
    apply isBigO_iff.mpr
    refine ⟨1,?_⟩
    filter_upwards [weightedMass_eventually_bounded hb hb1 hrb] with t ht
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (D.nonneg _),abs_of_nonneg (hmajor0 t),one_mul]
    have hr := remainder_mass_le F ha hb ha1 hb1 t
    have hp := mul_le_mul_of_nonneg_left ht (weightedMass_nonneg (remainder a a1 t))
    change weightedMass (remainder a a1 t)*weightedMass (b t)≤weightedMass (remainder a a1 t)*C at hp
    dsimp only [major]
    nlinarith only [hr,hp]
  exact hbig.trans_isLittleO hm

end
end SpanningTreeIsoperimetry.WeightedBilinearPath
