import SpanningTreeIsoperimetry.ToeplitzHankelConvolution
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Concrete weighted absolute estimates for Laurent convolution. The weight
is `1 + |n|`; no ambient Banach algebra is postulated. -/
namespace SpanningTreeIsoperimetry.LaurentWeightedConvolution
open ToeplitzHankelKernels ToeplitzHankelConvolution
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem weightedMass_nonneg (a : Laurent) : 0≤weightedMass a :=
  tsum_nonneg (weightedTerm_nonneg a)

theorem abs_le_weightedTerm (a : Laurent) (n : ℤ) : |a n|≤weightedTerm a n := by
  unfold weightedTerm
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n.natAbs) (abs_nonneg (a n))]

theorem mass_le_weightedMass {a : Laurent} (ha : WeightedSummable a) :
    mass a≤weightedMass a :=
  (summable_abs ha).tsum_le_tsum (abs_le_weightedTerm a) ha

theorem weightedTerm_add_le (a b : Laurent) (n : ℤ) :
    weightedTerm (a+b) n≤weightedTerm a n+weightedTerm b n := by
  unfold weightedTerm
  simpa only [Pi.add_apply,mul_add] using
    mul_le_mul_of_nonneg_left (abs_add_le (a n) (b n)) (by positivity : (0 : ℝ)≤1+n.natAbs)

theorem weighted_add {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b) :
    WeightedSummable (a+b) :=
  Summable.of_nonneg_of_le (weightedTerm_nonneg _) (weightedTerm_add_le a b) (ha.add hb)

theorem weightedMass_add_le {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b) :
    weightedMass (a+b)≤weightedMass a+weightedMass b := by
  have h := (weighted_add ha hb).tsum_le_tsum (weightedTerm_add_le a b) (ha.add hb)
  simpa only [ha.tsum_add hb,weightedMass] using h

theorem weighted_neg {a : Laurent} (ha : WeightedSummable a) : WeightedSummable (-a) := by
  change Summable (fun n => (1+(n.natAbs : ℝ))*|(-a) n|)
  change Summable (fun n => (1+(n.natAbs : ℝ))*|a n|) at ha
  simpa only [Pi.neg_apply,abs_neg] using ha

theorem weighted_sub {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b) :
    WeightedSummable (a-b) := by
  simpa only [sub_eq_add_neg] using weighted_add ha (weighted_neg hb)

theorem weightedMass_neg (a : Laurent) : weightedMass (-a)=weightedMass a := by
  simp only [weightedMass,weightedTerm,Pi.neg_apply,abs_neg]

theorem weightedMass_sub_le {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b) :
    weightedMass (a-b)≤weightedMass a+weightedMass b := by
  simpa only [sub_eq_add_neg,weightedMass_neg] using weightedMass_add_le ha (weighted_neg hb)

theorem weighted_smul {a : Laurent} (ha : WeightedSummable a) (c : ℝ) :
    WeightedSummable (c • a) := by
  convert ha.mul_left |c| using 1
  funext n
  simp only [weightedTerm,Pi.smul_apply,smul_eq_mul,abs_mul]
  ring

theorem weightedMass_smul (a : Laurent) (c : ℝ) : weightedMass (c • a)=|c| *weightedMass a := by
  unfold weightedMass
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [weightedTerm,Pi.smul_apply,smul_eq_mul,abs_mul]
  ring

theorem weightedMass_flip (a : Laurent) : weightedMass (flip a)=weightedMass a := by
  have h := (Equiv.neg ℤ).tsum_eq (weightedTerm a)
  change (∑' n : ℤ,weightedTerm a (-n))=(∑' n : ℤ,weightedTerm a n) at h
  simpa only [weightedMass,weightedTerm,ToeplitzHankelKernels.flip,Int.natAbs_neg] using h

/-- Integer shear reindexes convolution without dropping any index. -/
def convolutionShear : (ℤ×ℤ) ≃ (ℤ×ℤ) where
  toFun p := (p.1-p.2,p.2)
  invFun p := (p.1+p.2,p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

def pairMajorant (a b : Laurent) (p : ℤ×ℤ) : ℝ :=
  weightedTerm a (p.1-p.2)*weightedTerm b p.2

theorem pairMajorant_summable {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b) :
    Summable (pairMajorant a b) := by
  have hp : Summable (fun p : ℤ×ℤ => weightedTerm a p.1*weightedTerm b p.2) :=
    ha.mul_of_nonneg hb (weightedTerm_nonneg a) (weightedTerm_nonneg b)
  have hs := hp.comp_injective (i := convolutionShear) convolutionShear.injective
  exact hs

theorem pairMajorant_sum {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b) :
    (∑' p : ℤ×ℤ,pairMajorant a b p)=weightedMass a*weightedMass b := by
  calc
    _=(∑' p : ℤ×ℤ,weightedTerm a p.1*weightedTerm b p.2) :=
      convolutionShear.tsum_eq _
    _=_ := (ha.tsum_mul_tsum hb
      (ha.mul_of_nonneg hb (weightedTerm_nonneg a) (weightedTerm_nonneg b))).symm

theorem weight_sub_le (n k : ℤ) :
    (1+(n.natAbs : ℝ))≤(1+((n-k).natAbs : ℝ))*(1+(k.natAbs : ℝ)) := by
  have hn : n.natAbs≤(n-k).natAbs+k.natAbs := by
    simpa only [sub_add_cancel] using Int.natAbs_add_le (n-k) k
  have hr : (n.natAbs : ℝ)≤((n-k).natAbs : ℝ)+(k.natAbs : ℝ) := by exact_mod_cast hn
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (n-k).natAbs)
    (Nat.cast_nonneg (α := ℝ) k.natAbs)]

theorem weighted_convolution_term_le {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b)
    (n : ℤ) : weightedTerm (convolution a b) n≤∑' k : ℤ,pairMajorant a b (n,k) := by
  have habs : Summable (fun k : ℤ => |a (n-k)*b k|) := by
    apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _
      (((summable_abs ha).comp_injective (Equiv.subLeft n).injective).mul_right (mass b))
    intro k
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_le_mass (summable_abs hb) k) (abs_nonneg _)
  have hnorm : |convolution a b n|≤∑' k : ℤ,|a (n-k)*b k| := by
    simpa only [convolution,Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun k : ℤ => a (n-k)*b k)
        (by simpa only [Real.norm_eq_abs] using habs)
  have hmajor : Summable (fun k : ℤ => pairMajorant a b (n,k)) :=
    (pairMajorant_summable ha hb).comp_injective (by
      intro i j h
      exact congrArg Prod.snd h)
  calc
    _≤(1+(n.natAbs : ℝ))*(∑' k : ℤ,|a (n-k)*b k|) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _=∑' k : ℤ,(1+(n.natAbs : ℝ))*|a (n-k)*b k| := (tsum_mul_left).symm
    _≤_ := (habs.mul_left _).tsum_le_tsum (fun k => by
      rw [abs_mul]
      calc
        _≤((1+((n-k).natAbs : ℝ))*(1+(k.natAbs : ℝ)))*(|a (n-k)| *|b k|) :=
          mul_le_mul_of_nonneg_right (weight_sub_le n k) (by positivity)
        _=pairMajorant a b (n,k) := by unfold pairMajorant weightedTerm; ring) hmajor

theorem weighted_convolution {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b) :
    WeightedSummable (convolution a b) :=
  Summable.of_nonneg_of_le (weightedTerm_nonneg _) (weighted_convolution_term_le ha hb)
    (pairMajorant_summable ha hb).prod

theorem weightedMass_convolution_le {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b) :
    weightedMass (convolution a b)≤weightedMass a*weightedMass b := by
  have h := (weighted_convolution ha hb).tsum_le_tsum (weighted_convolution_term_le ha hb)
    (pairMajorant_summable ha hb).prod
  exact h.trans_eq ((pairMajorant_summable ha hb).tsum_prod.symm.trans (pairMajorant_sum ha hb))


theorem convolution_terms_summable {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b)
    (n : ℤ) : Summable (fun k : ℤ => a (n-k)*b k) := by
  simpa only [sub_zero] using full_entry_summable (summable_abs ha) (summable_abs hb) n 0

theorem convolution_add_left {a b c : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b)
    (hc : WeightedSummable c) : convolution (a+b) c=convolution a c+convolution b c := by
  funext n
  simp only [convolution,Pi.add_apply,add_mul]
  exact (convolution_terms_summable ha hc n).tsum_add (convolution_terms_summable hb hc n)

theorem convolution_add_right {a b c : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b)
    (hc : WeightedSummable c) : convolution a (b+c)=convolution a b+convolution a c := by
  rw [convolution_comm a (b+c),convolution_add_left hb hc ha,
    convolution_comm b a,convolution_comm c a]

theorem convolution_sub_left {a b c : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b)
    (hc : WeightedSummable c) : convolution (a-b) c=convolution a c-convolution b c := by
  funext n
  simp only [convolution,Pi.sub_apply,sub_mul]
  exact (convolution_terms_summable ha hc n).tsum_sub (convolution_terms_summable hb hc n)

theorem convolution_sub_right {a b c : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b)
    (hc : WeightedSummable c) : convolution a (b-c)=convolution a b-convolution a c := by
  rw [convolution_comm a (b-c),convolution_sub_left hb hc ha,
    convolution_comm b a,convolution_comm c a]

theorem convolution_smul_left (a b : Laurent) (c : ℝ) :
    convolution (c • a) b=c • convolution a b := by
  funext n
  simp only [convolution,Pi.smul_apply,smul_eq_mul,mul_assoc,tsum_mul_left]

theorem convolution_smul_right (a b : Laurent) (c : ℝ) :
    convolution a (c • b)=c • convolution a b := by
  rw [convolution_comm a (c • b),convolution_smul_left,convolution_comm b a]

/-- A concrete continuity estimate, usable without a normed-space instance. -/
theorem convolution_difference_mass_le {a b c d : Laurent}
    (ha : WeightedSummable a) (hb : WeightedSummable b)
    (hc : WeightedSummable c) (hd : WeightedSummable d) :
    weightedMass (convolution a b-convolution c d)≤
      weightedMass (a-c)*weightedMass b+weightedMass c*weightedMass (b-d) := by
  have he : convolution a b-convolution c d=
      convolution (a-c) b+convolution c (b-d) := by
    rw [convolution_sub_left ha hc hb,convolution_sub_right hc hb hd]
    abel
  rw [he]
  exact (weightedMass_add_le (weighted_convolution (weighted_sub ha hc) hb)
    (weighted_convolution hc (weighted_sub hb hd))).trans
      (add_le_add (weightedMass_convolution_le (weighted_sub ha hc) hb)
        (weightedMass_convolution_le hc (weighted_sub hb hd)))

end
end SpanningTreeIsoperimetry.LaurentWeightedConvolution
