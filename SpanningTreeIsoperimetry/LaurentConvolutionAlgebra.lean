module

public import SpanningTreeIsoperimetry.LaurentWeightedConvolution

@[expose] public section

/-! The actual integer convolution has a unit and is associative on
absolutely summable coefficients. Weighted summability is preserved by the
already established quantitative product bound. -/
namespace SpanningTreeIsoperimetry.LaurentConvolutionAlgebra
open ToeplitzHankelKernels ToeplitzHankelConvolution LaurentWeightedConvolution
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Laurent convolution unit. This is not the pointwise constant function. -/
def unitCoeff : Laurent := fun n => if n=0 then 1 else 0

theorem weighted_unit : WeightedSummable unitCoeff := by
  have he : weightedTerm unitCoeff=fun n : ℤ => if n=0 then 1 else 0 := by
    funext n
    by_cases hn : n=0 <;> simp [weightedTerm,unitCoeff,hn]
  change Summable (weightedTerm unitCoeff)
  rw [he]
  exact (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable

theorem weightedMass_unit : weightedMass unitCoeff=1 := by
  unfold weightedMass
  have he (n : ℤ) : weightedTerm unitCoeff n=if n=0 then 1 else 0 := by
    by_cases hn : n=0 <;> simp [weightedTerm,unitCoeff,hn]
  simp only [he,tsum_ite_eq]

theorem convolution_unit_right (a : Laurent) : convolution a unitCoeff=a := by
  funext n
  simp only [convolution,unitCoeff,mul_ite,mul_one,mul_zero,tsum_ite_eq,sub_zero]

theorem convolution_unit_left (a : Laurent) : convolution unitCoeff a=a := by
  rw [convolution_comm,convolution_unit_right]

theorem convolution_zero_right (a : Laurent) : convolution a 0=0 := by
  funext n
  simp only [convolution,Pi.zero_apply,mul_zero,tsum_zero]

theorem convolution_zero_left (a : Laurent) : convolution 0 a=0 := by
  rw [convolution_comm,convolution_zero_right]

theorem flip_unit : flip unitCoeff=unitCoeff := by
  funext n
  simp only [ToeplitzHankelKernels.flip,unitCoeff,neg_eq_zero]

theorem flip_flip (a : Laurent) : flip (flip a)=a := by
  funext n
  simp only [ToeplitzHankelKernels.flip,neg_neg]

theorem flip_convolution (a b : Laurent) :
    flip (convolution a b)=convolution (flip a) (flip b) := by
  funext n
  have ht := (Equiv.neg ℤ).tsum_eq (fun k : ℤ => a (-n-k)*b k)
  change (∑' k : ℤ,a (-n-(-k))*b (-k))=(∑' k : ℤ,a (-n-k)*b k) at ht
  change (∑' k : ℤ,a (-n-k)*b k)=(∑' k : ℤ,a (-(n-k))*b (-k))
  rw [← ht]
  apply tsum_congr
  intro k
  congr 1
  congr 1
  ring

theorem flip_eq_iff_even (a : Laurent) : flip a=a ↔ Function.Even a := by
  constructor
  · intro h n
    exact congrFun h n
  · intro h
    funext n
    exact h n

theorem convolution_flip_even (a : Laurent) : Function.Even (convolution a (flip a)) := by
  apply (flip_eq_iff_even _).mp
  rw [flip_convolution,flip_flip,convolution_comm]

/-- A bijection giving the two unconstrained coefficient indices in a
triple convolution. -/
def tripleShear (n : ℤ) : (ℤ×ℤ) ≃ (ℤ×ℤ) where
  toFun p := (n-p.1,p.1-p.2)
  invFun p := (n-p.1,n-p.1-p.2)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by ext <;> dsimp <;> ring

def tripleTerm (a b c : Laurent) (n : ℤ) (p : ℤ×ℤ) : ℝ :=
  (a (n-p.1)*b (p.1-p.2))*c p.2

theorem tripleTerm_summable {a b c : Laurent}
    (ha : Summable (fun n => |a n|)) (hb : Summable (fun n => |b n|))
    (hc : Summable (fun n => |c n|)) (n : ℤ) : Summable (tripleTerm a b c n) := by
  have hp : Summable (fun p : ℤ×ℤ => |a p.1| *|b p.2|) :=
    ha.mul_of_nonneg hb (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
  have hs := hp.comp_injective (i := tripleShear n) (tripleShear n).injective
  have hs' : Summable (fun p : ℤ×ℤ => |a (n-p.1)| *|b (p.1-p.2)|) := hs
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hs'.mul_right (mass c))
  intro p
  simp only [tripleTerm,Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_le_mass hc p.2) (by positivity)

theorem convolution_assoc {a b c : Laurent}
    (ha : Summable (fun n => |a n|)) (hb : Summable (fun n => |b n|))
    (hc : Summable (fun n => |c n|)) :
    convolution (convolution a b) c=convolution a (convolution b c) := by
  funext n
  have hs := tripleTerm_summable ha hb hc n
  calc
    convolution (convolution a b) c n=(∑' l : ℤ,∑' k : ℤ,tripleTerm a b c n (k,l)) := by
      unfold convolution
      apply tsum_congr
      intro l
      have he := convolution_shift a b n l
      change (∑' k : ℤ,a ((n-l)-k)*b k)=(∑' k : ℤ,a (n-k)*b (k-l)) at he
      rw [he,← tsum_mul_right]
      rfl
    _=(∑' p : ℤ×ℤ,tripleTerm a b c n p.swap) := hs.prod_symm.tsum_prod.symm
    _=(∑' p : ℤ×ℤ,tripleTerm a b c n p) := (Equiv.prodComm ℤ ℤ).tsum_eq _
    _=(∑' k : ℤ,∑' l : ℤ,tripleTerm a b c n (k,l)) := hs.tsum_prod
    _=convolution a (convolution b c) n := by
      simp only [convolution,tripleTerm,mul_assoc,tsum_mul_left]

theorem convolution_assoc_weighted {a b c : Laurent}
    (ha : WeightedSummable a) (hb : WeightedSummable b) (hc : WeightedSummable c) :
    convolution (convolution a b) c=convolution a (convolution b c) :=
  convolution_assoc (summable_abs ha) (summable_abs hb) (summable_abs hc)


theorem convolution_left_comm {a b c : Laurent}
    (ha : WeightedSummable a) (hb : WeightedSummable b) (hc : WeightedSummable c) :
    convolution a (convolution b c)=convolution b (convolution a c) := by
  rw [← convolution_assoc_weighted ha hb hc,convolution_comm a b,
    convolution_assoc_weighted hb ha hc]

/-- Pairing a factor with its reflected factor preserves its convolution
inverse. This is the exact even-symbol inverse used by the shifted kernel. -/
theorem convolution_flip_inverse {a b : Laurent}
    (ha : WeightedSummable a) (hb : WeightedSummable b)
    (hinv : convolution a b=unitCoeff) :
    convolution (convolution a (flip a)) (convolution b (flip b))=unitCoeff := by
  rw [convolution_assoc_weighted ha (weighted_flip ha)
      (weighted_convolution hb (weighted_flip hb)),
    convolution_left_comm (weighted_flip ha) hb (weighted_flip hb),
    ← convolution_assoc_weighted ha hb (weighted_convolution (weighted_flip ha) (weighted_flip hb)),
    hinv,convolution_unit_left,← flip_convolution,hinv,flip_unit]

end
end SpanningTreeIsoperimetry.LaurentConvolutionAlgebra
