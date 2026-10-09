import SpanningTreeIsoperimetry.ToeplitzHankelKernels

/-! Actual integer-convolution identities for the Toeplitz and shifted
Toeplitz-minus-Hankel kernels, with all sum rearrangements justified. -/
namespace SpanningTreeIsoperimetry.ToeplitzHankelConvolution
open ToeplitzHankelKernels SummableKernelProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def convolution (a b : Laurent) (n : ℤ) : ℝ := ∑' k : ℤ,a (n-k)*b k

theorem convolution_comm (a b : Laurent) : convolution a b=convolution b a := by
  funext n
  have ht := (Equiv.subLeft n).tsum_eq (fun k : ℤ => a (n-k)*b k)
  change (∑' k : ℤ,a (n-(n-k))*b (n-k))=convolution a b n at ht
  rw [← ht]
  simp only [sub_sub_cancel]
  unfold convolution
  exact tsum_congr (fun k => mul_comm _ _)

theorem full_entry_summable {a b : Laurent}
    (ha : Summable (fun n => |a n|)) (hb : Summable (fun n => |b n|)) (x y : ℤ) :
    Summable (fun k : ℤ => a (x-k)*b (k-y)) := by
  have hs := (ha.comp_injective (show Function.Injective (fun k : ℤ => x-k) by
    intro i j h; dsimp only at h; omega)).mul_right (mass b)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
  intro k
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_le_mass hb (k-y)) (abs_nonneg _)

theorem convolution_shift (a b : Laurent) (x y : ℤ) :
    convolution a b (x-y)=∑' k : ℤ,a (x-k)*b (k-y) := by
  have ht := (Equiv.subRight y).tsum_eq (fun k : ℤ => a ((x-y)-k)*b k)
  change (∑' k : ℤ,a ((x-y)-(k-y))*b (k-y))=convolution a b (x-y) at ht
  rw [← ht]
  apply tsum_congr
  intro k
  congr 1
  congr 1
  ring

/-- The discarded negative intermediate indices give exactly the Hankel
product, including its index-one convention. -/
theorem toeplitz_convolution {a b : Laurent}
    (ha : Summable (fun n => |a n|)) (hb : Summable (fun n => |b n|)) :
    T (convolution a b)=product (T a) (T b)+product (H a) (H (flip b)) := by
  ext i j
  let F : ℤ → ℝ := fun k => a ((i : ℤ)-k)*b (k-j)
  have hF : Summable F := full_entry_summable ha hb i j
  have hp : Summable (fun n : ℕ => F n) := hF.comp_injective Nat.cast_injective
  have hn : Summable (fun n : ℕ => F (-((n+1 : ℕ) : ℤ))) :=
    hF.comp_injective (by intro m n h; dsimp only at h; omega)
  have hsplit := tsum_of_nat_of_neg_add_one hp hn
  have hneg (k : ℕ) : F (-((k+1 : ℕ) : ℤ))=H a i k*H (flip b) k j := by
    dsimp only [F,H,hankelOffset,ToeplitzHankelKernels.flip]
    congr 1 <;> congr 1 <;> omega
  change convolution a b ((i : ℤ)-j)=_
  rw [convolution_shift]
  change (∑' k : ℤ,F k)=_
  rw [hsplit]
  simp only [Pi.add_apply,product]
  congr 1
  apply tsum_congr
  intro k
  simpa only [Nat.cast_add,Nat.cast_one] using hneg k

theorem difference_summable {a b : Laurent}
    (ha : Summable (fun n => |a n|)) (hb : Summable (fun n => |b n|)) (x y : ℤ) :
    Summable (fun k : ℤ => a (x-k)*(b (k-y)-b (k+y))) := by
  have hs := (full_entry_summable ha hb x y).sub (full_entry_summable ha hb x (-y))
  convert hs using 1
  funext k
  simp only [sub_neg_eq_add]
  ring

theorem difference_tsum {a b : Laurent}
    (ha : Summable (fun n => |a n|)) (hb : Summable (fun n => |b n|)) (x y : ℤ) :
    (∑' k : ℤ,a (x-k)*(b (k-y)-b (k+y)))=
      convolution a b (x-y)-convolution a b (x+y) := by
  have hs : Summable (fun k : ℤ => a (x-k)*b (k+y)) := by
    simpa only [sub_neg_eq_add] using full_entry_summable ha hb x (-y)
  simp only [mul_sub]
  rw [(full_entry_summable ha hb x y).tsum_sub hs]
  rw [convolution_shift a b x y]
  have hright : convolution a b (x+y)=∑' k : ℤ,a (x-k)*b (k+y) := by
    simpa only [sub_neg_eq_add] using convolution_shift a b x (-y)
  rw [hright]

/-- Reflection about index minus one accounts for the shift by two.
Only the right coefficient sequence is required to be even. -/
theorem M_convolution {a b : Laurent}
    (ha : Summable (fun n => |a n|)) (hb : Summable (fun n => |b n|))
    (he : Function.Even b) : product (M a) (M b)=M (convolution a b) := by
  ext i j
  let x : ℤ := (i : ℤ)+1
  let y : ℤ := (j : ℤ)+1
  let F : ℤ → ℝ := fun k => a (x-k)*(b (k-y)-b (k+y))
  have hF : Summable F := difference_summable ha hb x y
  have hp : Summable (fun n : ℕ => F ((n+1 : ℕ) : ℤ)) :=
    hF.comp_injective (by intro m n h; dsimp only at h; omega)
  have hn : Summable (fun n : ℕ => F (-((n+1 : ℕ) : ℤ))) :=
    hF.comp_injective (by intro m n h; dsimp only at h; omega)
  have hsplit := tsum_of_add_one_of_neg_add_one hp hn
  have hzero : F 0=0 := by
    dsimp only [F]
    rw [zero_sub,zero_add,he y,sub_self,mul_zero]
  have hpos (k : ℕ) : F ((k+1 : ℕ) : ℤ)=
      a ((i : ℤ)-k)*(b ((k : ℤ)-j)-b ((k+j+2 : ℕ) : ℤ)) := by
    dsimp only [F,x,y]
    congr 1
    · congr 1
      omega
    · congr 1 <;> congr 1 <;> omega
  have hneg (k : ℕ) : F (-((k+1 : ℕ) : ℤ))=
      a ((i+k+2 : ℕ) : ℤ)*(b ((k+j+2 : ℕ) : ℤ)-b ((k : ℤ)-j)) := by
    have h1 : x-(-((k+1 : ℕ) : ℤ))=((i+k+2 : ℕ) : ℤ) := by dsimp [x]; omega
    have h2 : -((k+1 : ℕ) : ℤ)-y= -((k+j+2 : ℕ) : ℤ) := by dsimp [y]; omega
    have h3 : -((k+1 : ℕ) : ℤ)+y= -((k : ℤ)-j) := by dsimp [y]; omega
    dsimp only [F]
    rw [h1,h2,h3,he ((k+j+2 : ℕ) : ℤ),he ((k : ℤ)-j)]
  have hpair (k : ℕ) : M a i k*M b k j=F ((k+1 : ℕ) : ℤ)+F (-((k+1 : ℕ) : ℤ)) := by
    rw [hpos,hneg]
    dsimp only [M,T,Hshift,hankelOffset,Pi.sub_apply]
    ring
  have htotal : product (M a) (M b) i j=∑' k : ℤ,F k := by
    unfold product
    simp_rw [hpair]
    rw [hp.tsum_add hn]
    rw [hsplit,hzero,add_zero]
    simp only [Nat.cast_add,Nat.cast_one]
  rw [htotal]
  change (∑' k : ℤ,a (x-k)*(b (k-y)-b (k+y)))=
    convolution a b ((i : ℤ)-j)-convolution a b ((i+j+2 : ℕ) : ℤ)
  rw [difference_tsum ha hb x y]
  congr 1 <;> congr 1 <;> dsimp [x,y] <;> omega

theorem toeplitz_convolution_weighted {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b) :
    T (convolution a b)=product (T a) (T b)+product (H a) (H (flip b)) :=
  toeplitz_convolution (summable_abs ha) (summable_abs hb)

theorem toeplitz_defect_summable {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b) :
    Summable (AbsolutelySummableDeterminant.entryNorm
      (T (convolution a b)-product (T a) (T b))) := by
  have he : T (convolution a b)-product (T a) (T b)=product (H a) (H (flip b)) := by
    rw [toeplitz_convolution_weighted ha hb]
    abel
  rw [he]
  exact product_summable (H_summable ha) (H_summable (weighted_flip hb))

theorem toeplitz_commutator {a b : Laurent}
    (ha : Summable (fun n => |a n|)) (hb : Summable (fun n => |b n|)) :
    product (T a) (T b)-product (T b) (T a)=
      product (H b) (H (flip a))-product (H a) (H (flip b)) := by
  ext i j
  have h1 := congrFun (congrFun (toeplitz_convolution ha hb) i) j
  have h2 := congrFun (congrFun (toeplitz_convolution hb ha) i) j
  rw [convolution_comm a b] at h1
  simp only [Pi.add_apply] at h1 h2
  change product (T a) (T b) i j-product (T b) (T a) i j=_
  change _=product (H b) (H (flip a)) i j-product (H a) (H (flip b)) i j
  linarith only [h1,h2]

theorem M_convolution_weighted {a b : Laurent} (ha : WeightedSummable a) (hb : WeightedSummable b)
    (he : Function.Even b) : product (M a) (M b)=M (convolution a b) :=
  M_convolution (summable_abs ha) (summable_abs hb) he

end
end SpanningTreeIsoperimetry.ToeplitzHankelConvolution
