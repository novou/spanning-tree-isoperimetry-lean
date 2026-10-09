import SpanningTreeIsoperimetry.BoundedKernelAlgebra

/-! Distribution of actual kernel products with absolute convergence
justified by explicit row bounds. -/
namespace SpanningTreeIsoperimetry.BoundedKernelLinear
open BoundedKernelProduct BoundedKernelAlgebra SummableKernelProduct
noncomputable section

theorem rowBound_add {A B : Kernel} {a b : ℝ} (hA : RowBound A a) (hB : RowBound B b) :
    RowBound (A+B) (a+b) := by
  have hs (i : ℕ) : Summable (fun j => |(A+B) i j|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun j => abs_add_le _ _)
      ((hA.summable i).add (hB.summable i))
  refine ⟨add_nonneg hA.nonneg hB.nonneg,hs,?_⟩
  intro i
  have h := (hs i).tsum_le_tsum (fun j => abs_add_le (A i j) (B i j))
    ((hA.summable i).add (hB.summable i))
  rw [(hA.summable i).tsum_add (hB.summable i)] at h
  exact h.trans (add_le_add (hA.bound i) (hB.bound i))

theorem rowBound_neg {A : Kernel} {a : ℝ} (hA : RowBound A a) : RowBound (-A) a := by
  refine ⟨hA.nonneg,?_,?_⟩
  · intro i
    simpa only [Pi.neg_apply,abs_neg] using hA.summable i
  · intro i
    simpa only [rowNorm,Pi.neg_apply,abs_neg] using hA.bound i

theorem rowBound_sub {A B : Kernel} {a b : ℝ} (hA : RowBound A a) (hB : RowBound B b) :
    RowBound (A-B) (a+b) := by
  simpa only [sub_eq_add_neg] using rowBound_add hA (rowBound_neg hB)

theorem entry_summable {A B : Kernel} {a b : ℝ} (hA : RowBound A a) (hB : RowBound B b)
    (i j : ℕ) : Summable (fun k => A i k*B k j) :=
  (entry_product_summable hA hB i j).of_abs

theorem product_add_left {A B D : Kernel} {a b d : ℝ}
    (hA : RowBound A a) (hB : RowBound B b) (hD : RowBound D d) :
    product (A+B) D=product A D+product B D := by
  ext i j
  simp only [product,Pi.add_apply,add_mul]
  exact (entry_summable hA hD i j).tsum_add (entry_summable hB hD i j)

theorem product_add_right {A B D : Kernel} {a b d : ℝ}
    (hA : RowBound A a) (hB : RowBound B b) (hD : RowBound D d) :
    product A (B+D)=product A B+product A D := by
  ext i j
  simp only [product,Pi.add_apply,mul_add]
  exact (entry_summable hA hB i j).tsum_add (entry_summable hA hD i j)

theorem product_sub_left {A B D : Kernel} {a b d : ℝ}
    (hA : RowBound A a) (hB : RowBound B b) (hD : RowBound D d) :
    product (A-B) D=product A D-product B D := by
  ext i j
  simp only [product,Pi.sub_apply,sub_mul]
  exact (entry_summable hA hD i j).tsum_sub (entry_summable hB hD i j)

theorem product_sub_right {A B D : Kernel} {a b d : ℝ}
    (hA : RowBound A a) (hB : RowBound B b) (hD : RowBound D d) :
    product A (B-D)=product A B-product A D := by
  ext i j
  simp only [product,Pi.sub_apply,mul_sub]
  exact (entry_summable hA hB i j).tsum_sub (entry_summable hA hD i j)

theorem product_neg_left (A B : Kernel) : product (-A) B= -product A B := by
  ext i j
  simp only [product,Pi.neg_apply,neg_mul,tsum_neg]

theorem product_neg_right (A B : Kernel) : product A (-B)= -product A B := by
  ext i j
  simp only [product,Pi.neg_apply,mul_neg,tsum_neg]

end
end SpanningTreeIsoperimetry.BoundedKernelLinear
