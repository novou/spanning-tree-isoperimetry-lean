import SpanningTreeIsoperimetry.FiniteDeterminantContinuity

/-! Zero-padding invariance for actual finite-section determinants. -/
namespace SpanningTreeIsoperimetry.FiniteSectionPadding
open Matrix FiniteDeterminantContinuity
open scoped BigOperators
noncomputable section

def finiteSection (K : ℕ → ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j => K i.val j.val

def pad (K : ℕ → ℕ → ℝ) (n m : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i.val<m ∧ j.val<m then K i.val j.val else 0

theorem det_pad_succ (K : ℕ → ℕ → ℝ) {m n : ℕ} (hm : m≤n) :
    (1+pad K (n+1) m).det=(1+pad K n m).det := by
  have hrow (j : Fin (n+1)) : (1+pad K (n+1) m) (Fin.last n) j=
      if j=Fin.last n then 1 else 0 := by
    simp [Matrix.add_apply,Matrix.one_apply,pad,Fin.val_last,show ¬n<m by omega,eq_comm]
  have hsub : (1+pad K (n+1) m).submatrix Fin.castSucc Fin.castSucc=1+pad K n m := by
    ext i j
    simp [Matrix.submatrix_apply,Matrix.add_apply,Matrix.one_apply,pad]
  have hs : (-1 : ℝ)^(n+n)=1 := by
    rw [show n+n=2*n by omega,pow_mul]
    norm_num
  rw [Matrix.det_succ_row _ (Fin.last n),Finset.sum_eq_single (Fin.last n)]
  · simp only [hrow,ite_true,Fin.val_last,hs,one_mul,mul_one,Fin.succAbove_last,hsub]
  · intro j _ hj
    simp only [hrow,ite_false,if_neg hj,mul_zero,zero_mul]
  · simp

theorem det_pad (K : ℕ → ℕ → ℝ) {m n : ℕ} (hm : m≤n) :
    (1+pad K n m).det=(1+finiteSection K m).det := by
  induction n,hm using Nat.le_induction with
  | base =>
    have he : pad K m m=finiteSection K m := by
      ext i j
      simp [pad,finiteSection,i.is_lt,j.is_lt]
    rw [he]
  | succ n hn ih => exact (det_pad_succ K hn).trans ih

/-- Two different section sizes can be compared inside the same finite
matrix, without introducing a dimension factor into the continuity bound. -/
theorem sections_difference_le (K : ℕ → ℕ → ℝ) {m n N : ℕ} (hm : m≤N) (hn : n≤N) :
    |(1+finiteSection K m).det-(1+finiteSection K n).det|≤
      mass (pad K N m-pad K N n)*Real.exp (mass (pad K N m)+mass (pad K N n)) := by
  rw [← det_pad K hm,← det_pad K hn]
  exact determinant_continuity _ _

end
end SpanningTreeIsoperimetry.FiniteSectionPadding
