import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A dimension-independent finite determinant continuity estimate.
The entrywise absolute-sum norm is the only matrix size parameter. This is
intended for finite sections of absolutely summable corner kernels. -/
namespace SpanningTreeIsoperimetry.FiniteDeterminantContinuity
open Matrix
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rowMass (A : Matrix ι ι ℝ) (i : ι) : ℝ := ∑ j,|A i j|
def mass (A : Matrix ι ι ℝ) : ℝ := ∑ i,rowMass A i

theorem rowMass_nonneg (A : Matrix ι ι ℝ) (i : ι) : 0≤rowMass A i :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem mass_nonneg (A : Matrix ι ι ℝ) : 0≤mass A :=
  Finset.sum_nonneg (fun _ _ => rowMass_nonneg A _)

/-- The elementary row-sum determinant estimate, obtained directly from
Leibniz and the inclusion of permutations among all functions. -/
theorem abs_det_le_prod_rowMass (A : Matrix ι ι ℝ) : |A.det|≤∏ i,rowMass A i := by
  have hc (B : Matrix ι ι ℝ) : |B.det|≤∏ j,∑ i,|B i j| := by
    rw [Matrix.det_apply']
    calc
      |∑ σ : Equiv.Perm ι,((Equiv.Perm.sign σ : ℤ) : ℝ)*∏ i,B (σ i) i|
          ≤∑ σ : Equiv.Perm ι,|((Equiv.Perm.sign σ : ℤ) : ℝ)*∏ i,B (σ i) i| :=
        Finset.abs_sum_le_sum_abs _ _
      _=∑ σ : Equiv.Perm ι,∏ i,|B (σ i) i| := by
        apply Finset.sum_congr rfl
        intro σ _
        have hs : |((Equiv.Perm.sign σ : ℤ) : ℝ)|=1 := by exact_mod_cast Equiv.Perm.sign_abs σ
        rw [abs_mul,hs,one_mul,Finset.abs_prod]
      _≤∑ f : ι → ι,∏ i,|B (f i) i| := by
        apply Finset.sum_le_sum_of_injOn (fun σ : Equiv.Perm ι => (σ : ι → ι))
        · intro σ _ τ _ h
          exact Equiv.ext (congrFun h)
        · exact Finset.subset_univ _
        · intro σ _
          exact le_refl _
        · intro f _ _
          exact Finset.prod_nonneg (fun _ _ => abs_nonneg _)
      _=∏ j,∑ i,|B i j| := (Fintype.prod_sum (fun j i => |B i j|)).symm
  simpa only [Matrix.det_transpose,Matrix.transpose_apply,rowMass] using hc A.transpose

theorem rowMass_one_add (A : Matrix ι ι ℝ) (i : ι) : rowMass (1+A) i≤1+rowMass A i := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset ι))
    (fun j _ => abs_add_le ((1 : Matrix ι ι ℝ) i j) (A i j))
  simpa [rowMass,Matrix.add_apply,Matrix.one_apply,Finset.sum_add_distrib,apply_ite,eq_comm] using h

private theorem product_row_bound (A B : Matrix ι ι ℝ) (s : Finset ι) :
    (∏ i∈s,(1+rowMass A i+rowMass B i))≤Real.exp (mass A+mass B) := by
  calc
    (∏ i∈s,(1+rowMass A i+rowMass B i))≤∏ i∈s,Real.exp (rowMass A i+rowMass B i) := by
      apply Finset.prod_le_prod₀
      · intro i _
        linarith [rowMass_nonneg A i,rowMass_nonneg B i]
      · intro i _
        have h := Real.add_one_le_exp (rowMass A i+rowMass B i)
        linarith
    _=Real.exp (∑ i∈s,(rowMass A i+rowMass B i)) := (Real.exp_sum s _).symm
    _≤Real.exp (mass A+mass B) := by
      apply Real.exp_le_exp.mpr
      have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun i _ _ => add_nonneg (rowMass_nonneg A i) (rowMass_nonneg B i))
      simpa only [Finset.sum_add_distrib,mass] using h

variable [LinearOrder ι]

def blendRows (A B : Matrix ι ι ℝ) (k : ι) : Matrix ι ι ℝ := fun i =>
  if i<k then (1+A) i else if i=k then (1+A) i-(1+B) i else (1+B) i

theorem det_sub_eq_sum_blendRows (A B : Matrix ι ι ℝ) :
    (1+A).det-(1+B).det=∑ k,(blendRows A B k).det := by
  have h := (Matrix.detRowAlternating.toMultilinearMap : MultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ).map_piecewise_sub_map_piecewise (fun i => ((1 : Matrix ι ι ℝ)+A) i) (fun i => ((1 : Matrix ι ι ℝ)+B) i) (fun i => ((1 : Matrix ι ι ℝ)+A) i) Finset.univ
  simp only [Finset.piecewise_univ,Finset.mem_univ,ite_true] at h
  convert h using 1 <;> try rfl
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  funext i
  dsimp only [blendRows]
  split_ifs <;> rfl

theorem rowMass_blend_self (A B : Matrix ι ι ℝ) (k : ι) :
    rowMass (blendRows A B k) k=rowMass (A-B) k := by
  unfold rowMass
  apply Finset.sum_congr rfl
  intro j _
  simp only [blendRows,lt_self_iff_false,ite_false,ite_true,Pi.sub_apply,Matrix.add_apply,Matrix.sub_apply]
  congr 1
  ring

theorem rowMass_blend_other (A B : Matrix ι ι ℝ) {i k : ι} (hik : i≠k) :
    rowMass (blendRows A B k) i≤1+rowMass A i+rowMass B i := by
  by_cases hil : i<k
  · have he : rowMass (blendRows A B k) i=rowMass (1+A) i := by simp only [rowMass,blendRows,hil,ite_true]
    rw [he]
    linarith [rowMass_one_add A i,rowMass_nonneg B i]
  · have he : rowMass (blendRows A B k) i=rowMass (1+B) i := by simp only [rowMass,blendRows,hil,hik,ite_false]
    rw [he]
    linarith [rowMass_one_add B i,rowMass_nonneg A i]

theorem abs_det_blendRows_le (A B : Matrix ι ι ℝ) (k : ι) :
    |(blendRows A B k).det|≤rowMass (A-B) k*Real.exp (mass A+mass B) := by
  calc
    |(blendRows A B k).det|≤∏ i,rowMass (blendRows A B k) i := abs_det_le_prod_rowMass _
    _=rowMass (A-B) k*(∏ i∈Finset.univ.erase k,rowMass (blendRows A B k) i) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),rowMass_blend_self]
    _≤rowMass (A-B) k*(∏ i∈Finset.univ.erase k,(1+rowMass A i+rowMass B i)) := by
      apply mul_le_mul_of_nonneg_left _ (rowMass_nonneg _ _)
      apply Finset.prod_le_prod₀
      · exact fun i _ => rowMass_nonneg _ i
      · intro i hi
        exact rowMass_blend_other A B (Finset.mem_erase.mp hi).1
    _≤rowMass (A-B) k*Real.exp (mass A+mass B) :=
      mul_le_mul_of_nonneg_left (product_row_bound A B _) (rowMass_nonneg _ _)

/-- The bound is independent of the number of rows. It is therefore usable
when two finite sections are compared after zero-padding the smaller one. -/
theorem determinant_continuity (A B : Matrix ι ι ℝ) :
    |(1+A).det-(1+B).det|≤mass (A-B)*Real.exp (mass A+mass B) := by
  rw [det_sub_eq_sum_blendRows]
  calc
    |∑ k,(blendRows A B k).det|≤∑ k,|(blendRows A B k).det| := Finset.abs_sum_le_sum_abs _ _
    _≤∑ k,rowMass (A-B) k*Real.exp (mass A+mass B) :=
      Finset.sum_le_sum (fun k _ => abs_det_blendRows_le A B k)
    _=mass (A-B)*Real.exp (mass A+mass B) := by rw [← Finset.sum_mul]; rfl

end
end SpanningTreeIsoperimetry.FiniteDeterminantContinuity
