import SpanningTreeIsoperimetry.SummableKernelProduct

/-! Direct-sum algebra for entrywise summable real kernels. No general
operator or Banach algebra instance is introduced. -/
namespace SpanningTreeIsoperimetry.SummableKernelAlgebra
open SummableKernelProduct AbsolutelySummableDeterminant
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem add_summable {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) : Summable (entryNorm (A+B)) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ (hA.add hB)
  intro p
  exact abs_add_le _ _

theorem product_zero (A : Kernel) : product A 0=0 := by
  ext i j
  simp [product]

theorem zero_product (A : Kernel) : product 0 A=0 := by
  ext i j
  simp [product]

theorem product_add_left {A B C : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (hC : Summable (entryNorm C)) :
    product (A+B) C=product A C+product B C := by
  ext i j
  simp only [product,Pi.add_apply,add_mul]
  exact (productEntry_summable hA hC i j).tsum_add (productEntry_summable hB hC i j)

theorem product_add_right {A B C : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (hC : Summable (entryNorm C)) :
    product A (B+C)=product A B+product A C := by
  ext i j
  simp only [product,Pi.add_apply,mul_add]
  exact (productEntry_summable hA hB i j).tsum_add (productEntry_summable hA hC i j)

theorem product_sub_left {A B C : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (hC : Summable (entryNorm C)) :
    product (A-B) C=product A C-product B C := by
  ext i j
  simp only [product,Pi.sub_apply,sub_mul]
  exact (productEntry_summable hA hC i j).tsum_sub (productEntry_summable hB hC i j)

theorem product_sub_right {A B C : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (hC : Summable (entryNorm C)) :
    product A (B-C)=product A B-product A C := by
  ext i j
  simp only [product,Pi.sub_apply,mul_sub]
  exact (productEntry_summable hA hB i j).tsum_sub (productEntry_summable hA hC i j)

theorem product_smul_left (r : ℝ) (A B : Kernel) : product (r • A) B=r • product A B := by
  ext i j
  simp only [product,Pi.smul_apply,smul_eq_mul,mul_assoc,tsum_mul_left]

theorem product_smul_right (r : ℝ) (A B : Kernel) : product A (r • B)=r • product A B := by
  ext i j
  simp only [product,Pi.smul_apply,smul_eq_mul]
  have he : (fun k => A i k*(r*B k j))=(fun k => r*(A i k*B k j)) := by
    funext k
    ring
  rw [he,tsum_mul_left]

theorem entry_le_totalMass {A : Kernel} (hA : Summable (entryNorm A)) (i j : ℕ) :
    |A i j| ≤ totalMass A := hA.le_tsum (i,j) (fun _ _ => abs_nonneg _)

/-- Absolute convergence of the double sum which justifies associativity. -/
theorem triple_pair_summable {A B C : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (hC : Summable (entryNorm C)) (i l : ℕ) :
    Summable (fun p : ℕ×ℕ => A i p.1*B p.1 p.2*C p.2 l) := by
  let f : ℕ×ℕ → ℝ := fun p => A i p.1*B p.1 p.2*C p.2 l
  have hs := (row_summable hA i).mul_of_nonneg (column_summable hC l)
    (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
  have hm : Summable (fun p : ℕ×ℕ => totalMass B*(|A i p.1| *|C p.2 l|)) := hs.mul_left (totalMass B)
  have hf : Summable (fun p => ‖f p‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hm
    intro p
    rw [Real.norm_eq_abs]
    dsimp only [f]
    rw [abs_mul,abs_mul]
    calc
      |A i p.1| *|B p.1 p.2| *|C p.2 l|=(|A i p.1| *|C p.2 l|)*|B p.1 p.2| := by ring
      _ ≤ (|A i p.1| *|C p.2 l|)*totalMass B :=
        mul_le_mul_of_nonneg_left (entry_le_totalMass hB _ _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _=totalMass B*(|A i p.1| *|C p.2 l|) := by ring
  exact hf.of_norm

theorem product_assoc {A B C : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (hC : Summable (entryNorm C)) :
    product (product A B) C=product A (product B C) := by
  ext i l
  have hf := triple_pair_summable hA hB hC i l
  calc
    product (product A B) C i l=(∑' k,∑' j,A i j*B j k*C k l) := by
      simp only [product,tsum_mul_right]
    _=(∑' j,∑' k,A i j*B j k*C k l) := hf.tsum_comm
    _=product A (product B C) i l := by simp only [product,mul_assoc,tsum_mul_left]

theorem compose_eq_add (A B : Kernel) : composePerturbation A B=A+B+product A B := rfl

theorem compose_zero_left (A : Kernel) : composePerturbation 0 A=A := by
  rw [compose_eq_add,zero_product]
  simp

theorem compose_zero_right (A : Kernel) : composePerturbation A 0=A := by
  rw [compose_eq_add,product_zero]
  simp

theorem compose_assoc {A B C : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (hC : Summable (entryNorm C)) :
    composePerturbation (composePerturbation A B) C=composePerturbation A (composePerturbation B C) := by
  simp only [compose_eq_add]
  rw [product_add_left (add_summable hA hB) (product_summable hA hB) hC,
    product_add_left hA hB hC,
    product_add_right hA (add_summable hB hC) (product_summable hB hC),
    product_add_right hA hB hC,product_assoc hA hB hC]
  abel

/-- Cancellation uses the stated inverse equation; it is not inferred from
summability or from a one-sided operator argument. -/
theorem compose_left_cancel_of_left_inverse {A B C D : Kernel}
    (hA : Summable (entryNorm A)) (hB : Summable (entryNorm B))
    (hC : Summable (entryNorm C)) (hD : Summable (entryNorm D))
    (hBA : composePerturbation B A=0)
    (he : composePerturbation A C=composePerturbation A D) : C=D := by
  have h := congrArg (fun K => composePerturbation B K) he
  rw [← compose_assoc hB hA hC,← compose_assoc hB hA hD,hBA,
    compose_zero_left,compose_zero_left] at h
  exact h

theorem compose_right_cancel_of_right_inverse {A B C D : Kernel}
    (hA : Summable (entryNorm A)) (hB : Summable (entryNorm B))
    (hC : Summable (entryNorm C)) (hD : Summable (entryNorm D))
    (hAB : composePerturbation A B=0)
    (he : composePerturbation C A=composePerturbation D A) : C=D := by
  have h := congrArg (fun K => composePerturbation K B) he
  rw [compose_assoc hC hA hB,compose_assoc hD hA hB,hAB,
    compose_zero_right,compose_zero_right] at h
  exact h

theorem left_right_inverse_unique {A B C : Kernel}
    (hA : Summable (entryNorm A)) (hB : Summable (entryNorm B)) (hC : Summable (entryNorm C))
    (hBA : composePerturbation B A=0) (hAC : composePerturbation A C=0) : B=C := by
  have h := compose_assoc hB hA hC
  rw [hBA,hAC,compose_zero_left,compose_zero_right] at h
  exact h.symm

end
end SpanningTreeIsoperimetry.SummableKernelAlgebra
