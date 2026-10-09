import SpanningTreeIsoperimetry.SummableKernelProduct

/-! The missing inner-index tail in a product of two actual finite sections. -/
namespace SpanningTreeIsoperimetry.SummableKernelProductTail
open SummableKernelProduct AbsolutelySummableDeterminant FiniteSectionPadding FiniteDeterminantContinuity
open scoped BigOperators
noncomputable section

def shiftColumns (A : Kernel) (n : ℕ) : Kernel := fun i k => A i (k+n)
def shiftRows (B : Kernel) (n : ℕ) : Kernel := fun k j => B (k+n) j

def productRemainder (A B : Kernel) (n : ℕ) : Kernel := product (shiftColumns A n) (shiftRows B n)

private theorem shiftColumns_injective (n : ℕ) :
    Function.Injective (fun p : ℕ×ℕ => (p.1,p.2+n)) := by
  intro p q hpq
  change (p.1,p.2+n)=(q.1,q.2+n) at hpq
  have h := Prod.mk.inj hpq
  exact Prod.ext h.1 (Nat.add_right_cancel h.2)

private theorem shiftRows_injective (n : ℕ) :
    Function.Injective (fun p : ℕ×ℕ => (p.1+n,p.2)) := by
  intro p q hpq
  change (p.1+n,p.2)=(q.1+n,q.2) at hpq
  have h := Prod.mk.inj hpq
  exact Prod.ext (Nat.add_right_cancel h.1) h.2

theorem shiftColumns_summable {A : Kernel} (hA : Summable (entryNorm A)) (n : ℕ) :
    Summable (entryNorm (shiftColumns A n)) := hA.comp_injective (shiftColumns_injective n)

theorem shiftRows_summable {A : Kernel} (hA : Summable (entryNorm A)) (n : ℕ) :
    Summable (entryNorm (shiftRows A n)) := hA.comp_injective (shiftRows_injective n)

theorem shiftColumns_mass_le_tail {A : Kernel} (hA : Summable (entryNorm A)) (n : ℕ) :
    totalMass (shiftColumns A n)≤tailMass A n := by
  apply Summable.tsum_le_tsum_of_inj (fun p : ℕ×ℕ => (p.1,p.2+n)) (shiftColumns_injective n)
    (fun p _ => tailEntry_nonneg A n p) _ (shiftColumns_summable hA n) (tailEntry_summable A hA n)
  intro p
  simp [entryNorm,shiftColumns,tailEntry,show n≤p.2+n by omega]

theorem shiftRows_mass_le {A : Kernel} (hA : Summable (entryNorm A)) (n : ℕ) :
    totalMass (shiftRows A n)≤totalMass A := by
  apply Summable.tsum_le_tsum_of_inj (fun p : ℕ×ℕ => (p.1+n,p.2)) (shiftRows_injective n)
    (fun p _ => abs_nonneg (A p.1 p.2)) _ (shiftRows_summable hA n) hA
  intro p
  exact le_refl _

theorem tailMass_le_total {A : Kernel} (hA : Summable (entryNorm A)) (n : ℕ) :
    tailMass A n≤totalMass A :=
  (tailEntry_summable A hA n).tsum_le_tsum (tailEntry_le A n) hA

theorem remainder_summable {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (n : ℕ) : Summable (entryNorm (productRemainder A B n)) :=
  product_summable (shiftColumns_summable hA n) (shiftRows_summable hB n)

theorem remainder_mass_le {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (n : ℕ) :
    totalMass (productRemainder A B n)≤tailMass A n*totalMass B := by
  have hp := product_mass_le (shiftColumns_summable hA n) (shiftRows_summable hB n)
  exact hp.trans (mul_le_mul (shiftColumns_mass_le_tail hA n) (shiftRows_mass_le hB n)
    (totalMass_nonneg _) (tsum_nonneg (tailEntry_nonneg A n)))

theorem product_split {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (n i j : ℕ) :
    (∑ k∈Finset.range n,A i k*B k j)+productRemainder A B n i j=product A B i j := by
  exact (productEntry_summable hA hB i j).sum_add_tsum_nat_add n

theorem finite_product_error {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (n : ℕ) :
    finiteSection (product A B) n-finiteSection A n*finiteSection B n=
      finiteSection (productRemainder A B n) n := by
  ext i j
  simp only [Matrix.sub_apply,Matrix.mul_apply,finiteSection]
  have h := product_split hA hB n i.val j.val
  rw [← Fin.sum_univ_eq_sum_range] at h
  linarith only [h]

theorem mass_section_le {A : Kernel} (hA : Summable (entryNorm A)) (n : ℕ) :
    mass (finiteSection A n)≤totalMass A := by
  have he : pad A n n=finiteSection A n := by
    ext i j
    simp [pad,finiteSection,i.is_lt,j.is_lt]
  simpa only [he] using mass_pad_le A hA n n

theorem finite_product_error_mass_le {A B : Kernel} (hA : Summable (entryNorm A))
    (hB : Summable (entryNorm B)) (n : ℕ) :
    mass (finiteSection (product A B) n-finiteSection A n*finiteSection B n)≤
      tailMass A n*totalMass B := by
  rw [finite_product_error hA hB]
  exact (mass_section_le (remainder_summable hA hB n) n).trans (remainder_mass_le hA hB n)

end
end SpanningTreeIsoperimetry.SummableKernelProductTail
