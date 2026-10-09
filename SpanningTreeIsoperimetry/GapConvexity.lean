import SpanningTreeIsoperimetry.EnhancedBoundary
import SpanningTreeIsoperimetry.FoundationsBridge

/-! Vanishing vacancy-gap counts give actual row and column convexity.
This is the geometric final step after the integer-defect comparison. -/
namespace SpanningTreeIsoperimetry

open SquareMaximality.Windows SquareMaximality.Boundary

theorem complement_interval_of_no_internal_runs {L : ℕ} {B : Finset ℕ}
    (hzero : (internalRunStarts L B).card = 0) {x z y : ℕ}
    (hx : x ∉ B) (hy : y ∉ B) (hyL : y ≤ L) (hxz : x ≤ z) (hzy : z ≤ y) : z ∉ B := by
  intro hz
  let T := (Finset.Icc x z).filter (fun a => a ∈ B)
  have hT : T.Nonempty := ⟨z,by simp [T,hxz,hz]⟩
  let a := T.min' hT
  have ha : a ∈ T := Finset.min'_mem T hT
  have hax : x ≤ a ∧ a ≤ z ∧ a ∈ B := by
    simpa only [T,Finset.mem_filter,Finset.mem_Icc,and_assoc] using ha
  have hxa : x < a := by
    by_contra h
    have : a=x := by omega
    exact hx (this ▸ hax.2.2)
  have hpred : a-1 ∉ B := by
    intro hp
    have hpT : a-1 ∈ T := by simp [T,hp]; omega
    have hmin := Finset.min'_le T (a-1) hpT
    change a ≤ a-1 at hmin
    omega
  have hright : a ∉ rightBoundaryRun L B := by
    intro hr
    have hsub := (mem_rightBoundaryRun.mp hr).2
    exact hy (hsub (Finset.mem_Icc.mpr ⟨by omega,hyL⟩))
  have hi : a ∈ internalRunStarts L B :=
    mem_internalRunStarts.mpr ⟨by omega,by omega,hax.2.2,hpred,hright⟩
  have he := Finset.card_eq_zero.mp hzero
  simpa only [he,Finset.notMem_empty] using hi

theorem rowConvex_of_encoded_gaps_zero {A : Domain} {R S : ℕ}
    (hsub : A ⊆ rectangle (R+1) (S+1))
    (hzero : horizontalInternalRunCount R S (encodedVacancies R S A) = 0) :
    IsRowConvex A := by
  intro x₁ x x₂ y h₁ h₂ hl hu
  have hb₁ := mem_rectangle.mp (hsub h₁)
  have hb₂ := mem_rectangle.mp (hsub h₂)
  have hx₀ : 0 ≤ x := by omega
  have hy₀ : 0 ≤ y := hb₁.2.2.1
  have hyS : y.toNat ≤ S := by omega
  have hsum := Finset.single_le_sum
    (s := line S) (f := fun v => (internalRunStarts R
      (row R (encodedVacancies R S A) v)).card)
    (fun _ _ => Nat.zero_le _) (mem_line.mpr hyS)
  have hz : (internalRunStarts R (row R (encodedVacancies R S A) y.toNat)).card=0 := by
    change _ ≤ horizontalInternalRunCount R S (encodedVacancies R S A) at hsum
    omega
  have hleft : x₁.toNat ∉ row R (encodedVacancies R S A) y.toNat := by
    intro hm
    have hnot := (mem_encodedVacancies.mp (mem_row.mp hm).2).2.2
    exact hnot (by simpa [ofNatPoint,Int.toNat_of_nonneg hb₁.1,
      Int.toNat_of_nonneg hy₀] using h₁)
  have hright : x₂.toNat ∉ row R (encodedVacancies R S A) y.toNat := by
    intro hm
    have hnot := (mem_encodedVacancies.mp (mem_row.mp hm).2).2.2
    exact hnot (by simpa [ofNatPoint,Int.toNat_of_nonneg hb₂.1,
      Int.toNat_of_nonneg hy₀] using h₂)
  have hxnot := complement_interval_of_no_internal_runs hz hleft hright
    (by omega : x₂.toNat ≤ R) (by omega : x₁.toNat ≤ x.toNat) (by omega : x.toNat ≤ x₂.toNat)
  by_contra hx
  apply hxnot
  apply mem_row.mpr
  refine ⟨by omega,mem_encodedVacancies.mpr ⟨by omega,hyS,?_⟩⟩
  simpa [ofNatPoint,Int.toNat_of_nonneg hx₀,Int.toNat_of_nonneg hy₀] using hx

theorem columnConvex_of_encoded_gaps_zero {A : Domain} {R S : ℕ}
    (hsub : A ⊆ rectangle (R+1) (S+1))
    (hzero : verticalInternalRunCount R S (encodedVacancies R S A) = 0) :
    IsColumnConvex A := by
  intro x y₁ y y₂ h₁ h₂ hl hu
  have hb₁ := mem_rectangle.mp (hsub h₁)
  have hb₂ := mem_rectangle.mp (hsub h₂)
  have hy₀ : 0 ≤ y := by omega
  have hx₀ : 0 ≤ x := hb₁.1
  have hxR : x.toNat ≤ R := by omega
  have hsum := Finset.single_le_sum
    (s := line R) (f := fun v => (internalRunStarts S
      (column S (encodedVacancies R S A) v)).card)
    (fun _ _ => Nat.zero_le _) (mem_line.mpr hxR)
  have hz : (internalRunStarts S (column S (encodedVacancies R S A) x.toNat)).card=0 := by
    change _ ≤ verticalInternalRunCount R S (encodedVacancies R S A) at hsum
    omega
  have hbottom : y₁.toNat ∉ column S (encodedVacancies R S A) x.toNat := by
    intro hm
    have hnot := (mem_encodedVacancies.mp (mem_column.mp hm).2).2.2
    exact hnot (by simpa [ofNatPoint,Int.toNat_of_nonneg hb₁.2.2.1,
      Int.toNat_of_nonneg hx₀] using h₁)
  have htop : y₂.toNat ∉ column S (encodedVacancies R S A) x.toNat := by
    intro hm
    have hnot := (mem_encodedVacancies.mp (mem_column.mp hm).2).2.2
    exact hnot (by simpa [ofNatPoint,Int.toNat_of_nonneg hb₂.2.2.1,
      Int.toNat_of_nonneg hx₀] using h₂)
  have hynot := complement_interval_of_no_internal_runs hz hbottom htop
    (by omega : y₂.toNat ≤ S) (by omega : y₁.toNat ≤ y.toNat) (by omega : y.toNat ≤ y₂.toNat)
  by_contra hy
  apply hynot
  apply mem_column.mpr
  refine ⟨by omega,mem_encodedVacancies.mpr ⟨hxR,by omega,?_⟩⟩
  simpa [ofNatPoint,Int.toNat_of_nonneg hx₀,Int.toNat_of_nonneg hy₀] using hy

theorem boundaryVacancies_eq_all_of_no_interior {A : Domain} {R S : ℕ}
    (hzero : canonicalInteriorCount R S A=0) :
    boundaryVacancies R S (encodedVacancies R S A) = encodedVacancies R S A := by
  classical
  haveI : IsEmpty (Fin (canonicalInteriorCount R S A)) := by rw [hzero]; infer_instance
  have hpart := canonical_partition R S A
  simp only [Finset.univ_eq_empty,Finset.biUnion_empty,Finset.union_empty] at hpart
  apply Finset.image_injective ofNatPoint_injective
  change canonicalBoundary R S A = _
  rw [image_encodedVacancies]
  exact hpart.symm

/-- The two integer vacancy counts used in the hull comparison really force
interval rows and columns; this is not an additional geometric input. -/
theorem convex_of_zero_vacancy_defects {A : Domain} {R S : ℕ}
    (hsub : A ⊆ rectangle (R+1) (S+1))
    (hgap : EnhancedBoundary.boundaryGapCount R S A=0)
    (hinterior : canonicalInteriorCount R S A=0) :
    IsRowConvex A ∧ IsColumnConvex A := by
  unfold EnhancedBoundary.boundaryGapCount at hgap
  rw [boundaryVacancies_eq_all_of_no_interior hinterior] at hgap
  exact ⟨rowConvex_of_encoded_gaps_zero hsub (by omega),
    columnConvex_of_encoded_gaps_zero hsub (by omega)⟩

end SpanningTreeIsoperimetry
