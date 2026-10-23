module

public import SpanningTreeIsoperimetry.EnhancedBoundary

@[expose] public section

/-! Empty-vacancy endpoints of the enhanced hull estimate. -/
namespace SpanningTreeIsoperimetry

open SquareMaximality SquareMaximality.Boundary SquareMaximality.Windows

theorem canonicalInteriorCount_zero_of_no_vacancies {R S : ℕ} {A : Finset Point}
    (hV : encodedVacancies R S A=∅) : canonicalInteriorCount R S A=0 := by
  by_contra hz
  let i : Fin (canonicalInteriorCount R S A) := ⟨0,Nat.pos_of_ne_zero hz⟩
  let c := (canonicalInteriorEquiv R S A).symm i
  obtain ⟨p,hp⟩ := interiorComponent_nonempty R S (canonicalVacancies R S A) c
  obtain ⟨hpV,_⟩ := mem_interiorComponent.mp hp
  change p ∈ encodedVacancies R S A at hpV
  simpa only [hV,Finset.notMem_empty] using hpV

theorem boundaryGapCount_zero_of_no_vacancies {R S : ℕ} {A : Finset Point}
    (hV : encodedVacancies R S A=∅) : EnhancedBoundary.boundaryGapCount R S A=0 := by
  have hB : boundaryVacancies R S (encodedVacancies R S A)=∅ := by
    apply Finset.subset_empty.mp
    simpa only [hV] using boundaryVacancies_subset R S (encodedVacancies R S A)
  simp [EnhancedBoundary.boundaryGapCount,hB,horizontalInternalRunCount,
    verticalInternalRunCount,row,column,internalRunStarts]

theorem encodedVacancies_full_rectangle (R S : ℕ) :
    encodedVacancies R S (SquareMaximality.rectangle 0 0 (R+1) (S+1))=∅ := by
  have h := image_encodedVacancies R S (SquareMaximality.rectangle 0 0 (R+1) (S+1))
  rw [Finset.sdiff_self] at h
  exact Finset.image_eq_empty.mp h

theorem vacancy_counts_full_rectangle (R S : ℕ) :
    EnhancedBoundary.boundaryGapCount R S (SquareMaximality.rectangle 0 0 (R+1) (S+1))=0 ∧
      canonicalInteriorCount R S (SquareMaximality.rectangle 0 0 (R+1) (S+1))=0 :=
  ⟨boundaryGapCount_zero_of_no_vacancies (encodedVacancies_full_rectangle R S),
    canonicalInteriorCount_zero_of_no_vacancies (encodedVacancies_full_rectangle R S)⟩

end SpanningTreeIsoperimetry
