import SpanningTreeIsoperimetry.GreenCornerReflection
import SpanningTreeIsoperimetry.CornerPrimalFaces

/-! Actual four-corner counts are bounded by the sum of the individual finite
corner energies. All placement, disjointness and cardinality inputs are proved. -/
namespace SpanningTreeIsoperimetry.FiniteCornerProducts
open Ferrers CornerEnergy CornerPrimalDomains SquareMaximality.Boundary
open GreenMinorProducts GreenCornerReflection CornerStripBridge
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def faceVacancyFit {R S : ℕ} (hR0 : 1≤R) (hS0 : 1≤S) {M : Corner → Diagram}
    (hM : ∀ c, IsFerrers (M c)) (hR : totalDefect M≤R) (hS : totalDefect M≤S) :
    fourCornerVacancies (R-1) (S-1) M⊆faceRectangle R S := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : R≠0)
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : S≠0)
  exact fourCorner_subset (ferrers_family_fit hM hR hS)

theorem face_vacancy_card {R S : ℕ} (hR0 : 1≤R) (hS0 : 1≤S) {M : Corner → Diagram}
    (hM : ∀ c, IsFerrers (M c)) (hR : totalDefect M≤R) (hS : totalDefect M≤S) :
    (fourCornerVacancies (R-1) (S-1) M).card=totalDefect M := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : R≠0)
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : S≠0)
  change (fourCornerVacancies r s M).card=totalDefect M
  rw [fourCornerVacancies,Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro c _
    exact placedCorner_card c (ferrers_family_fit hM hR hS c)
  · intro c _ d _ hcd
    exact placedCorner_disjoint hM hR hS hcd

theorem corner_energy_lower {R S : ℕ} (hR0 : 1≤R) (hS0 : 1≤S) {M : Corner → Diagram}
    (hM : ∀ c, IsFerrers (M c)) (hR : totalDefect M≤R) (hS : totalDefect M≤S) :
    (∑ c, dirichletEnergy (ferrers_family_fit hM hR hS c))≤
      dirichletEnergy (faceVacancyFit hR0 hS0 hM hR hS) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : R≠0)
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : S≠0)
  let P : Corner → Diagram := fun c => placedCorner r s c (M c)
  have hfit (c : Corner) : P c⊆faceRectangle (r+1) (s+1) :=
    placedCorner_subset c (ferrers_family_fit hM hR hS c)
  have hd : Pairwise fun c d => Disjoint (P c) (P d) :=
    fun _ _ hcd => placedCorner_disjoint hM hR hS hcd
  have h := dirichletEnergy_superadditive (Finset.Subset.refl (faceRectangle (r+1) (s+1))) P hfit hd
  have he (c : Corner) : dirichletEnergy (hfit c)=dirichletEnergy (ferrers_family_fit hM hR hS c) :=
    dirichletEnergy_reflected c (ferrers_family_fit hM hR hS c)
  simpa only [he] using h

theorem corner_count_eq_greenMinor {R S : ℕ} (hR0 : 1≤R) (hS0 : 1≤S) {M : Corner → Diagram}
    (hM : ∀ c, IsFerrers (M c)) (hR : totalDefect M≤R) (hS : totalDefect M≤S) :
    (treeCount (cornerPrimal R S M) : ℝ)=
      (treeCount (rectangle (R+1) (S+1)) : ℝ)*(greenMinor (faceVacancyFit hR0 hS0 hM hR hS)).det := by
  have hs := cornerPrimal_treeCount_eq_dirichlet hR0 hS0 hM hR hS
  rw [unmarkedFaces,markedFaces_fourCorners hM (ferrers_family_fit hM hR hS),foundation_faceIndices] at hs
  have hf := (PrimalDirichlet.treeCount_pair_eq_dirichlet hR0 hS0
    (cornerStrip_hull hR0 (by omega : 0≤S))
    (cornerStrip_connected hR0 (by omega : 0≤S))
    (cornerStrip_no_interior (by omega : 0≤S))).1
  rw [hs,hf]
  exact greenMinor_det_identity (Finset.Subset.refl (faceRectangle R S))
    (faceVacancyFit hR0 hS0 hM hR hS)

theorem corner_log_count_upper {R S : ℕ} (hR0 : 1≤R) (hS0 : 1≤S) {M : Corner → Diagram}
    (hM : ∀ c, IsFerrers (M c)) (hR : totalDefect M≤R) (hS : totalDefect M≤S) :
    Real.log (treeCount (cornerPrimal R S M) : ℝ)≤
      Real.log (treeCount (rectangle (R+1) (S+1)) : ℝ)-
        SquareMaximality.squareLatticeEntropy*totalDefect M-
          ∑ c, dirichletEnergy (ferrers_family_fit hM hR hS c) := by
  have hf := (PrimalDirichlet.treeCount_pair_eq_dirichlet hR0 hS0
    (cornerStrip_hull hR0 (by omega : 0≤S))
    (cornerStrip_connected hR0 (by omega : 0≤S))
    (cornerStrip_no_interior (by omega : 0≤S))).1
  have hp : 0<(treeCount (rectangle (R+1) (S+1)) : ℝ) := by
    rw [hf]
    exact (dirichlet_posDef (Finset.Subset.refl (faceRectangle R S))).det_pos
  have hg := greenMinor_det_pos (Finset.Subset.refl (faceRectangle R S))
    (faceVacancyFit hR0 hS0 hM hR hS)
  rw [corner_count_eq_greenMinor hR0 hS0 hM hR hS,Real.log_mul hp.ne' hg.ne']
  have h := corner_energy_lower hR0 hS0 hM hR hS
  unfold dirichletEnergy at h
  rw [face_vacancy_card hR0 hS0 hM hR hS] at h
  change _≤Real.log (treeCount (rectangle (R+1) (S+1)) : ℝ)-
    SquareMaximality.squareLatticeEntropy*totalDefect M-
      ∑ c, (-Real.log (greenMinor (ferrers_family_fit hM hR hS c)).det-
        SquareMaximality.squareLatticeEntropy*(M c).card)
  linarith

end
end SpanningTreeIsoperimetry.FiniteCornerProducts
