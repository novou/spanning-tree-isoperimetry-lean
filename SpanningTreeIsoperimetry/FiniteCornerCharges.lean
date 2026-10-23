module

public import SpanningTreeIsoperimetry.FiniteCornerProducts
public import SpanningTreeIsoperimetry.FiniteSingletonSquareLower
public import SpanningTreeIsoperimetry.FiniteLongStripError

@[expose] public section

/-! Actual per-cell finite corner charges and strict tree-count comparisons
with the single long-side strip in the same hull. -/
namespace SpanningTreeIsoperimetry.FiniteCornerCharges
open Ferrers CornerEnergy CornerPrimalDomains CornerStripBridge FiniteCornerProducts
  SquareMaximality.Boundary
open scoped Classical BigOperators
noncomputable section

theorem finite_energy_ge_cell_charge {R S : ℕ} {M : Diagram} (hM : IsFerrers M)
    (hfit : M⊆faceRectangle R S) :
    realEnergy M+(M.card : ℝ)*correction (faceRectangle R S) {(0,0)}≤dirichletEnergy hfit := by
  rw [dirichletEnergy_eq hM hfit]
  linarith only [correction_ge_card_mul_singleton R S M]

theorem corner_log_count_upper_charged {R S : ℕ} (hR0 : 1≤R) (hS0 : 1≤S)
    {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c))
    (hR : totalDefect M≤R) (hS : totalDefect M≤S) :
    Real.log (treeCount (cornerPrimal R S M) : ℝ)≤
      Real.log (treeCount (rectangle (R+1) (S+1)) : ℝ)-
        SquareMaximality.squareLatticeEntropy*totalDefect M-
        (∑ c,realEnergy (M c))-(totalDefect M : ℝ)*correction (faceRectangle R S) {(0,0)} := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset Corner))
    (fun c _ => finite_energy_ge_cell_charge (hM c) (ferrers_family_fit hM hR hS c))
  have hcard : (∑ c : Corner, ((M c).card : ℝ))=(totalDefect M : ℝ) := by
    simp only [totalDefect,Nat.cast_sum]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,hcard] at hsum
  linarith only [hsum,corner_log_count_upper hR0 hS0 hM hR hS]

/-- Primal-coordinate form of the checked finite long-strip upper bound. -/
theorem finite_strip_upper_primal {r s k : ℕ} (hr : 3≤r) (hk : 1≤k) (hs : k+1<s) :
    dirichletEnergy (verticalDiagram_subset (by omega : 1≤r-1) (by omega : k≤s-1))≤
      realEnergy (horizontalStrip k)+FluxBounds.fluxBound r s k := by
  have h := (FiniteLongStripError.finite_long_strip_error (R := r-1) (S := s-1)
    (by omega) (k-1) (by omega)).2
  have hkk : k-1+1=k := by omega
  have hrr : ((r-1 : ℕ) : ℝ)+1=(r : ℝ) := by exact_mod_cast (show r-1+1=r by omega)
  have hss : ((s-1 : ℕ) : ℝ)+1=(s : ℝ) := by exact_mod_cast (show s-1+1=s by omega)
  have hkr : ((k-1 : ℕ) : ℝ)+1=(k : ℝ) := by exact_mod_cast hkk
  simp only [hkk,hrr,hss,hkr] at h
  linarith only [h]

theorem rectangle_count_pos {R S : ℕ} (hR : 1≤R) (hS : 1≤S) :
    0<(treeCount (rectangle (R+1) (S+1)) : ℝ) := by
  have h := (PrimalDirichlet.treeCount_pair_eq_dirichlet hR hS
    (cornerStrip_hull hR (by omega : 0≤S))
    (cornerStrip_connected hR (by omega : 0≤S)) (cornerStrip_no_interior (by omega : 0≤S))).1
  rw [h]
  exact (dirichlet_posDef (Finset.Subset.refl (faceRectangle R S))).det_pos

theorem strip_log_count_eq {R S k : ℕ} (hR : 1≤R) (hS : 1≤S) (hk : k≤S) :
    Real.log (treeCount (cornerStrip (R+1) (S+1) k) : ℝ)=
      Real.log (treeCount (rectangle (R+1) (S+1)) : ℝ)-
        SquareMaximality.squareLatticeEntropy*k-dirichletEnergy (verticalDiagram_subset hR hk) := by
  have hp := rectangle_count_pos hR hS
  have hg := greenMinor_det_pos (Finset.Subset.refl (faceRectangle R S)) (verticalDiagram_subset hR hk)
  rw [cornerStrip_treeCount_eq_greenMinor hR hS hk,Real.log_mul hp.ne' hg.ne']
  unfold dirichletEnergy
  have hc : (verticalDiagram k).card=k := by simp [verticalDiagram]
  rw [hc]
  ring

theorem strip_count_pos {R S k : ℕ} (hR : 1≤R) (hS : 1≤S) (hk : k≤S) :
    0<(treeCount (cornerStrip (R+1) (S+1) k) : ℝ) := by
  rw [cornerStrip_treeCount_eq_greenMinor hR hS hk]
  exact mul_pos (rectangle_count_pos hR hS)
    (greenMinor_det_pos (Finset.Subset.refl (faceRectangle R S)) (verticalDiagram_subset hR hk))

theorem corner_count_pos {R S : ℕ} (hR0 : 1≤R) (hS0 : 1≤S)
    {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c))
    (hR : totalDefect M≤R) (hS : totalDefect M≤S) :
    0<(treeCount (cornerPrimal R S M) : ℝ) := by
  rw [corner_count_eq_greenMinor hR0 hS0 hM hR hS]
  exact mul_pos (rectangle_count_pos hR0 hS0)
    (greenMinor_det_pos (Finset.Subset.refl (faceRectangle R S)) (faceVacancyFit hR0 hS0 hM hR hS))

/-- A reusable actual-count comparison, before the canonical scalar gap is
inserted. The finite energies and both primal graph counts are identified. -/
theorem count_lt_strip_of_energy_gap {R S : ℕ} (hR0 : 1≤R) (hS0 : 1≤S)
    {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c))
    (hR : totalDefect M≤R) (hS : totalDefect M≤S)
    (hgap : dirichletEnergy (verticalDiagram_subset hR0 hS)<
      (∑ c,realEnergy (M c))+(totalDefect M : ℝ)*correction (faceRectangle R S) {(0,0)}) :
    treeCount (cornerPrimal R S M)<treeCount (cornerStrip (R+1) (S+1) (totalDefect M)) := by
  have hlog : Real.log (treeCount (cornerPrimal R S M) : ℝ)<
      Real.log (treeCount (cornerStrip (R+1) (S+1) (totalDefect M)) : ℝ) := by
    rw [strip_log_count_eq hR0 hS0 hS]
    linarith only [corner_log_count_upper_charged hR0 hS0 hM hR hS,hgap]
  have hlt := (Real.log_lt_log_iff (corner_count_pos hR0 hS0 hM hR hS)
    (strip_count_pos hR0 hS0 hS)).mp hlog
  exact_mod_cast hlt

end
end SpanningTreeIsoperimetry.FiniteCornerCharges
