import SpanningTreeIsoperimetry.FiniteCornerCharges
import SpanningTreeIsoperimetry.CornerProfileNormalization

/-! Finite strip-energy orientation, derived from the actual primal count
comparison. It transports the correction bounds to every strip orientation. -/
namespace SpanningTreeIsoperimetry.FiniteCornerOrientation
open Ferrers CornerEnergy CornerStripBridge FerrersPrimalBridge DomainIsometries
  CornerPrimalDomains CornerProfileNormalization FiniteCornerCharges StripTreeComparisons
  SquareMaximality.Boundary
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem primal_count_eq_greenMinor {R S : ℕ} {M : Diagram} (hR : 1≤R) (hS : 1≤S)
    (hM : IsFerrers M) (hfit : M⊆faceRectangle R S) :
    (treeCount (primalDomain R S M) : ℝ)=
      (treeCount (rectangle (R+1) (S+1)) : ℝ)*(greenMinor hfit).det := by
  have hrect := (PrimalDirichlet.treeCount_pair_eq_dirichlet hR hS
    (cornerStrip_hull hR (by omega : 0≤S))
    (cornerStrip_connected hR (by omega : 0≤S)) (cornerStrip_no_interior (by omega : 0≤S))).1
  rw [primal_treeCount_eq_dirichlet hR hS hM hfit,hrect]
  exact greenMinor_det_identity (Finset.Subset.refl (faceRectangle R S)) hfit

theorem primal_count_pos {R S : ℕ} {M : Diagram} (hR : 1≤R) (hS : 1≤S)
    (hM : IsFerrers M) (hfit : M⊆faceRectangle R S) :
    0<(treeCount (primalDomain R S M) : ℝ) := by
  rw [primal_count_eq_greenMinor hR hS hM hfit]
  exact mul_pos (rectangle_count_pos hR hS)
    (greenMinor_det_pos (Finset.Subset.refl (faceRectangle R S)) hfit)

theorem primal_log_count_eq {R S : ℕ} {M : Diagram} (hR : 1≤R) (hS : 1≤S)
    (hM : IsFerrers M) (hfit : M⊆faceRectangle R S) :
    Real.log (treeCount (primalDomain R S M) : ℝ)=
      Real.log (treeCount (rectangle (R+1) (S+1)) : ℝ)-
        SquareMaximality.squareLatticeEntropy*M.card-dirichletEnergy hfit := by
  rw [primal_count_eq_greenMinor hR hS hM hfit,
    Real.log_mul (rectangle_count_pos hR hS).ne'
      (greenMinor_det_pos (Finset.Subset.refl (faceRectangle R S)) hfit).ne']
  unfold dirichletEnergy
  ring

theorem horizontal_fit {R S k : ℕ} (hk : k≤R) (hS : 1≤S) : horizontalStrip k⊆faceRectangle R S := by
  intro p hp
  have h := mem_horizontalStrip.mp hp
  exact mem_faceRectangle.mpr ⟨by omega,by omega⟩

theorem primal_horizontal (R S k : ℕ) : primalDomain R S (horizontalStrip k)=horizontalCornerStrip (R+1) (S+1) k := by
  rw [primalDomain_eq,integerFaces_horizontalStrip]
  rfl

theorem finite_orientation {R S k : ℕ} (hR : 1≤R) (hRS : R≤S) (hk : k≤R) :
    dirichletEnergy (verticalDiagram_subset hR (hk.trans hRS))≤
      dirichletEnergy (horizontal_fit hk (by omega : 1≤S)) := by
  have hS : 1≤S := by omega
  have hfit := horizontal_fit hk hS
  have hc := orientation_treeCount (r := R+1) (s := S+1) (k := k) (by omega) (by omega) (by omega)
  rw [← primal_horizontal R S k] at hc
  have hreal : (treeCount (primalDomain R S (horizontalStrip k)) : ℝ)≤
      treeCount (cornerStrip (R+1) (S+1) k) := by exact_mod_cast hc
  have hl := Real.log_le_log (primal_count_pos hR hS (horizontalStrip_isFerrers k) hfit) hreal
  rw [primal_log_count_eq hR hS (horizontalStrip_isFerrers k) hfit,
    strip_log_count_eq hR hS (hk.trans hRS),card_horizontalStrip] at hl
  linarith only [hl]

theorem stripDiagram_energy (k : ℕ) (v : Bool) : realEnergy (stripDiagram k v)=realEnergy (horizontalStrip k) := by
  cases v
  · rfl
  · exact FiniteStripError.verticalDiagram_energy k

theorem long_strip_energy_le {R S k : ℕ} (hR : 1≤R) (hRS : R≤S) (hk : k≤R) (v : Bool)
    (hfit : stripDiagram k v⊆faceRectangle R S) :
    dirichletEnergy (verticalDiagram_subset hR (hk.trans hRS))≤dirichletEnergy hfit := by
  cases v
  · exact finite_orientation hR hRS hk
  · rfl

theorem long_strip_correction_le {R S k : ℕ} (hR : 1≤R) (hRS : R≤S) (hk : k≤R) (v : Bool) :
    correction (faceRectangle R S) (verticalDiagram k)≤correction (faceRectangle R S) (stripDiagram k v) := by
  have hfit : stripDiagram k v⊆faceRectangle R S :=
    ferrers_fit_of_card (stripDiagram_ferrers k v) (by simpa only [stripDiagram_card] using hk)
      (by simpa only [stripDiagram_card] using hk.trans hRS)
  have h := long_strip_energy_le hR hRS hk v hfit
  rw [dirichletEnergy_eq (verticalDiagram_ferrers k),dirichletEnergy_eq (stripDiagram_ferrers k v),
    stripDiagram_energy,FiniteStripError.verticalDiagram_energy] at h
  linarith only [h]

end
end SpanningTreeIsoperimetry.FiniteCornerOrientation
