import SpanningTreeIsoperimetry.CrossHullCountComparison
import SpanningTreeIsoperimetry.CanonicalConcentrationArithmetic
import SpanningTreeIsoperimetry.StabilitySharpness

/-! Exact actual canonical-count decomposition underlying the extremal
asymptotic, and the actual square limit defining its constant. -/
namespace SpanningTreeIsoperimetry.CanonicalCountExpansion
open Ferrers CornerEnergy CornerStripBridge RectangularRemainder RectangleProfileContinuity
open CrossHullCountComparison CanonicalConcentrationArithmetic Filter
open scoped BigOperators Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def squareConstant : ℝ := B 1

def stripCorrection (N : ℕ) : ℝ :=
  correction (faceRectangle ((canonicalParameters N).1-1) ((canonicalParameters N).2.1-1))
    (verticalDiagram (canonicalParameters N).2.2)

def canonicalRemainder (N : ℕ) : ℝ :=
  J (((canonicalParameters N).2.1 : ℝ)/(canonicalParameters N).1)-squareConstant+
    error (canonicalParameters N).1 (canonicalParameters N).2.1-stripCorrection N-
      (1/4)*Real.log (1+((canonicalParameters N).2.2 : ℝ)/N)

private theorem alpha_eq_log : SquareMaximality.Rectangle.Concrete.alpha=Real.log (1+Real.sqrt 2) := by
  rw [← SquareMaximality.Rectangle.Concrete.exp_alpha,Real.log_exp]

theorem squareConstant_eq_J_one : squareConstant=J 1 := by simp [squareConstant,J]

theorem square_constant_limit :
    Tendsto (fun n : ℕ => Real.log (treeCount (rectangle n n) : ℝ)-
      SquareMaximality.squareLatticeEntropy*(n : ℝ)^2+2*Real.log (1+Real.sqrt 2)*n+
        (1/2)*Real.log (n : ℝ)) atTop (𝓝 squareConstant) := by
  have he : Tendsto (fun n : ℕ => error n n) atTop (𝓝 0) := by
    apply StabilitySharpness.error_tendsto tendsto_id
    filter_upwards [eventually_ge_atTop 1] with n hn
    change 0<n ∧ n≤n ∧ n≤3*n
    exact ⟨by omega,le_rfl,by omega⟩
  have hb : Tendsto (fun n : ℕ => squareConstant+error n n) atTop (𝓝 squareConstant) := by
    simpa using he.const_add squareConstant
  apply hb.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  unfold error F squareConstant
  rw [div_self hn0,alpha_eq_log]
  ring

theorem finite_energy_eq {N r s k : ℕ} (hN : 0<N) (hp : canonicalParameters N=(r,s,k))
    (hr : 2≤r) : finiteTargetEnergy hr (show k≤s-1 by
      have hh := parameters_properties hN hp; omega)=
        realEnergy (horizontalStrip k)+stripCorrection N := by
  have hprops := parameters_properties hN hp
  have hk : k≤s-1 := by omega
  have hh := dirichletEnergy_eq (verticalDiagram_ferrers k)
    (verticalDiagram_subset (by omega : 1≤r-1) hk)
  rw [FiniteStripError.verticalDiagram_energy] at hh
  simpa only [finiteTargetEnergy,stripCorrection,hp] using hh

theorem stripCorrection_bounds {N r s k : ℕ} (hN : 0<N) (hp : canonicalParameters N=(r,s,k))
    (hr : 3≤r) : 0≤stripCorrection N ∧ stripCorrection N≤FluxBounds.fluxBound r s k := by
  have hprops := parameters_properties hN hp
  have hgap := canonical_gap hN hp
  have ht := finite_target_upper hr (show 2≤s by omega) (show k+1<s by omega)
  have he := finite_energy_eq hN hp (show 2≤r by omega)
  refine ⟨correction_nonneg _ _,?_⟩
  linarith

theorem canonical_log_exact {N r s k : ℕ} (hN : 0<N) (hp : canonicalParameters N=(r,s,k))
    (hr : 2≤r) :
    Real.log (treeCount (canonicalDomain N) : ℝ)=
      SquareMaximality.squareLatticeEntropy*N-Real.log (1+Real.sqrt 2)*minimumSideSum N-
        (1/4)*Real.log ((N : ℝ)+k)+J ((s : ℝ)/r)-realEnergy (horizontalStrip k)+
          error r s-stripCorrection N := by
  have hprops := parameters_properties hN hp
  have hs : 2≤s := by omega
  have hk : k≤s-1 := by omega
  have ht := target_log_eq hr hs hk
  have he := finite_energy_eq hN hp hr
  have hf := F_eq_J (show 0<r by omega) (show 0<s by omega)
  have harea : (r : ℝ)*s=(N : ℝ)+k := by exact_mod_cast hprops.2.2.2.1
  have hsum : (r : ℝ)+s=minimumSideSum N := by exact_mod_cast hprops.2.2.1
  have hbulk : SquareMaximality.squareLatticeEntropy*(r : ℝ)*s=
      SquareMaximality.squareLatticeEntropy*N+SquareMaximality.squareLatticeEntropy*k := by
    rw [mul_assoc,harea]
    ring
  unfold F at hf
  rw [hbulk,hsum,harea,alpha_eq_log] at hf
  unfold canonicalDomain
  rw [hp]
  linarith

theorem canonical_log_decomposition {N : ℕ} (hN : 0<N) (hr : 2≤(canonicalParameters N).1) :
    Real.log (treeCount (canonicalDomain N) : ℝ)=
      SquareMaximality.squareLatticeEntropy*N-Real.log (1+Real.sqrt 2)*minimumSideSum N-
        (1/4)*Real.log (N : ℝ)+squareConstant-realEnergy (horizontalStrip (canonicalParameters N).2.2)+
          canonicalRemainder N := by
  let r := (canonicalParameters N).1
  let s := (canonicalParameters N).2.1
  let k := (canonicalParameters N).2.2
  have hp : canonicalParameters N=(r,s,k) := rfl
  have hh := canonical_log_exact hN hp hr
  have hN0 : (N : ℝ)≠0 := by exact_mod_cast hN.ne'
  have hlog : Real.log ((N : ℝ)+k)=Real.log (N : ℝ)+Real.log (1+(k : ℝ)/N) := by
    have harg : 1+(k : ℝ)/N≠0 := by positivity
    rw [show (N : ℝ)+k=(N : ℝ)*(1+(k : ℝ)/N) by field_simp [hN0] <;> ring,
      Real.log_mul hN0 harg]
  rw [hlog] at hh
  unfold canonicalRemainder
  change _=SquareMaximality.squareLatticeEntropy*N-Real.log (1+Real.sqrt 2)*minimumSideSum N-
    (1/4)*Real.log (N : ℝ)+squareConstant-realEnergy (horizontalStrip k)+
      (J ((s : ℝ)/r)-squareConstant+error r s-stripCorrection N-(1/4)*Real.log (1+(k : ℝ)/N))
  linarith

end
end SpanningTreeIsoperimetry.CanonicalCountExpansion
