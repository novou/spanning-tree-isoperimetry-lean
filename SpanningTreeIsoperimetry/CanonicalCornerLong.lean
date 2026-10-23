module

public import SpanningTreeIsoperimetry.FiniteCornerCharges
public import SpanningTreeIsoperimetry.CanonicalConcentrationArithmetic
public import SpanningTreeIsoperimetry.CanonicalFluxBounds
public import SpanningTreeIsoperimetry.RefinedCornerEnvelope

@[expose] public section

set_option backward.privateInPublic true

/-! Actual canonical-hull concentration at every deficit at least five. -/
namespace SpanningTreeIsoperimetry.CanonicalCornerLong
open Ferrers CornerEnergy CornerPrimalDomains CornerStripBridge FiniteCornerCharges
  CanonicalConcentrationArithmetic FluxBounds RefinedCornerEnvelope CornerConcentration
open scoped Classical BigOperators
noncomputable section

private theorem flux_five_fixed : fluxBound 10 15 5<(1 : ℝ)/100 := by
  have hp := pow_lt_pow_left₀ (show Real.pi<(63/20 : ℝ) by linarith [Real.pi_lt_d2])
    Real.pi_pos.le (by decide : 3≠0)
  norm_num [fluxBound,cubic,quadratic]
  nlinarith only [hp]

private theorem flux_six_fixed : fluxBound 13 19 6<(1 : ℝ)/100 := by
  have hp := pow_lt_pow_left₀ (show Real.pi<(63/20 : ℝ) by linarith [Real.pi_lt_d2])
    Real.pi_pos.le (by decide : 3≠0)
  norm_num [fluxBound,cubic,quadratic]
  nlinarith only [hp]

theorem flux_five_lt {r s : ℝ} (hr : 10≤r) (hs : 15≤s) : fluxBound r s 5<(1 : ℝ)/100 := by
  calc
    _≤fluxBound 10 s 5 := fluxBound_antitone_left (by norm_num) hr (by norm_num)
    _≤fluxBound 10 15 5 := fluxBound_antitone_right (by norm_num) (by norm_num) hs
    _<_ := flux_five_fixed

theorem flux_six_lt {r s : ℝ} (hr : 13≤r) (hs : 19≤s) : fluxBound r s 6<(1 : ℝ)/100 := by
  calc
    _≤fluxBound 13 s 6 := fluxBound_antitone_left (by norm_num) hr (by norm_num)
    _≤fluxBound 13 19 6 := fluxBound_antitone_right (by norm_num) (by norm_num) hs
    _<_ := flux_six_fixed

theorem bound_long_lower {k : ℕ} (hk : 7≤k) : (7054 : ℝ)/100000≤bound k := by
  unfold bound
  split_ifs <;> (try omega) <;> norm_num

/-- The actual universal corner-energy gap strictly dominates the actual
canonical finite-strip flux at every k≥5. -/
theorem canonical_flux_gap {N r s k : ℕ} (hN : 0<N) (hp : canonicalParameters N=(r,s,k)) (hk : 5≤k) :
    realEnergy (horizontalStrip k)+fluxBound r s k<bound k := by
  have hgap := canonical_gap hN hp
  by_cases hk5 : k=5
  · subst k
    have hr := canonical_five_min hN hp
    have hs : 15≤s := by omega
    have hf := flux_five_lt (r := (r : ℝ)) (s := (s : ℝ)) (by exact_mod_cast hr) (by exact_mod_cast hs)
    have he := StripSupportingLines.strip_supporting_line 5
    norm_num [bound] at he ⊢
    linarith
  · by_cases hk6 : k=6
    · subst k
      have hr := canonical_six_min hN hp
      have hs : 19≤s := by omega
      have hf := flux_six_lt (r := (r : ℝ)) (s := (s : ℝ)) (by exact_mod_cast hr) (by exact_mod_cast hs)
      have he := StripSupportingLines.strip_supporting_line 6
      norm_num [bound] at he ⊢
      linarith
    · have hk7 : 7≤k := by omega
      have hf := CanonicalFluxBounds.canonical_long hN (by simpa only [hp] using hk7)
      simp only [hp] at hf
      linarith [bound_long_lower hk7,UniformStripEnergy.realEnergy_strip_lt_13_200 k]

/-- Strict actual spanning-tree comparison for every nonconcentrated Ferrers
family on an actual canonical hull with deficit at least five. -/
theorem canonical_nonstrip_long {N r s k : ℕ} (hN : 0<N) (hp : canonicalParameters N=(r,s,k))
    (hk : 5≤k) {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c))
    (htotal : totalDefect M=k) (hn : ¬IsConcentrated Finset.univ M) :
    treeCount (cornerPrimal (r-1) (s-1) M)<treeCount (cornerStrip r s k) := by
  have hprop := parameters_properties hN hp
  have hgap := canonical_gap hN hp
  have hr0 : 1≤r-1 := by omega
  have hs0 : 1≤s-1 := by omega
  have hR : totalDefect M≤r-1 := by omega
  have hS : totalDefect M≤s-1 := by omega
  have hb := RefinedCornerEnvelope.family_bound Finset.univ M (fun c _ => hM c)
    (by change 2≤totalDefect M; omega) hn
  change bound (totalDefect M)<∑ c,realEnergy (M c) at hb
  rw [htotal] at hb
  have hf := finite_strip_upper_primal (by omega : 3≤r) (by omega : 1≤totalDefect M) (by omega : totalDefect M+1<s)
  have hbound := canonical_flux_gap hN hp hk
  have hc : 0≤(totalDefect M : ℝ)*correction (faceRectangle (r-1) (s-1)) {(0,0)} := by
    exact mul_nonneg (Nat.cast_nonneg _) (correction_nonneg _ _)
  have he : dirichletEnergy (verticalDiagram_subset hr0 hS)<
      (∑ c,realEnergy (M c))+(totalDefect M : ℝ)*correction (faceRectangle (r-1) (s-1)) {(0,0)} := by
    rw [← htotal] at hbound hb
    linarith only [hf,hbound,hb,hc]
  have h := count_lt_strip_of_energy_gap hr0 hs0 hM hR hS he
  simpa only [htotal,Nat.sub_add_cancel (show 1≤r by omega),Nat.sub_add_cancel (show 1≤s by omega)] using h

end
end SpanningTreeIsoperimetry.CanonicalCornerLong
