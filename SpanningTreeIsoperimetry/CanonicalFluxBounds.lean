module

public import SpanningTreeIsoperimetry.CanonicalRectangleBounds
public import SpanningTreeIsoperimetry.LargeImbalanceBounds

@[expose] public section

/-! Flux estimates for the actual canonical selector, with its integer
arithmetic discharged by CanonicalRectangleBounds. -/
namespace SpanningTreeIsoperimetry.CanonicalFluxBounds
open FluxBounds LargeImbalanceBounds CanonicalRectangleBounds

theorem canonical_large_imbalance {N : ℕ} (hN : 0<N) :
    let L := minimumSideSum N
    let m := L/2
    let e := L%2
    let d := m*(m+e)-N
    let T := selectorIndex d e
    let R := (canonicalParameters N).1
    let S := (canonicalParameters N).2.1
    let k := (canonicalParameters N).2.2
    4≤T → fluxBound R S k < 8*Real.pi^3/(45*(T : ℝ)^4*((T : ℝ)+1)) := by
  dsimp only
  intro hT
  let T := selectorIndex
    (minimumSideSum N/2*(minimumSideSum N/2+minimumSideSum N%2)-N)
    (minimumSideSum N%2)
  let R := (canonicalParameters N).1
  let S := (canonicalParameters N).2.1
  let k := (canonicalParameters N).2.2
  change 4≤T at hT
  change fluxBound R S k < 8*Real.pi^3/(45*(T : ℝ)^4*((T : ℝ)+1))
  have hp := canonical_flux_hypotheses hN
  change 0<R ∧ R≤S ∧ k≤2*T+1 ∧ T^2-T+k+1≤R ∧ R+k≤S at hp
  have ht2 : T≤T^2 := by simpa only [pow_two] using Nat.le_mul_self T
  have hr : (T : ℝ)^2-T+k+1≤R := by
    have hh : ((T^2-T+k+1 : ℕ) : ℝ)≤R := by exact_mod_cast hp.2.2.2.1
    simpa only [Nat.cast_add,Nat.cast_sub ht2,Nat.cast_pow,Nat.cast_one] using hh
  exact fluxBound_large_imbalance (by exact_mod_cast hT) (Nat.cast_nonneg k)
    (by exact_mod_cast hp.2.2.1) hr (by exact_mod_cast hp.2.2.2.2)

/-- The parity term in the canonical size relation is essential at the
largest possible deficit. -/
theorem canonical_square_bound {T e R k : ℕ} (he : e≤1) (hk : 7≤k)
    (hstep : k≤2*T+e) (hsize : T^2-T+T*e+k+1≤R) :
    ((k : ℝ)+1)^2/4<R := by
  have ht2 : T≤T^2 := by simpa only [pow_two] using Nat.le_mul_self T
  have hr : (T : ℝ)^2-T+T*e+k+1≤R := by
    have hh : ((T^2-T+T*e+k+1 : ℕ) : ℝ)≤R := by exact_mod_cast hsize
    simpa only [Nat.cast_add,Nat.cast_sub ht2,Nat.cast_pow,Nat.cast_mul,Nat.cast_one] using hh
  have hk' : (7 : ℝ)≤k := by exact_mod_cast hk
  interval_cases e
  · have hs : (k : ℝ)≤2*T := by exact_mod_cast hstep
    norm_num at hr
    have hp := mul_nonneg (show (0 : ℝ)≤2*T-k by linarith)
      (show (0 : ℝ)≤2*T+k-2 by linarith)
    nlinarith
  · have hs : (k : ℝ)≤2*T+1 := by exact_mod_cast hstep
    norm_num at hr
    have hp := mul_nonneg (show (0 : ℝ)≤2*T+1-k by linarith)
      (show (0 : ℝ)≤2*T+k-1 by linarith)
    nlinarith

theorem canonical_long {N : ℕ} (hN : 0<N) (hk : 7≤(canonicalParameters N).2.2) :
    fluxBound (canonicalParameters N).1 (canonicalParameters N).2.1
      (canonicalParameters N).2.2 < (277 : ℝ)/50000 := by
  let L := minimumSideSum N
  let m := L/2
  let e := L%2
  let d := m*(m+e)-N
  let T := selectorIndex d e
  let R := (canonicalParameters N).1
  let S := (canonicalParameters N).2.1
  let k := (canonicalParameters N).2.2
  have he : e≤1 := by dsimp [e]; omega
  have hs := selector_remainder_lt_step (selectorIndex_bounds d e).1 (selectorIndex_bounds d e).2
  change k<2*T+e+1 at hs
  have hsize := canonical_size_relation hN
  change T^2-T+T*e+k+1≤R at hsize
  have hsq := canonical_square_bound he hk (show k≤2*T+e by omega) hsize
  have hp := canonical_flux_hypotheses hN
  change 0<R ∧ R≤S ∧ k≤2*T+1 ∧ T^2-T+k+1≤R ∧ R+k≤S at hp
  exact fluxBound_canonical_long (by exact_mod_cast hk) hsq (by exact_mod_cast hp.2.2.2.2)

end SpanningTreeIsoperimetry.CanonicalFluxBounds
