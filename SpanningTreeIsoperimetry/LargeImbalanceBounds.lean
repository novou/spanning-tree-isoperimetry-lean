module

public import SpanningTreeIsoperimetry.FluxBounds
public import SpanningTreeIsoperimetry.AspectCost

@[expose] public section

set_option backward.privateInPublic true

/-! Bounds for the actual aspect/flux comparison. Tree-count exclusion also
uses the finite-domain comparison and refined corner-energy envelope. -/
namespace SpanningTreeIsoperimetry.LargeImbalanceBounds
open FluxBounds AspectCost
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def fourthRatio (a x : ℝ) : ℝ := x^3/(a+x)^4

private theorem hasDerivAt_fourthRatio {a x : ℝ} (hx : a+x≠0) :
    HasDerivAt (fourthRatio a) (x^2*(3*a-x)/(a+x)^5) x := by
  have h := ((hasDerivAt_id x).pow 3).div (((hasDerivAt_id x).const_add a).pow 4) (pow_ne_zero 4 hx)
  convert h using 1 <;> (try funext y) <;> dsimp [fourthRatio,Pi.pow_apply,id_eq] <;> field_simp [hx] <;> ring

theorem fourthRatio_monotone {a : ℝ} (ha : 0<a) :
    MonotoneOn (fourthRatio a) (Set.Icc 0 (3*a)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (3*a))
  · intro x hx
    exact (hasDerivAt_fourthRatio (show a+x≠0 by linarith [hx.1])).continuousAt.continuousWithinAt
  · intro x hx
    have hx' := interior_subset hx
    exact (hasDerivAt_fourthRatio (show a+x≠0 by linarith [hx'.1])).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' := interior_subset hx
    rw [(hasDerivAt_fourthRatio (show a+x≠0 by linarith [hx'.1])).deriv]
    exact div_nonneg (mul_nonneg (sq_nonneg _) (by linarith [hx'.2])) (by have := hx'.1; positivity)

/-- Exact flux-imbalance estimate from the canonical arithmetic inequalities. -/
theorem fluxBound_large_imbalance {T r s k : ℝ}
    (hT : 4≤T) (hk : 0≤k) (hkt : k≤2*T+1)
    (hr : T^2-T+k+1≤r) (hs : r+k≤s) :
    fluxBound r s k < 8*Real.pi^3/(45*T^4*(T+1)) := by
  let a := T^2-T-2
  let x := k+1
  let y := 2*T+2
  have hquad : 12≤T^2-T := by
    nlinarith [mul_nonneg (show 0≤T-4 by linarith) (show 0≤T+3 by linarith)]
  have ha : 0<a := by dsimp [a]; linarith
  have hr2 : 2<r := by linarith
  have hx : 0≤x := by dsimp [x]; linarith
  have hy : 0≤y := by dsimp [y]; linarith
  have hxy : x≤y := by dsimp [x,y]; linarith
  have hy3 : y≤3*a := by
    dsimp [y,a]
    nlinarith [mul_nonneg (show 0≤T-4 by linarith) (show 0≤3*T+7 by linarith)]
  have hx3 : x≤3*a := hxy.trans hy3
  have hax : a+x≤r-2 := by dsimp [a,x]; linarith
  have hratio := fourthRatio_monotone ha ⟨hx,hx3⟩ ⟨hy,hy3⟩ hxy
  calc
    fluxBound r s k < Real.pi^3/45 * (x^3/(r-2)^4) := fluxBound_lt_fourth hr2 hk hs
    _ ≤ Real.pi^3/45 * fourthRatio a x := by unfold fourthRatio; gcongr
    _ ≤ Real.pi^3/45 * fourthRatio a y := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by
      unfold fourthRatio
      rw [show a+y=T*(T+1) by dsimp [a,y]; ring,mul_pow]
      dsimp only [y]
      have hT0 : T≠0 := by linarith
      have hT1 : T+1≠0 := by linarith
      field_simp [hT0,hT1]
      ring

def canonicalRatio (x : ℝ) : ℝ := (x^3-x)/(x^4-64)^2

private theorem fourth_denom_pos {x : ℝ} (hx : 8≤x) : 0<x^4-64 := by
  have hx2 : 64≤x^2 := by nlinarith [sq_nonneg (x-8)]
  nlinarith [sq_nonneg (x^2-64)]

private theorem hasDerivAt_canonicalRatio {x : ℝ} (hx : 8≤x) :
    HasDerivAt canonicalRatio
      ((x^4*(7-5*x^2)+64*(1-3*x^2))/(x^4-64)^3) x := by
  have hD := fourth_denom_pos hx
  have hN := ((hasDerivAt_id x).pow 3).sub (hasDerivAt_id x)
  have hden := ((hasDerivAt_id x).pow 4).sub_const 64
  convert hN.div (hden.pow 2) (pow_ne_zero 2 hD.ne') using 1 <;>
    (try funext y) <;> dsimp [canonicalRatio,Pi.pow_apply,Pi.sub_apply,id_eq] <;> field_simp [hD.ne'] <;> ring

theorem canonicalRatio_antitone : AntitoneOn canonicalRatio (Set.Ici 8) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 8)
  · intro x hx
    exact (hasDerivAt_canonicalRatio hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_canonicalRatio (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 8≤x := interior_subset hx
    have hx2 : 64≤x^2 := by nlinarith [sq_nonneg (x-8)]
    rw [(hasDerivAt_canonicalRatio hx').deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (pow_pos (fourth_denom_pos hx') 3).le
    have h1 : x^4*(7-5*x^2)≤0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have h2 : 64*(1-3*x^2)≤0 := by linarith
    linarith

/-- The k≥7 canonical branch fits below the refined-envelope margin. -/
theorem fluxBound_canonical_long {r s k : ℝ}
    (hk : 7≤k) (hr : (k+1)^2/4<r) (hs : r+k≤s) :
    fluxBound r s k < (277 : ℝ)/50000 := by
  let x := k+1
  have hx : 8≤x := by dsimp [x]; linarith
  have hx2 : 64≤x^2 := by nlinarith [sq_nonneg (x-8)]
  have hr2 : 2<r := by dsimp [x] at hx2; nlinarith
  have hD := fourth_denom_pos hx
  have hden : (x^4-64)/16<r^2-4 := by
    have hp : 0<(r-x^2/4)*(r+x^2/4) := mul_pos (by dsimp [x]; linarith) (by nlinarith)
    nlinarith
  have hden0 : 0<(x^4-64)/16 := by positivity
  have hsq : ((x^4-64)/16)^2<(r^2-4)^2 := by
    nlinarith [mul_pos (sub_pos.mpr hden) (show 0<(r^2-4)+(x^4-64)/16 by linarith)]
  have hnum : 0<Real.pi^3*k*(k+1)*(k+2) := by
    have hk0 : 0<k := by linarith
    positivity
  have hbound : fluxBound r s k < (256*Real.pi^3/45)*canonicalRatio x := by
    apply lt_of_le_of_lt (fluxBound_le_cubic hr2 (by linarith) hs)
    calc
      _ < Real.pi^3*k*(k+1)*(k+2)/(45*((x^4-64)/16)^2) :=
        div_lt_div_of_pos_left hnum (by positivity) (by nlinarith)
      _ = _ := by
        unfold canonicalRatio
        have he : k*(k+1)*(k+2)=x^3-x := by dsimp [x]; ring
        rw [show Real.pi^3*k*(k+1)*(k+2)=Real.pi^3*(k*(k+1)*(k+2)) by ring,he]
        field_simp [hD.ne']
        ring
  have hmono : canonicalRatio x≤canonicalRatio 8 := canonicalRatio_antitone (by simp) hx hx
  have hpi : Real.pi<(22 : ℝ)/7 := by linarith [Real.pi_lt_d4]
  have hpi3 : Real.pi^3<((22 : ℝ)/7)^3 := by gcongr
  apply hbound.trans_le
  calc
    (256*Real.pi^3/45)*canonicalRatio x ≤ (256*Real.pi^3/45)*canonicalRatio 8 :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ (277 : ℝ)/50000 := by
      norm_num [canonicalRatio] at hpi3 ⊢
      nlinarith

end
end SpanningTreeIsoperimetry.LargeImbalanceBounds
