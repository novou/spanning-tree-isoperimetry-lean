module

public import SpanningTreeIsoperimetry.RectangleModeSums
public import SpanningTreeIsoperimetry.GeometricTailBounds
public import SpanningTreeIsoperimetry.SharpRectangleExpansion

@[expose] public section

set_option backward.privateInPublic true

/-! Quantitative omitted-mode and endpoint errors for the actual rectangle. -/
namespace SpanningTreeIsoperimetry.RectangleTailRemainder

open SquareMaximality.Rectangle RectangularRemainder RectangleResidualBounds
open RectangleModeSums GeometricTailBounds SharpRectangleExpansion CoupledRectangleError
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def tailPolynomial : ℝ :=
  1/(1-1/500)+3*moment1 (1/500)+3*moment2 (1/500)+moment3 (1/500)

private theorem tailPolynomial_nonneg : 0≤tailPolynomial := by
  norm_num [tailPolynomial,moment1,moment2,moment3]

theorem cubicTail_polynomial_bound {r : ℕ} (hr : 1≤r) :
    cubicTail (1/500) r≤(1/500)^r*(r : ℝ)^3*tailPolynomial := by
  have hrR : (1 : ℝ)≤r := by exact_mod_cast hr
  have hr2 : (r : ℝ)≤(r : ℝ)^2 := by nlinarith [sq_nonneg ((r : ℝ)-1)]
  have hr23 : (r : ℝ)^2≤(r : ℝ)^3 := by
    nlinarith [mul_nonneg (show 0≤(r : ℝ)-1 by linarith) (sq_nonneg (r : ℝ))]
  have hr13 : (r : ℝ)≤(r : ℝ)^3 := hr2.trans hr23
  have hr03 : (1 : ℝ)≤(r : ℝ)^3 := hrR.trans hr13
  have hm1 : 0≤3*moment1 (1/500) := by norm_num [moment1]
  have hm2 : 0≤3*moment2 (1/500) := by norm_num [moment2]
  have hm3 : 0≤moment3 (1/500) := by norm_num [moment3]
  have h1 := mul_le_mul_of_nonneg_right hr23 hm1
  have h2 := mul_le_mul_of_nonneg_right hr13 hm2
  have h3 := mul_le_mul_of_nonneg_right hr03 hm3
  have hb : (r : ℝ)^3/(1-1/500)+3*(r : ℝ)^2*moment1 (1/500)+
      3*r*moment2 (1/500)+moment3 (1/500)≤(r : ℝ)^3*tailPolynomial := by
    unfold tailPolynomial
    have h := add_le_add (add_le_add (add_le_add
      (le_refl ((r : ℝ)^3/(1-1/500))) h1) h2) h3
    convert h using 1 <;> ring
  rw [cubicTail_eq (by norm_num : |(1 : ℝ)/500|<1)]
  have h := mul_le_mul_of_nonneg_left hb (show 0≤(1/500 : ℝ)^r by positivity)
  simpa only [mul_assoc] using h

theorem scaled_cubicTail_bound {r0 r : ℕ} (h0 : 1≤r0) (hr : r0≤r) :
    (r : ℝ)^2*cubicTail (1/500) r≤(r0 : ℝ)^5*(1/500)^r0*tailPolynomial := by
  have hr1 : 1≤r := h0.trans hr
  have h := mul_le_mul_of_nonneg_left (cubicTail_polynomial_bound hr1) (sq_nonneg (r : ℝ))
  have hp := pow_mul_geometric_antitone 5 (q := (1 : ℝ)/500) (by norm_num) (by norm_num) h0 hr1 hr
  have hm := mul_le_mul_of_nonneg_right hp tailPolynomial_nonneg
  calc
    _≤(r : ℝ)^2*((1/500)^r*(r : ℝ)^3*tailPolynomial) := h
    _=((r : ℝ)^5*(1/500)^r)*tailPolynomial := by ring
    _≤_ := hm

/-- The aspect factor in the omitted cubic Bose sum is absorbed by decay. -/
theorem omittedBose_scaled_bound {u : ℝ} (hu : 1≤u) {r : ℕ} (hr : 0<r) :
    u*omittedBose u r≤cubicTail (1/500) r/(1-1/500) := by
  have hu0 : 0<u := by linarith
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hpoint (n : ℕ) :
      u*(((r+n : ℕ) : ℝ)^3/(Real.exp (2*Real.pi*u*(r+n))-1))≤
        ((r+n : ℕ) : ℝ)^3*(1/500)^(r+n)/(1-1/500) := by
    have hj : 0<r+n := by omega
    have hjR : (0 : ℝ)<((r+n : ℕ) : ℝ) := by exact_mod_cast hj
    let c : ℝ := 2*Real.pi*((r+n : ℕ) : ℝ)
    have hc : 0<c := by dsimp [c]; positivity
    have hm := scaled_exp_reciprocal_antitone hc (by change (0 : ℝ)<1; norm_num) hu0 hu
    simp only [mul_one] at hm
    have harg : 2*Real.pi*u*(r+n)=c*u := by dsimp [c]; push_cast; ring
    have hh : u*(((r+n : ℕ) : ℝ)^3/(Real.exp (2*Real.pi*u*(r+n))-1))≤
        ((r+n : ℕ) : ℝ)^3/(Real.exp (2*Real.pi*((r+n : ℕ) : ℝ))-1) := by
      rw [harg]
      have h := mul_le_mul_of_nonneg_left hm (show 0≤((r+n : ℕ) : ℝ)^3 by positivity)
      convert h using 1 <;> dsimp [c] <;> ring
    exact hh.trans (linear_bose_term_le 3 hj)
  have hnonneg (n : ℕ) : 0≤u*(((r+n : ℕ) : ℝ)^3/(Real.exp (2*Real.pi*u*(r+n))-1)) := by
    have hd : 0<Real.exp (2*Real.pi*u*(r+n))-1 :=
      sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
    positivity
  have hG : HasSum (fun n : ℕ => ((r+n : ℕ) : ℝ)^3*(1/500)^(r+n)/(1-1/500))
      (cubicTail (1/500) r/(1-1/500)) := by
    rw [cubicTail_eq (by norm_num : |(1 : ℝ)/500|<1)]
    exact (cubicTail_hasSum (by norm_num : |(1 : ℝ)/500|<1) r).div_const (1-1/500)
  have hS := Summable.of_nonneg_of_le hnonneg hpoint hG.summable
  unfold omittedBose
  rw [← tsum_mul_left]
  exact (hS.tsum_le_tsum hpoint hG.summable).trans_eq hG.tsum_eq

private theorem q_aspect_le {u : ℝ} (hu : 1≤u) : Real.exp (-2*Real.pi*u)≤(1 : ℝ)/500 := by
  apply le_trans _ q_pi_le
  apply Real.exp_le_exp.mpr
  nlinarith [Real.pi_pos]

/-- Fourth-order decay of the omitted linear modes from any positive start. -/
theorem linear_tail_quartic {u : ℝ} (hu : 1≤u) {r0 r : ℕ} (h0 : 1≤r0) (hr : r0≤r) :
    (r : ℝ)^4*|logTail (Real.exp (-2*Real.pi*u)) r|≤
      (r0 : ℝ)^4*(1/500)^r0/(1-1/500)^2 := by
  have hr1 : 1≤r := h0.trans hr
  let q := Real.exp (-2*Real.pi*u)
  have hq0 : 0<q := Real.exp_pos _
  have hq : q≤1/500 := q_aspect_le hu
  have hq1 : q<1 := by linarith
  have hb := logTail_bound hq0 hq1 (show 0<r by omega)
  have hb' : |logTail q r|≤(1/500)^r/(1-1/500)^2 := by
    apply hb.trans
    gcongr
  have hp := pow_mul_geometric_antitone 4 (q := (1 : ℝ)/500) (by norm_num) (by norm_num) h0 hr1 hr
  calc
    _≤(r : ℝ)^4*((1/500)^r/(1-1/500)^2) := mul_le_mul_of_nonneg_left hb' (by positivity)
    _=((r : ℝ)^4*(1/500)^r)/(1-1/500)^2 := by ring
    _≤_ := div_le_div_of_nonneg_right hp (by norm_num)

/-- Fourth-order endpoint-log decay, using the exact alpha exponential. -/
theorem endpoint_quartic {r0 r : ℕ} (h0 : 1≤r0) (hr : r0≤r) :
    (r : ℝ)^4*|(1/2 : ℝ)*Real.log (1-Real.exp (-4*r*Concrete.alpha))|≤
      (r0 : ℝ)^4*(1/33)^r0/(2*(1-(1/33)^r0)) := by
  have hr1 : 1≤r := h0.trans hr
  have hq0 := Concrete.q_pos
  have hq1 := Concrete.q_lt_one
  have hpow1 : Concrete.q^r<1 := pow_lt_one₀ hq0.le hq1 (by omega)
  have hbar : (1/33 : ℝ)^r<1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hbar0 : (1/33 : ℝ)^r0<1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hqpow : Concrete.q^r≤(1/33 : ℝ)^r := pow_le_pow_left₀ hq0.le q_alpha_le r
  have hqstep : (1/33 : ℝ)^r≤(1/33 : ℝ)^r0 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hr
  have he : Real.exp (-4*r*Concrete.alpha)=Concrete.q^r := by
    rw [Concrete.q,← Real.exp_nat_mul]
    congr 1
    ring
  have hlog : Real.log (1-Concrete.q^r)≤0 :=
    Real.log_nonpos (sub_pos.mpr hpow1).le (by have := pow_nonneg hq0.le r; linarith)
  have hneg : -Real.log (1-Concrete.q^r)≤(1/33 : ℝ)^r/(1-(1/33)^r) := by
    apply (Concrete.Inputs.neg_log_one_sub_le (pow_nonneg hq0.le r) hpow1).trans
    gcongr
  have habs : |(1/2 : ℝ)*Real.log (1-Real.exp (-4*r*Concrete.alpha))|≤
      (1/33 : ℝ)^r/(2*(1-(1/33)^r)) := by
    rw [he,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/2),abs_of_nonpos hlog]
    have h := mul_le_mul_of_nonneg_left hneg (by norm_num : (0 : ℝ)≤1/2)
    convert h using 1 <;> field_simp [(sub_pos.mpr hbar).ne'] <;> ring
  have hp := pow_mul_geometric_antitone 4 (q := (1 : ℝ)/33) (by norm_num) (by norm_num) h0 hr1 hr
  calc
    _≤(r : ℝ)^4*((1/33)^r/(2*(1-(1/33)^r))) := mul_le_mul_of_nonneg_left habs (by positivity)
    _=((r : ℝ)^4*(1/33)^r)/(2*(1-(1/33)^r)) := by ring
    _≤((r0 : ℝ)^4*(1/33)^r0)/(2*(1-(1/33)^r)) :=
      div_le_div_of_nonneg_right hp (by positivity)
    _≤_ := div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left (by linarith) (by norm_num : (0 : ℝ)≤2))

theorem omittedBose_nonneg {u : ℝ} (hu : 0<u) {r : ℕ} (hr : 0<r) : 0≤omittedBose u r := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  apply tsum_nonneg
  intro n
  have hd : 0<Real.exp (2*Real.pi*u*(r+n))-1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  exact div_nonneg (by positivity) hd.le

def tailError (r s : ℕ) : ℝ :=
  |logTail (Real.exp (-2*Real.pi*((s : ℝ)/r))) r|+
    (Real.pi^3*s/(6*(r : ℝ)^3))*omittedBose ((s : ℝ)/r) r+
    |(1/2)*Real.log (1-Real.exp (-4*r*Concrete.alpha))|

theorem combined_tail_quartic {r0 r s : ℕ} (h0 : 1≤r0) (hr : r0≤r) (hrs : r≤s) :
    (r : ℝ)^4*tailError r s≤tailAllowance r0 := by
  have hr1 : 1≤r := h0.trans hr
  have hrR : (0 : ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have hsR : (r : ℝ)≤s := by exact_mod_cast hrs
  let u := (s : ℝ)/r
  have hu : 1≤u := (one_le_div hrR).mpr hsR
  have hlin := linear_tail_quartic hu h0 hr
  have hend := endpoint_quartic h0 hr
  have hom := omittedBose_scaled_bound hu (show 0<r by omega)
  have hcub := scaled_cubicTail_bound h0 hr
  have hTP := tailPolynomial_nonneg
  have hmid : (r : ℝ)^2*(u*omittedBose u r)≤
      ((r0 : ℝ)^5*(1/500)^r0*tailPolynomial)/(1-1/500) := by
    calc
      _≤(r : ℝ)^2*(cubicTail (1/500) r/(1-1/500)) := mul_le_mul_of_nonneg_left hom (sq_nonneg _)
      _=((r : ℝ)^2*cubicTail (1/500) r)/(1-1/500) := by ring
      _≤_ := div_le_div_of_nonneg_right hcub (by norm_num)
  have hpi : Real.pi≤(22 : ℝ)/7 := by linarith [Real.pi_lt_d4]
  have hscaled : (r : ℝ)^4*((Real.pi^3*s/(6*(r : ℝ)^3))*omittedBose u r)≤
      ((22/7 : ℝ)^3/6)*(r0 : ℝ)^5*(1/500)^r0*tailPolynomial/(1-1/500) := by
    calc
      _=(Real.pi^3/6)*((r : ℝ)^2*(u*omittedBose u r)) := by
        dsimp [u]
        field_simp [hrR.ne'] <;> ring
      _≤(Real.pi^3/6)*(((r0 : ℝ)^5*(1/500)^r0*tailPolynomial)/(1-1/500)) :=
        mul_le_mul_of_nonneg_left hmid (by positivity)
      _≤((22/7 : ℝ)^3/6)*(((r0 : ℝ)^5*(1/500)^r0*tailPolynomial)/(1-1/500)) := by gcongr
      _=_ := by ring
  have h := add_le_add (add_le_add hend hlin) hscaled
  convert h using 1 <;> dsimp [u,tailError,tailAllowance,tailPolynomial] <;> ring

theorem tailError_four_lt {r s : ℕ} (hr : 4≤r) (hrs : r≤s) :
    tailError r s<(1/1000)/(r : ℝ)^4 := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have h := (combined_tail_quartic (r0 := 4) (by omega) hr hrs).trans_lt tailAllowance_four_lt
  exact (lt_div_iff₀ (pow_pos hrR 4)).mpr (by simpa only [mul_comm] using h)

theorem tailError_three_lt {r s : ℕ} (hr : 3≤r) (hrs : r≤s) :
    tailError r s<(1/500)/(r : ℝ)^4 := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have h := (combined_tail_quartic (r0 := 3) (by omega) hr hrs).trans_lt tailAllowance_three_lt
  exact (lt_div_iff₀ (pow_pos hrR 4)).mpr (by simpa only [mul_comm] using h)

end
end SpanningTreeIsoperimetry.RectangleTailRemainder
