module

public import SpanningTreeIsoperimetry.BoundaryLossSeries
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

/-! The positive hyperbolic boundary-loss integral is its convergent image
series. The fourth-order bound follows from the checked zeta-four sum. -/
namespace SpanningTreeIsoperimetry.BoundaryLossIntegral
open MeasureTheory Set Filter BoundaryLossSeries
open scoped BigOperators Topology
noncomputable section

def laplace (a x : ℝ) : ℝ := x*Real.exp (-(a*x))

theorem laplace_integrable {a : ℝ} (ha : 0<a) : IntegrableOn (laplace a) (Ioi 0) := by
  change IntegrableOn (fun x : ℝ => x*Real.exp (-(a*x))) (Ioi 0)
  simpa only [Real.rpow_one,neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ))
      (by norm_num) (by norm_num) ha)

theorem integral_laplace {a : ℝ} (ha : 0<a) :
    (∫ x : ℝ in Ioi 0, laplace a x)=1/a^2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (2 : ℝ)) (r := a) (by norm_num) ha
  norm_num [laplace,Real.Gamma_nat_eq_factorial] at h ⊢
  exact h

def term (r c : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  x*Real.sinh (c*x)^2*Real.exp (-(2*r*((n : ℝ)+1)*x))

def integrand (r c x : ℝ) : ℝ := x*Real.sinh (c*x)^2/(Real.exp (2*r*x)-1)

private theorem sinh_sq_exp (x : ℝ) :
    Real.sinh x^2=(Real.exp (2*x)+Real.exp (-(2*x))-2)/4 := by
  have h := Real.cosh_two_mul x
  have hs := Real.cosh_sq_sub_sinh_sq x
  rw [Real.cosh_eq] at h
  nlinarith only [h,hs]

theorem term_eq (r c : ℝ) (n : ℕ) (x : ℝ) :
    term r c n x=(1/4 : ℝ)*(laplace (2*(r*(n+1)-c)) x+
      laplace (2*(r*(n+1)+c)) x-2*laplace (2*r*(n+1)) x) := by
  have h1 : Real.exp (2*(c*x))*Real.exp (-(2*r*((n : ℝ)+1)*x))=
      Real.exp (-(2*(r*(n+1)-c)*x)) := by rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-(2*(c*x)))*Real.exp (-(2*r*((n : ℝ)+1)*x))=
      Real.exp (-(2*(r*(n+1)+c)*x)) := by rw [← Real.exp_add]; congr 1; ring
  unfold term
  rw [sinh_sq_exp]
  calc
    _=(x/4)*(Real.exp (2*(c*x))*Real.exp (-(2*r*((n : ℝ)+1)*x))+
      Real.exp (-(2*(c*x)))*Real.exp (-(2*r*((n : ℝ)+1)*x))-
      2*Real.exp (-(2*r*((n : ℝ)+1)*x))) := by ring
    _=_ := by rw [h1,h2]; unfold laplace; ring

private theorem rate_pos {r c : ℝ} (hc : 0≤c) (hr : c<r) (n : ℕ) :
    0<r*((n : ℝ)+1)-c := by
  have hn := Nat.cast_nonneg (α := ℝ) n
  have hr0 : 0<r := lt_of_le_of_lt hc hr
  nlinarith

theorem term_integrable {r c : ℝ} (hc : 0≤c) (hr : c<r) (n : ℕ) :
    IntegrableOn (term r c n) (Ioi 0) := by
  have hm := rate_pos hc hr n
  have hp : 0<2*(r*((n : ℝ)+1)+c) := by linarith
  have h0 : 0<2*r*((n : ℝ)+1) := by nlinarith
  have he : term r c n=(fun x => (1/4 : ℝ)*(laplace (2*(r*(n+1)-c)) x+
      laplace (2*(r*(n+1)+c)) x-2*laplace (2*r*(n+1)) x)) := funext (term_eq r c n)
  rw [he]
  exact (((laplace_integrable (show 0<2*(r*((n : ℝ)+1)-c) by positivity)).add
    (laplace_integrable hp)).sub ((laplace_integrable h0).const_mul 2)).const_mul (1/4)

theorem integral_term {r c : ℝ} (hc : 0≤c) (hr : c<r) (n : ℕ) :
    (∫ x : ℝ in Ioi 0, term r c n x)=(1/16 : ℝ)*imageDifference (r*(n+1)) c := by
  have hm := rate_pos hc hr n
  have hp : 0<2*(r*((n : ℝ)+1)+c) := by linarith
  have h0 : 0<2*r*((n : ℝ)+1) := by nlinarith
  have hm' : 0<2*(r*((n : ℝ)+1)-c) := by positivity
  simp_rw [term_eq]
  rw [integral_const_mul]
  have hsub := integral_sub ((laplace_integrable hm').add (laplace_integrable hp))
    ((laplace_integrable h0).const_mul 2)
  simp only [Pi.add_apply] at hsub
  rw [hsub,integral_add (laplace_integrable hm') (laplace_integrable hp),integral_const_mul,
    integral_laplace hm',integral_laplace hp,integral_laplace h0]
  unfold imageDifference
  have hr0 : r≠0 := (lt_of_le_of_lt hc hr).ne'
  have hn0 : (n : ℝ)+1≠0 := by positivity
  have hminus : r*((n : ℝ)+1)-c≠0 := hm.ne'
  have hplus : r*((n : ℝ)+1)+c≠0 := by linarith
  field_simp
  <;> ring

theorem term_nonneg {r c x : ℝ} (hx : 0≤x) (n : ℕ) : 0≤term r c n x := by
  unfold term
  positivity

/-- Geometric expansion at every positive integration point. -/
theorem term_hasSum {r c x : ℝ} (hr : 0<r) (hx : 0<x) :
    HasSum (fun n => term r c n x) (integrand r c x) := by
  let q := Real.exp (-(2*r*x))
  have hq0 : 0<q := Real.exp_pos _
  have hq1 : q<1 := by apply Real.exp_lt_one_iff.mpr; nlinarith
  have hs := ((hasSum_geometric_of_abs_lt_one (by rw [abs_of_pos hq0]; exact hq1)).mul_left q).mul_left
    (x*Real.sinh (c*x)^2)
  have heq : q*(1-q)⁻¹=1/(Real.exp (2*r*x)-1) := by
    dsimp only [q]
    rw [Real.exp_neg]
    have he : Real.exp (2*r*x)≠0 := (Real.exp_pos _).ne'
    have he1 : Real.exp (2*r*x)-1≠0 := by
      have hh : 1<Real.exp (2*r*x) := Real.one_lt_exp_iff.mpr (by positivity)
      linarith
    field_simp
    <;> ring
  have hlim : x*Real.sinh (c*x)^2*(q*(1-q)⁻¹)=integrand r c x := by
    rw [heq]
    unfold integrand
    ring
  rw [hlim] at hs
  apply hs.congr_fun
  intro n
  unfold term
  congr 1
  dsimp only [q]
  rw [← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  ring

/-- The hyperbolic integral is exactly the positive image series. -/
theorem integral_eq_imageSeries {r c : ℝ} (hc : 0≤c) (hr : c<r) :
    (∫ x : ℝ in Ioi 0, integrand r c x)=(1/16 : ℝ)*∑' n : ℕ, imageDifference (r*(n+1)) c := by
  have hn (n : ℕ) : (∫ x : ℝ in Ioi 0, ‖term r c n x‖)=(1/16 : ℝ)*imageDifference (r*(n+1)) c := by
    rw [← integral_term hc hr n]
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact Real.norm_of_nonneg (term_nonneg hx.le n)
  have hs : Summable (fun n => ∫ x : ℝ in Ioi 0, ‖term r c n x‖) := by
    simp_rw [hn]
    exact (imageDifference_summable hc hr).mul_left (1/16)
  have hsum := hasSum_integral_of_summable_integral_norm (term_integrable hc hr) hs
  have hpoint : (fun x : ℝ => ∑' n, term r c n x)=ᵐ[volume.restrict (Ioi 0)] integrand r c := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact (term_hasSum (lt_of_le_of_lt hc hr) hx).tsum_eq
  calc
    _=∫ x : ℝ in Ioi 0, ∑' n, term r c n x := (integral_congr_ae hpoint).symm
    _=∑' n, ∫ x : ℝ in Ioi 0, term r c n x := hsum.tsum_eq.symm
    _=(1/16 : ℝ)*∑' n : ℕ, imageDifference (r*(n+1)) c := by
      simp_rw [integral_term hc hr]
      exact tsum_mul_left

/-- The integrability needed for the subsequent monotone gamma substitution.
It also follows from the positive, nonzero value of the convergent series. -/
theorem integrand_integrable {r c : ℝ} (hc : 0≤c) (hr : c<r) :
    IntegrableOn (integrand r c) (Ioi 0) := by
  by_cases hc0 : c=0
  · subst c
    have he : integrand r 0=(fun _ : ℝ => 0) := by funext x; simp [integrand]
    rw [he]
    exact integrable_zero ℝ ℝ (volume.restrict (Ioi 0))
  have hcp : 0<c := lt_of_le_of_ne hc (Ne.symm hc0)
  have hp : 0 < imageDifference r c := by
    rw [imageDifference_eq hc hr]
    have hr0 : 0<r := lt_trans hcp hr
    have hgap : 0<r^2-c^2 := by nlinarith
    have hnum : 0<3*r^2-c^2 := by nlinarith
    positivity
  have hsum : 0<∑' n : ℕ, imageDifference (r*(n+1)) c := by
    apply (imageDifference_summable hc hr).tsum_pos
      (fun n => imageDifference_nonneg hc (by have h := rate_pos hc hr n; linarith)) 0
    simpa only [Nat.cast_zero,zero_add,mul_one] using hp
  apply Integrable.of_integral_ne_zero
  rw [integral_eq_imageSeries hc hr]
  exact (mul_pos (by norm_num : (0 : ℝ)<1/16) hsum).ne'

/-- The exact fourth-order hyperbolic integral upper bound from the appendix. -/
theorem integral_majorant {r c : ℝ} (hc : 0≤c) (hr : c<r) :
    (4/Real.pi)*(∫ x : ℝ in Ioi 0, integrand r c x)≤Real.pi^3*c^2/(60*(r^2-c^2)^2) := by
  rw [integral_eq_imageSeries hc hr]
  have he : (4/Real.pi)*((1/16 : ℝ)*(∑' n : ℕ, imageDifference (r*(n+1)) c))=
      (1/(4*Real.pi))*(∑' n : ℕ, imageDifference (r*(n+1)) c) := by ring
  rw [he]
  exact imageSeries_le hc hr

end
end SpanningTreeIsoperimetry.BoundaryLossIntegral
