module

public import SpanningTreeIsoperimetry.SecondProfileModes
public import Mathlib.Analysis.Calculus.SmoothSeries

@[expose] public section

set_option backward.privateInPublic true

/-! Locally uniformly summable actual derivatives of the second profile. -/
namespace SpanningTreeIsoperimetry.SecondProfileCalculus

open Set Filter RectangularSecondProfile SecondProfileModes CoupledRectangleError
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

private theorem polynomial_bounds {b u : ℝ} (hb : 0≤b) (hu : 0≤u) (hub : u≤b) :
    |profilePolynomial u|≤(b+1)^3 ∧
      |profilePolynomialDeriv u|≤8*(b+1)^3 ∧
      |profilePolynomialSecond u|≤10*(b+1)^3 := by
  have hb2 := sq_nonneg b
  have hb3 := pow_nonneg hb 3
  have h1 : 1≤(b+1)^3 := by nlinarith
  have h2 : (b+1)^2≤(b+1)^3 := by nlinarith
  have h3 : b+1≤(b+1)^3 := by nlinarith
  have hB : 0≤b+1 := by linarith
  have hu2 : u^2≤(b+1)^2 := by gcongr; linarith
  refine ⟨?_,?_,?_⟩
  · rw [abs_of_nonneg (show 0≤profilePolynomial u by unfold profilePolynomial; positivity)]
    unfold profilePolynomial
    calc
      _≤(b+1)*(b+1)^2 := by
        have hplus : 1+u≤b+1 := by linarith
        exact mul_le_mul (by linarith : u≤b+1)
          (pow_le_pow_left₀ (by linarith : 0≤1+u) hplus 2) (sq_nonneg _) hB
      _=(b+1)^3 := by ring
  · rw [abs_of_nonneg (show 0≤profilePolynomialDeriv u by unfold profilePolynomialDeriv; positivity)]
    unfold profilePolynomialDeriv
    nlinarith
  · rw [abs_of_nonneg (show 0≤profilePolynomialSecond u by unfold profilePolynomialSecond; positivity)]
    unfold profilePolynomialSecond
    nlinarith

private theorem coefficient_bound {β b u : ℝ} (hβ : 1≤β) (hb : 0≤b) (hu : 0≤u) (hub : u≤b)
    {k : ℕ} (hk : k≤2) : |(modeCoefficient β k).eval u|≤30*β^2*(b+1)^3 := by
  obtain ⟨h0,h1,h2⟩ := polynomial_bounds hb hu hub
  have hB : 0≤(b+1)^3 := by positivity
  have hβ0 : 0≤β := by linarith
  have hβ1 : 1≤β^2 := by nlinarith
  have hβ2 : β≤β^2 := by nlinarith
  have hm1 := mul_le_mul_of_nonneg_right hβ1 hB
  have hm2 := mul_le_mul_of_nonneg_right hβ2 hB
  have hp : 0≤β^2*(b+1)^3 := by positivity
  interval_cases k
  · rw [coefficient_zero]
    nlinarith
  · rw [coefficient_one]
    have hm : |β*profilePolynomial u|≤β*(b+1)^3 := by
      rw [abs_mul,abs_of_nonneg hβ0]
      exact mul_le_mul_of_nonneg_left h0 hβ0
    have ht := abs_sub_le (profilePolynomialDeriv u) (0 : ℝ) (β*profilePolynomial u)
    simp only [sub_zero,zero_sub,abs_neg] at ht
    nlinarith
  · rw [coefficient_two,secondModePolynomial_identity]
    have hm : |2*β*profilePolynomialDeriv u|≤16*β*(b+1)^3 := by
      rw [abs_mul,abs_of_nonneg (by positivity : 0≤2*β)]
      have h := mul_le_mul_of_nonneg_left h1 (show 0≤2*β by positivity)
      nlinarith
    have hn : |β^2*profilePolynomial u|≤β^2*(b+1)^3 := by
      rw [abs_mul,abs_of_nonneg (sq_nonneg β)]
      exact mul_le_mul_of_nonneg_left h0 (sq_nonneg β)
    have ht := abs_sub_le (profilePolynomialSecond u) (0 : ℝ) (2*β*profilePolynomialDeriv u)
    simp only [sub_zero,zero_sub,abs_neg] at ht
    have ht' := abs_add_le (profilePolynomialSecond u-2*β*profilePolynomialDeriv u)
      (β^2*profilePolynomial u)
    nlinarith

def modeMajorant (a b : ℝ) (n : ℕ) : ℝ :=
  (120*Real.pi^2*(b+1)^3)*((n : ℝ)+1)^6*Real.exp (-2*Real.pi*a)^(n+1)

theorem modeMajorant_summable {a : ℝ} (ha : 0<a) (b : ℝ) : Summable (modeMajorant a b) := by
  let q := Real.exp (-2*Real.pi*a)
  have hq0 : 0<q := Real.exp_pos _
  have hq1 : q<1 := by rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have hm := geometricMoment_summable 6 (show |q|<1 by rwa [abs_of_pos hq0])
  have hshift : Summable (fun n : ℕ => ((n : ℝ)+1)^6*q^(n+1)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (summable_nat_add_iff 1).mpr hm
  apply (hshift.mul_left (120*Real.pi^2*(b+1)^3)).congr
  intro n
  dsimp only [modeMajorant,q]
  exact (mul_assoc _ _ _).symm

theorem weightedMode_norm_le {a b u : ℝ} (ha : 0<a) (hb : 0≤b) (hau : a≤u) (hub : u≤b)
    (n : ℕ) {k : ℕ} (hk : k≤2) : ‖weightedMode n k u‖≤modeMajorant a b n := by
  have hu : 0≤u := ha.le.trans hau
  have hf := frequency_ge_six n
  have hβ : 1≤frequency n := by linarith
  have hw := weight_nonneg n
  have hw' := weight_le_fourth n
  have hc := coefficient_bound hβ hb hu hub hk
  have hpow : Real.exp (-2*Real.pi*a)^(n+1)=Real.exp (-frequency n*a) := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [frequency]
    push_cast
    ring
  have he : Real.exp (-frequency n*u)≤Real.exp (-2*Real.pi*a)^(n+1) := by
    rw [hpow]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hau (by linarith)
  rw [Real.norm_eq_abs,weightedMode,abs_mul,abs_mul,abs_of_nonneg hw,abs_of_pos (Real.exp_pos _)]
  calc
    _≤((n : ℝ)+1)^4*(30*(frequency n)^2*(b+1)^3)*Real.exp (-2*Real.pi*a)^(n+1) := by gcongr
    _=modeMajorant a b n := by unfold modeMajorant frequency; ring

def sumMode (k : ℕ) (u : ℝ) : ℝ := ∑' n : ℕ, weightedMode n k u

theorem weightedMode_summable {u : ℝ} (hu : 0<u) {k : ℕ} (hk : k≤2) :
    Summable (fun n : ℕ => weightedMode n k u) := by
  exact Summable.of_norm_bounded (modeMajorant_summable (show 0<u/2 by linarith) (u+1))
    (fun n => weightedMode_norm_le (by linarith) (by linarith) (by linarith) (by linarith) n hk)

theorem hasDerivAt_sumMode {u : ℝ} (hu : 0<u) {k : ℕ} (hk : k<2) :
    HasDerivAt (sumMode k) (sumMode (k+1) u) u := by
  have huI : u∈Ioo (u/2) (u+1) := by constructor <;> linarith
  apply hasDerivAt_tsum_of_isPreconnected
    (modeMajorant_summable (show 0<u/2 by linarith) (u+1)) isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => hasDerivAt_weightedMode n k y)
    (fun n y hy => weightedMode_norm_le (by linarith) (by linarith) hy.1.le hy.2.le n (by omega))
    huI (weightedMode_summable hu (by omega)) huI

def K2D1 (u : ℝ) : ℝ := Real.pi^3/1440*(profilePolynomialDeriv u+240*sumMode 1 u)
def K2D2 (u : ℝ) : ℝ := Real.pi^3/1440*(profilePolynomialSecond u+240*sumMode 2 u)

theorem sumMode_zero_eq {u : ℝ} (hu : 0<u) : sumMode 0 u=profilePolynomial u*boseCubic u := by
  rw [boseCubic_eq_divisor_series hu]
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (ArithmeticFunction.sigma 3 n : ℝ)*
    Real.exp (-2*Real.pi*u)^n)]
  rw [← tsum_mul_left]
  unfold sumMode
  apply tsum_congr
  intro n
  rw [weightedMode,coefficient_zero]
  have he : Real.exp (-2*Real.pi*u)^(n+1)=Real.exp (-frequency n*u) := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [frequency]
    push_cast
    ring
  rw [he]
  unfold weight
  ring

theorem K2_eq_modes {u : ℝ} (hu : 0<u) :
    K2 u=Real.pi^3/1440*(profilePolynomial u+240*sumMode 0 u) := by
  rw [sumMode_zero_eq hu]
  unfold K2 profilePolynomial
  ring

private theorem hasDerivAt_profilePolynomial (u : ℝ) :
    HasDerivAt profilePolynomial (profilePolynomialDeriv u) u := by
  unfold profilePolynomial profilePolynomialDeriv
  convert (hasDerivAt_id u).fun_mul (((hasDerivAt_const u 1).fun_add (hasDerivAt_id u)).fun_pow 2) using 1 <;>
    simp only [id_eq,Nat.cast_ofNat,pow_one,mul_one] <;> ring

private theorem hasDerivAt_profilePolynomialDeriv (u : ℝ) :
    HasDerivAt profilePolynomialDeriv (profilePolynomialSecond u) u := by
  unfold profilePolynomialDeriv profilePolynomialSecond
  convert ((hasDerivAt_const u 1).fun_add ((hasDerivAt_id u).const_mul 4)).fun_add
    (((hasDerivAt_id u).fun_pow 2).const_mul 3) using 1 <;>
    simp only [id_eq,Nat.cast_ofNat,pow_one,mul_one] <;> ring

theorem hasDerivAt_K2 {u : ℝ} (hu : 0<u) : HasDerivAt K2 (K2D1 u) u := by
  have h := ((hasDerivAt_profilePolynomial u).fun_add ((hasDerivAt_sumMode hu (k := 0) (by omega)).const_mul 240)).const_mul
    (Real.pi^3/1440)
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hu] with v hv
  exact K2_eq_modes hv

theorem hasDerivAt_K2D1 {u : ℝ} (hu : 0<u) : HasDerivAt K2D1 (K2D2 u) u := by
  exact ((hasDerivAt_profilePolynomialDeriv u).fun_add
    ((hasDerivAt_sumMode hu (k := 1) (by omega)).const_mul 240)).const_mul (Real.pi^3/1440)

theorem iteratedDeriv_K2_two {u : ℝ} (hu : 0<u) : iteratedDeriv 2 K2 u=K2D2 u := by
  have he : deriv K2=ᶠ[𝓝 u] K2D1 := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    exact (hasDerivAt_K2 hv).deriv
  have hd := (hasDerivAt_K2D1 hu).congr_of_eventuallyEq he
  rw [iteratedDeriv_succ,iteratedDeriv_succ,iteratedDeriv_zero]
  exact hd.deriv

theorem sumMode_two_nonneg {u : ℝ} (hu : 1≤u) : 0≤sumMode 2 u :=
  tsum_nonneg (fun n => weightedMode_two_nonneg n hu)

theorem K2D2_pos {u : ℝ} (hu : 1≤u) : 0<K2D2 u := by
  have hs := sumMode_two_nonneg hu
  have hu0 : 0<u := by linarith
  unfold K2D2 profilePolynomialSecond
  positivity

theorem sumMode_two_convex : ConvexOn ℝ (Ici 1) (sumMode 2) := by
  refine ⟨convex_Ici 1,?_⟩
  intro x hx y hy a b ha hb hab
  have hx1 : 1≤x := hx
  have hy1 : 1≤y := hy
  have hz1 : 1≤a*x+b*y := by
    have hax := mul_le_mul_of_nonneg_left hx1 ha
    have hby := mul_le_mul_of_nonneg_left hy1 hb
    nlinarith
  have hx0 : 0<x := by linarith
  have hy0 : 0<y := by linarith
  have hz0 : 0<a*x+b*y := by linarith
  have hsz := weightedMode_summable hz0 (k := 2) (by omega)
  have hsx := weightedMode_summable hx0 (k := 2) (by omega)
  have hsy := weightedMode_summable hy0 (k := 2) (by omega)
  simp only [smul_eq_mul]
  calc
    sumMode 2 (a*x+b*y)≤(∑' n : ℕ, (a*weightedMode n 2 x+b*weightedMode n 2 y)) := by
      apply hsz.tsum_le_tsum _ ((hsx.mul_left a).add (hsy.mul_left b))
      intro n
      simpa only [smul_eq_mul] using (weightedMode_two_convex n).2 hx hy ha hb hab
    _=a*sumMode 2 x+b*sumMode 2 y := by
      rw [(hsx.mul_left a).tsum_add (hsy.mul_left b),tsum_mul_left,tsum_mul_left]
      rfl

theorem K2D2_convex : ConvexOn ℝ (Ici 1) K2D2 := by
  refine ⟨convex_Ici 1,?_⟩
  intro x hx y hy a b ha hb hab
  have h := sumMode_two_convex.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  unfold K2D2
  calc
    _≤(Real.pi^3/1440)*(profilePolynomialSecond (a*x+b*y)+
        240*(a*sumMode 2 x+b*sumMode 2 y)) := by gcongr
    _=_ := by
      unfold profilePolynomialSecond
      linear_combination -4*(Real.pi^3/1440)*hab

theorem K2D2_le_endpoints {u : ℝ} (hu : u∈Icc 1 3) :
    K2D2 u≤max (K2D2 1) (K2D2 3) :=
  K2D2_convex.le_max_of_mem_Icc (by simp) (by norm_num) hu

end
end SpanningTreeIsoperimetry.SecondProfileCalculus
