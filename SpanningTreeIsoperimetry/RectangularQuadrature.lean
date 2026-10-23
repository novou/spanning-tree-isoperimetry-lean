module

public import SpanningTreeIsoperimetry.RectangularRemainder
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

set_option backward.privateInPublic true

/-! Local Euler–Maclaurin identities through order six, proved by explicit
polynomial differentiation and repeated integration by parts. -/
namespace SpanningTreeIsoperimetry.RectangularQuadrature

open Polynomial MeasureTheory
open scoped BigOperators Interval
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

/-- Bernoulli polynomials divided by their factorials, through degree six. -/
def quadraturePolynomial : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X-C (1/2)
  | 2 => C (1/2)*X^2-C (1/2)*X+C (1/12)
  | 3 => C (1/6)*X^3-C (1/4)*X^2+C (1/12)*X
  | 4 => C (1/24)*X^4-C (1/12)*X^3+C (1/24)*X^2-C (1/720)
  | 5 => C (1/120)*X^5-C (1/48)*X^4+C (1/72)*X^3-C (1/720)*X
  | 6 => C (1/720)*X^6-C (1/240)*X^5+C (1/288)*X^4-C (1/1440)*X^2+C (1/30240)
  | _ => 0

theorem quadraturePolynomial_derivative {n : ℕ} (hn : n<6) :
    derivative (quadraturePolynomial (n+1))=quadraturePolynomial n := by
  interval_cases n <;> apply Polynomial.funext <;> intro x <;>
    norm_num [quadraturePolynomial,Polynomial.derivative_add,Polynomial.derivative_sub,
      Polynomial.derivative_mul,Polynomial.derivative_pow] <;> ring

def scaledKernel (a h : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  h^n*(quadraturePolynomial n).eval ((x-a)/h)

theorem continuous_scaledKernel (a h : ℝ) (n : ℕ) : Continuous (scaledKernel a h n) := by
  unfold scaledKernel
  fun_prop

theorem hasDerivAt_scaledKernel (a h x : ℝ) {n : ℕ} (hn : n<6) (hh : h≠0) :
    HasDerivAt (scaledKernel a h (n+1)) (scaledKernel a h n x) x := by
  have hi := ((hasDerivAt_id x).sub_const a).div_const h
  have hp := ((quadraturePolynomial (n+1)).hasDerivAt ((x-a)/h)).comp x hi
  rw [quadraturePolynomial_derivative hn] at hp
  have ht := hp.const_mul (h^(n+1))
  unfold scaledKernel
  convert ht using 1 <;> (try rfl) <;>
    (try simp only [Function.comp_def,id_eq,pow_succ]) <;> field_simp <;> ring

@[simp] theorem scaledKernel_left (a h : ℝ) (n : ℕ) :
    scaledKernel a h n a=h^n*(quadraturePolynomial n).eval 0 := by simp [scaledKernel]

theorem scaledKernel_right (a h : ℝ) (n : ℕ) (hh : h≠0) :
    scaledKernel a h n (a+h)=h^n*(quadraturePolynomial n).eval 1 := by simp [scaledKernel,hh]

def weightedIntegral (a h : ℝ) (n : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∫ x in a..a+h, scaledKernel a h n x*f x

@[simp] theorem weightedIntegral_zero (a h : ℝ) (f : ℝ → ℝ) :
    weightedIntegral a h 0 f=∫ x in a..a+h, f x := by simp [weightedIntegral,scaledKernel,quadraturePolynomial]

/-- One exact integration-by-parts step in the derivative ladder. -/
theorem weightedIntegral_step (a h : ℝ) {n : ℕ} (hn : n<6) (hh : h≠0)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ x, HasDerivAt f (g x) x) :
    weightedIntegral a h n f=
      scaledKernel a h (n+1) (a+h)*f (a+h)-scaledKernel a h (n+1) a*f a-
        weightedIntegral a h (n+1) g := by
  have hb := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (continuous_scaledKernel a h (n+1)).continuousOn hf.continuousOn
    (fun x _ => hasDerivAt_scaledKernel a h x hn hh) (fun x _ => hd x)
    ((continuous_scaledKernel a h n).intervalIntegrable a (a+h)) (hg.intervalIntegrable a (a+h))
  change weightedIntegral a h (n+1) g=
    scaledKernel a h (n+1) (a+h)*f (a+h)-scaledKernel a h (n+1) a*f a-
      weightedIntegral a h n f at hb
  linarith

def cellError (a h : ℝ) (f : ℝ → ℝ) : ℝ :=
  (h/2)*(f a+f (a+h))-(∫ x in a..a+h, f x)

/-- Fourth-order local trapezoidal identity; all coefficients are exact. -/
theorem cellError_four (a h : ℝ) (hh : h≠0) (f : ℕ → ℝ → ℝ)
    (hc : ∀ n≤4, Continuous (f n)) (hd : ∀ n<4, ∀ x, HasDerivAt (f n) (f (n+1) x) x) :
    cellError a h (f 0)=h^2/12*(f 1 (a+h)-f 1 a)-h^4/720*(f 3 (a+h)-f 3 a)-
      weightedIntegral a h 4 (f 4) := by
  have h0 := weightedIntegral_step a h (n := 0) (by decide) hh (f 0) (f 1)
    (hc 0 (by omega)) (hc 1 (by omega)) (hd 0 (by omega))
  have h1 := weightedIntegral_step a h (n := 1) (by decide) hh (f 1) (f 2)
    (hc 1 (by omega)) (hc 2 (by omega)) (hd 1 (by omega))
  have h2 := weightedIntegral_step a h (n := 2) (by decide) hh (f 2) (f 3)
    (hc 2 (by omega)) (hc 3 (by omega)) (hd 2 (by omega))
  have h3 := weightedIntegral_step a h (n := 3) (by decide) hh (f 3) (f 4)
    (hc 3 (by omega)) (hc 4 (by omega)) (hd 3 (by omega))
  rw [weightedIntegral_zero] at h0
  have hright (n : ℕ) := scaledKernel_right a h n hh
  simp only [scaledKernel_left,hright] at h0 h1 h2 h3
  norm_num [quadraturePolynomial] at h0 h1 h2 h3
  unfold cellError
  linear_combination -h0+h1-h2+h3

/-- Sixth-order local trapezoidal identity with an explicit integral remainder. -/
theorem cellError_six (a h : ℝ) (hh : h≠0) (f : ℕ → ℝ → ℝ)
    (hc : ∀ n≤6, Continuous (f n)) (hd : ∀ n<6, ∀ x, HasDerivAt (f n) (f (n+1) x) x) :
    cellError a h (f 0)=h^2/12*(f 1 (a+h)-f 1 a)-h^4/720*(f 3 (a+h)-f 3 a)+
      h^6/30240*(f 5 (a+h)-f 5 a)-weightedIntegral a h 6 (f 6) := by
  have hfour := cellError_four a h hh f (fun n hn => hc n (by omega)) (fun n hn => hd n (by omega))
  have h4 := weightedIntegral_step a h (n := 4) (by decide) hh (f 4) (f 5)
    (hc 4 (by omega)) (hc 5 (by omega)) (hd 4 (by omega))
  have h5 := weightedIntegral_step a h (n := 5) (by decide) hh (f 5) (f 6)
    (hc 5 (by omega)) (hc 6 (by omega)) (hd 5 (by omega))
  have hright (n : ℕ) := scaledKernel_right a h n hh
  simp only [scaledKernel_left,hright] at h4 h5
  norm_num [quadraturePolynomial] at h4 h5
  linear_combination hfour-h4+h5

private theorem unit_product_bounds {x : ℝ} (hx : x∈Set.Icc 0 1) :
    0≤x*(1-x) ∧ x*(1-x)≤1/4 := by
  constructor
  · exact mul_nonneg hx.1 (by linarith [hx.2])
  · nlinarith [sq_nonneg (x-1/2)]

theorem quadraturePolynomial_four_bound {x : ℝ} (hx : x∈Set.Icc 0 1) :
    |(quadraturePolynomial 4).eval x|≤1/720 := by
  have hz := unit_product_bounds hx
  have hs : (x*(1-x))^2≤1/16 := by nlinarith
  have he : (quadraturePolynomial 4).eval x=(x*(1-x))^2/24-1/720 := by
    simp [quadraturePolynomial]
    ring
  rw [he,abs_le]
  constructor <;> nlinarith [sq_nonneg (x*(1-x))]

theorem quadraturePolynomial_six_bound {x : ℝ} (hx : x∈Set.Icc 0 1) :
    |(quadraturePolynomial 6).eval x|≤1/30240 := by
  let z := x*(1-x)
  have hz : 0≤z ∧ z≤1/4 := unit_product_bounds hx
  have hs : z^2≤1/16 := by nlinarith
  have hc : z^3≤z^2/4 := by
    have h := mul_le_mul_of_nonneg_right hz.2 (sq_nonneg z)
    nlinarith
  have hz3 : 0≤z^3 := pow_nonneg hz.1 _
  have he : (quadraturePolynomial 6).eval x=(1/42-z^2/2-z^3)/720 := by
    simp [quadraturePolynomial,z]
    ring
  rw [he,abs_le]
  constructor <;> nlinarith [sq_nonneg z]

/-- The local weighted remainder is controlled by its explicitly bounded
Bernoulli polynomial and the actual derivative integral. -/
theorem weightedIntegral_bound (a h : ℝ) (hh : 0<h) (n : ℕ) (f : ℝ → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ x∈Set.Icc 0 1, |(quadraturePolynomial n).eval x|≤C) :
    |weightedIntegral a h n f|≤(h^n*C)*(∫ x in a..a+h, |f x|) := by
  unfold weightedIntegral
  refine (intervalIntegral.abs_integral_le_integral_abs (by linarith : a≤a+h)).trans ?_
  calc
    (∫ x in a..a+h, |scaledKernel a h n x*f x|)≤
        ∫ x in a..a+h, (h^n*C)*|f x| := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (((continuous_scaledKernel a h n).mul hf).abs.intervalIntegrable _ _)
        ((hf.abs.const_mul (h^n*C)).intervalIntegrable _ _)
      intro x hx
      have ht : (x-a)/h∈Set.Icc 0 1 :=
        ⟨div_nonneg (by linarith [hx.1]) hh.le,(div_le_one hh).mpr (by linarith [hx.2])⟩
      have hb := hC _ ht
      have hk : |scaledKernel a h n x|≤h^n*C := by
        rw [scaledKernel,abs_mul,abs_of_nonneg (pow_nonneg hh.le n)]
        exact mul_le_mul_of_nonneg_left hb (pow_nonneg hh.le n)
      change |scaledKernel a h n x*f x|≤_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)
    _=(h^n*C)*(∫ x in a..a+h, |f x|) := intervalIntegral.integral_const_mul _ _

private theorem cellError_eq_trapezoidal (a h : ℝ) (f : ℝ → ℝ) :
    cellError a h f=trapezoidal_error f 1 a (a+h) := by
  rw [cellError,trapezoidal_error,trapezoidal_integral_one]
  simp only [add_sub_cancel_left]

private theorem mesh_step (a h : ℝ) (i : ℕ) :
    a+(i : ℝ)*h+h=a+((i+1 : ℕ) : ℝ)*h := by push_cast; ring

theorem sum_cellError (a h : ℝ) {N : ℕ} (hN : 0<N) (f : ℝ → ℝ) (hf : Continuous f) :
    (∑ i∈Finset.range N, cellError (a+(i : ℝ)*h) h f)=trapezoidal_error f N a (a+N*h) := by
  simp_rw [cellError_eq_trapezoidal,mesh_step]
  simpa only [Nat.cast_add,Nat.cast_one] using
    sum_trapezoidal_error_adjacent_intervals (a := a) (h := h) hN (hf.intervalIntegrable _ _)

def compositeRemainder (a h : ℝ) (N n : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ i∈Finset.range N, weightedIntegral (a+(i : ℝ)*h) h n f

theorem compositeRemainder_bound (a h : ℝ) (hh : 0<h) (N n : ℕ) (f : ℝ → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ x∈Set.Icc 0 1, |(quadraturePolynomial n).eval x|≤C) :
    |compositeRemainder a h N n f|≤(h^n*C)*(∫ x in a..a+N*h, |f x|) := by
  have hsum : (∑ i∈Finset.range N, ∫ x in a+(i : ℝ)*h..a+(i : ℝ)*h+h, |f x|)=
      ∫ x in a..a+N*h, |f x| := by
    simp_rw [mesh_step]
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := fun i : ℕ => a+(i : ℝ)*h)
      (n := N) (fun i _ => hf.abs.intervalIntegrable _ _)
    simpa only [Nat.cast_zero,zero_mul,add_zero] using h
  calc
    |compositeRemainder a h N n f|≤∑ i∈Finset.range N, |weightedIntegral (a+(i : ℝ)*h) h n f| :=
      Finset.abs_sum_le_sum_abs _ _
    _≤∑ i∈Finset.range N, (h^n*C)*(∫ x in a+(i : ℝ)*h..a+(i : ℝ)*h+h, |f x|) :=
      Finset.sum_le_sum (fun i _ => weightedIntegral_bound _ h hh n f hf C hC)
    _=(h^n*C)*(∫ x in a..a+N*h, |f x|) := by rw [← Finset.mul_sum,hsum]

private theorem mesh_telescope (a h : ℝ) (N : ℕ) (f : ℝ → ℝ) :
    (∑ i∈Finset.range N, f (a+((i+1 : ℕ) : ℝ)*h))-
      (∑ i∈Finset.range N, f (a+(i : ℝ)*h))=f (a+N*h)-f a := by
  rw [← Finset.sum_sub_distrib]
  simpa only [Nat.cast_zero,zero_mul,add_zero] using
    Finset.sum_range_sub (fun i : ℕ => f (a+(i : ℝ)*h)) N

theorem composite_four (a h : ℝ) (hh : h≠0) {N : ℕ} (hN : 0<N) (f : ℕ → ℝ → ℝ)
    (hc : ∀ n≤4, Continuous (f n)) (hd : ∀ n<4, ∀ x, HasDerivAt (f n) (f (n+1) x) x) :
    trapezoidal_error (f 0) N a (a+N*h)=
      h^2/12*(f 1 (a+N*h)-f 1 a)-h^4/720*(f 3 (a+N*h)-f 3 a)-compositeRemainder a h N 4 (f 4) := by
  rw [← sum_cellError a h hN (f 0) (hc 0 (by omega))]
  simp_rw [cellError_four _ h hh f hc hd,mesh_step]
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,mesh_telescope,
    Nat.cast_zero,zero_mul,add_zero,compositeRemainder]

theorem composite_six (a h : ℝ) (hh : h≠0) {N : ℕ} (hN : 0<N) (f : ℕ → ℝ → ℝ)
    (hc : ∀ n≤6, Continuous (f n)) (hd : ∀ n<6, ∀ x, HasDerivAt (f n) (f (n+1) x) x) :
    trapezoidal_error (f 0) N a (a+N*h)=
      h^2/12*(f 1 (a+N*h)-f 1 a)-h^4/720*(f 3 (a+N*h)-f 3 a)+
        h^6/30240*(f 5 (a+N*h)-f 5 a)-compositeRemainder a h N 6 (f 6) := by
  rw [← sum_cellError a h hN (f 0) (hc 0 (by omega))]
  simp_rw [cellError_six _ h hh f hc hd,mesh_step]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,mesh_telescope,
    Nat.cast_zero,zero_mul,add_zero,compositeRemainder]

end
end SpanningTreeIsoperimetry.RectangularQuadrature
