import SpanningTreeIsoperimetry.BoundarySingletonWeight
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! Quantitative transformed weight for the two-cell and square-defect
boundary corrections. -/
namespace SpanningTreeIsoperimetry.BoundaryShortWeight
open Set RectangularRemainder BoundarySingletonWeight
open scoped BigOperators
noncomputable section

theorem cosh_lower_four (t : ℝ) : t^2/2+t^4/24≤Real.cosh t-1 := by
  have h := sum_le_hasSum (Finset.range 3)
    (fun n _ => show 0≤t^(2*n)/(Nat.factorial (2*n) : ℝ) by rw [pow_mul]; positivity) (Real.hasSum_cosh t)
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  linarith

theorem cosh_upper_quadratic {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    Real.cosh t-1≤(11/20 : ℝ)*t^2 := by
  have hp := Real.exp_bound (x := t) (by rw [abs_of_nonneg ht.1]; exact ht.2) (n := 6) (by norm_num)
  have hn := Real.exp_bound (x := -t) (by rw [abs_neg,abs_of_nonneg ht.1]; exact ht.2) (n := 6) (by norm_num)
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  norm_num [Finset.sum_range_succ,Nat.factorial,abs_of_nonneg ht.1,abs_neg] at hp' hn'
  have h4 := pow_le_pow_of_le_one ht.1 ht.2 (show 2≤4 by omega)
  have h6 := pow_le_pow_of_le_one ht.1 ht.2 (show 2≤6 by omega)
  rw [Real.cosh_eq]
  nlinarith only [hp',hn',h4,h6,sq_nonneg t]

theorem transformed_weight_lower {θ : ℝ} (hθ : θ∈Icc (0 : ℝ) Real.pi) (hγ : gamma θ≤1) :
    (gamma θ)^3*(1+(gamma θ)^2/5)≤Real.sin θ*Real.sinh (gamma θ)^2 := by
  let t := gamma θ
  let x := Real.cosh t-1
  have ht : t∈Icc (0 : ℝ) 1 := ⟨gamma_nonneg hθ,hγ⟩
  have ht0 : 0≤t := ht.1
  have hx0 : 0≤x := by dsimp [x]; linarith [Real.one_le_cosh t]
  have hxlo : t^2/2+t^4/24≤x := cosh_lower_four t
  have hxhi : x≤(11/20 : ℝ)*t^2 := cosh_upper_quadratic ht
  have ht2 : t^2≤1 := pow_le_one₀ ht.1 ht.2
  have hx1 : x≤11/20 := by linarith
  have hx2 : x^2≤121/400 := by
    have h := pow_le_pow_left₀ hx0 hx1 2
    norm_num at h ⊢
    exact h
  have hpoly : 0≤(3/2 : ℝ)-2*x-x^2 := by nlinarith
  have hsin : Real.sin θ^2=x*(2-x) := by
    have hc : Real.cos θ=1-x := by
      have h := cosh_gamma θ
      dsimp only [x,t]
      linarith only [h]
    have hs := Real.sin_sq_add_cos_sq θ
    rw [hc] at hs
    nlinarith only [hs]
  have hsinh : Real.sinh t^2=x*(2+x) := by
    have hs := Real.cosh_sq_sub_sinh_sq t
    dsimp only [x]
    nlinarith only [hs]
  have hw : (Real.sin θ*Real.sinh t^2)^2=x^3*(2-x)*(2+x)^2 := by
    rw [mul_pow,hsin,hsinh]
    ring
  have hwlo : 8*x^3+(5/2 : ℝ)*x^4≤(Real.sin θ*Real.sinh t^2)^2 := by
    rw [hw]
    have h := mul_nonneg (pow_nonneg hx0 4) hpoly
    nlinarith only [h]
  let a := t^2/2+t^4/24
  have ha0 : 0≤a := by dsimp [a]; positivity
  have ha : a≤x := hxlo
  have h3 := pow_le_pow_left₀ ha0 ha 3
  have h4 := pow_le_pow_left₀ ha0 ha 4
  have hpositive : 0≤8*a^3+(5/2 : ℝ)*a^4-t^6*(1+t^2/5)^2 := by
    dsimp only [a]
    ring_nf
    positivity
  have hsq : (t^3*(1+t^2/5))^2≤(Real.sin θ*Real.sinh t^2)^2 := by
    nlinarith only [hwlo,h3,h4,hpositive]
  have hleft : 0≤t^3*(1+t^2/5) := by positivity
  have hright : 0≤Real.sin θ*Real.sinh t^2 :=
    mul_nonneg (Real.sin_nonneg_of_mem_Icc hθ) (sq_nonneg _)
  exact (sq_le_sq₀ hleft hright).mp hsq

end
end SpanningTreeIsoperimetry.BoundaryShortWeight
