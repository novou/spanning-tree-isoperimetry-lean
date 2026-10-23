module

public import SpanningTreeIsoperimetry.BoundaryShortWeight

@[expose] public section

/-! Algebraic lower profiles after multiplying the inverse-minor polynomial
by the proved transformed boundary weight. -/
namespace SpanningTreeIsoperimetry.BoundaryShortPolynomial
open Set BoundaryShortWeight
noncomputable section

theorem strip_profile {t w P : ℝ} (ht : t∈Ioc (0 : ℝ) 1)
    (hw : t^3*(1+t^2/5)≤w)
    (hP : (73/6 : ℝ)-(43/2)*(Real.cosh t-1)+12*(Real.cosh t-1)^2<P) :
    t^3*((73/6 : ℝ)-(1127/120)*t^2)<w*P := by
  have ht0 : 0 < t := ht.1
  let x := Real.cosh t-1
  have hlo : t^2/2≤x := by have h := cosh_lower_four t; dsimp [x]; nlinarith [sq_nonneg (t^2)]
  have hhi : x≤(11/20 : ℝ)*t^2 := cosh_upper_quadratic ⟨ht.1.le,ht.2⟩
  have hs := pow_le_pow_left₀ (show 0≤t^2/2 by positivity) hlo 2
  let Q : ℝ := 73/6-(473/40)*t^2+3*t^4
  have hQ : Q<P := by dsimp only [Q]; change 73/6-(43/2)*x+12*x^2<P at hP; nlinarith only [hP,hhi,hs]
  have ht2 : t^2≤1 := pow_le_one₀ ht.1.le ht.2
  have hQ0 : 0 < Q := by dsimp only [Q]; nlinarith only [ht2,sq_nonneg (t^2)]
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  have h1 := mul_lt_mul_of_pos_left hQ hw0
  have h2 := mul_le_mul_of_nonneg_right hw hQ0.le
  have hpoly : 0≤t^3*(1+t^2/5)*Q-t^3*((73/6 : ℝ)-(1127/120)*t^2) := by
    dsimp only [Q]
    ring_nf
    positivity
  nlinarith only [h1,h2,hpoly]

theorem square_profile {t w P : ℝ} (ht : t∈Ioc (0 : ℝ) 1)
    (hw : t^3*(1+t^2/5)≤w)
    (hP : (40 : ℝ)-36*(Real.cosh t-1)^2<P) :
    t^3*(40+(29/5 : ℝ)*t^2-11*t^4)<w*P := by
  have ht0 : 0 < t := ht.1
  let x := Real.cosh t-1
  have hx0 : 0≤x := by dsimp [x]; linarith [Real.one_le_cosh t]
  have hhi : x≤(11/20 : ℝ)*t^2 := cosh_upper_quadratic ⟨ht.1.le,ht.2⟩
  have hs := pow_le_pow_left₀ hx0 hhi 2
  let Q : ℝ := 40-(1089/100)*t^4
  have hQ : Q<P := by dsimp only [Q]; change 40-36*x^2<P at hP; nlinarith only [hP,hs]
  have ht4 : t^4≤1 := pow_le_one₀ ht.1.le ht.2
  have hQ0 : 0 < Q := by dsimp only [Q]; linarith
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  have h1 := mul_lt_mul_of_pos_left hQ hw0
  have h2 := mul_le_mul_of_nonneg_right hw hQ0.le
  have hcoef : 0≤(11/5 : ℝ)+(11/100)*t^2-(1089/500)*t^4 := by nlinarith only [ht4,sq_nonneg t]
  have hpoly : 0≤t^3*(1+t^2/5)*Q-t^3*(40+(29/5 : ℝ)*t^2-11*t^4) := by
    have h := mul_nonneg (pow_nonneg ht.1.le 5) hcoef
    dsimp only [Q]
    nlinarith only [h]
  nlinarith only [h1,h2,hpoly]

end
end SpanningTreeIsoperimetry.BoundaryShortPolynomial
