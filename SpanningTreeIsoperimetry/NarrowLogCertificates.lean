import SpanningTreeIsoperimetry.NarrowEntropyBounds

/-! Short exact logarithm certificates after dyadic rescaling. -/
namespace SpanningTreeIsoperimetry.NarrowLogCertificates
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def logSum (y : ℝ) : ℝ := ∑ j∈Finset.range 12,
  2*(1/(2*(j : ℝ)+1))*((y-1)/(y+1))^(2*j+1)

theorem logSum_le {y : ℝ} (hy : 1≤y) : logSum y≤Real.log y := by
  have hy0 : 0≤y-1 := by linarith
  have hs := Real.hasSum_log_one_add hy0
  have h1 : 1+(y-1)=y := by ring
  have h2 : (y-1)+2=y+1 := by ring
  rw [h1,h2] at hs
  exact sum_le_hasSum (Finset.range 12) (fun j _ => by positivity) hs

theorem log_two_upper : Real.log 2<(6931471806 : ℝ)/10000000000 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤6931471806/10000000000) 24
  norm_num [Finset.sum_range_succ,Nat.factorial] at hs
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ)<2)).mpr
  linarith

theorem dyadic_lower {x L : ℝ} (n : ℕ) (hx : 0<x) (hy : 1≤x/2^n)
    (hcert : L-(n : ℝ)*(6931471805/10000000000)<logSum (x/2^n)) : L<Real.log x := by
  have hl := logSum_le hy
  rw [Real.log_div hx.ne' (pow_ne_zero n (by norm_num : (2 : ℝ)≠0)),Real.log_pow] at hl
  have hn := mul_le_mul_of_nonneg_left CornerNumericBounds.log_two_lower.le (Nat.cast_nonneg (α := ℝ) n)
  linarith only [hcert,hl,hn]

theorem dyadic_upper {x U : ℝ} (n : ℕ) (hx : 0<x)
    (hu : 0≤U-(n : ℝ)*(6931471806/10000000000))
    (hcert : x/2^n<∑ j∈Finset.range 24,
      (U-(n : ℝ)*(6931471806/10000000000))^j/(Nat.factorial j : ℝ)) : Real.log x<U := by
  have hs := Real.sum_le_exp_of_nonneg hu 24
  have hy : 0<x/2^n := by positivity
  have hl := (Real.log_lt_iff_lt_exp hy).mpr (hcert.trans_le hs)
  rw [Real.log_div hx.ne' (pow_ne_zero n (by norm_num : (2 : ℝ)≠0)),Real.log_pow] at hl
  have hn := mul_le_mul_of_nonneg_left log_two_upper.le (Nat.cast_nonneg (α := ℝ) n)
  linarith only [hl,hn]

theorem energy_bounds_of_exact {E d k lo hi dLo dHi : ℝ} (hk : 0≤k)
    (he : E= -Real.log d-k*SquareMaximality.squareLatticeEntropy)
    (hpos : 0<dLo) (hd : dLo<d ∧ d<dHi)
    (hl : (1166243617/1000000000)*k+lo<Real.log (dHi⁻¹))
    (hu : Real.log (dLo⁻¹)<(1166243615/1000000000)*k+hi) : lo<E ∧ E<hi := by
  have hp : 0<d := hpos.trans hd.1
  have hlogL := Real.log_lt_log hp hd.2
  have hlogU := Real.log_lt_log hpos hd.1
  rw [Real.log_inv] at hl hu
  have hEL := mul_le_mul_of_nonneg_left NarrowEntropyBounds.entropy_lower.le hk
  have hEU := mul_le_mul_of_nonneg_left NarrowEntropyBounds.entropy_upper.le hk
  rw [he]
  constructor <;> nlinarith only [hl,hu,hlogL,hlogU,hEL,hEU]

end
end SpanningTreeIsoperimetry.NarrowLogCertificates
