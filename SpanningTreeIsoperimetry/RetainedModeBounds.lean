import SpanningTreeIsoperimetry.AngularKernelTaylor

/-! Exact low-mode exponential bounds for the sharp rectangular remainder.
Rational lower bounds for exp(gamma) are proved from the exact cosh equation. -/
namespace SpanningTreeIsoperimetry.RetainedModeBounds

open RectangularRemainder AngularKernelTaylor SquareMaximality.Rectangle
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem cosh_gamma {θ : ℝ} (hθ : θ∈Set.Icc 0 Real.pi) :
    Real.cosh (gamma θ)=2-Real.cos θ := by
  rw [gamma_eq_kernel hθ,Product.cosh_kernel]
  congr 2
  field_simp [Real.pi_ne_zero]

/-- Rational lower exponent values follow from the exact cosh identity,
without approximating arcosh or assuming a numerical mode table. -/
theorem exp_gamma_power_lower {θ a D : ℝ} {n : ℕ} (hθ : θ∈Set.Icc 0 Real.pi)
    (ha : 1≤a) (hn : 0<n) (hcosh : (a+1/a)/2<2-Real.cos θ) (hpow : D<a^n) :
    D<Real.exp ((n : ℝ)*gamma θ) := by
  have ha0 : 0<a := lt_of_lt_of_le zero_lt_one ha
  have hloga : 0≤Real.log a := Real.log_nonneg ha
  have hγ : 0≤gamma θ := gamma_nonneg hθ
  have hid : Real.cosh (Real.log a)=(a+1/a)/2 := by
    rw [Real.cosh_eq,Real.exp_log ha0,Real.exp_neg,Real.exp_log ha0]
    simp only [one_div]
  have hc : Real.cosh (Real.log a)<Real.cosh (gamma θ) := by
    rw [hid,cosh_gamma hθ]
    exact hcosh
  rw [Real.cosh_lt_cosh,abs_of_nonneg hloga,abs_of_nonneg hγ] at hc
  have he : a<Real.exp (gamma θ) := by
    simpa only [Real.exp_log ha0] using Real.exp_lt_exp.mpr hc
  have hp : a^n<(Real.exp (gamma θ))^n := by gcongr
  exact hpow.trans (by simpa only [Real.exp_nat_mul] using hp)

theorem first_mode_four : (396 : ℝ)<Real.exp (8*gamma (Real.pi/4)) := by
  apply exp_gamma_power_lower (n := 8) (a := 10561/5000)
  · constructor <;> nlinarith [Real.pi_pos]
  · norm_num
  · norm_num
  · rw [Real.cos_pi_div_four]
    have hsq : Real.sqrt 2≤(70711 : ℝ)/50000 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤2),Real.sqrt_nonneg (2 : ℝ)]
    norm_num
    linarith
  · norm_num

theorem second_mode_four : (37600 : ℝ)<Real.exp (8*gamma (Real.pi/2)) := by
  apply exp_gamma_power_lower (n := 8) (a := 933/250)
  · constructor <;> nlinarith [Real.pi_pos]
  · norm_num
  · norm_num
  · norm_num [Real.cos_pi_div_two]
  · norm_num

theorem third_mode_four : (550000 : ℝ)<Real.exp (8*gamma (3*Real.pi/4)) := by
  apply exp_gamma_power_lower (n := 8) (a := 261/50)
  · constructor <;> nlinarith [Real.pi_pos]
  · norm_num
  · norm_num
  · rw [show 3*Real.pi/4=Real.pi-Real.pi/4 by ring,Real.cos_pi_sub,Real.cos_pi_div_four]
    have hsq : (707 : ℝ)/500≤Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤2),Real.sqrt_nonneg (2 : ℝ)]
    norm_num
    linarith
  · norm_num

theorem fourth_mode_five : (22000000 : ℝ)<Real.exp (10*gamma (4*Real.pi/5)) := by
  apply exp_gamma_power_lower (n := 10) (a := 543/100)
  · constructor <;> nlinarith [Real.pi_pos]
  · norm_num
  · norm_num
  · rw [show 4*Real.pi/5=Real.pi-Real.pi/5 by ring,Real.cos_pi_sub,Real.cos_pi_div_five]
    have hsq : (559 : ℝ)/250≤Real.sqrt 5 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤5),Real.sqrt_nonneg (5 : ℝ)]
    norm_num
    linarith
  · norm_num

theorem first_mode_three : (321 : ℝ)<Real.exp (6*gamma (Real.pi/3)) := by
  apply exp_gamma_power_lower (n := 6) (a := 2617/1000)
  · constructor <;> nlinarith [Real.pi_pos]
  · norm_num
  · norm_num
  · norm_num [Real.cos_pi_div_three]
  · norm_num

theorem second_mode_three : (12000 : ℝ)<Real.exp (6*gamma (2*Real.pi/3)) := by
  apply exp_gamma_power_lower (n := 6) (a := 479/100)
  · constructor <;> nlinarith [Real.pi_pos]
  · norm_num
  · norm_num
  · rw [show 2*Real.pi/3=Real.pi-Real.pi/3 by ring,Real.cos_pi_sub]
    norm_num [Real.cos_pi_div_three]
  · norm_num

/-- Every longer admissible rectangle inherits its fixed low-mode bound. -/
theorem exp_mode_lower_transfer {m r s j D : ℝ} (hm : 0<m) (hmr : m≤r)
    (hrs : r≤s) (hj : 0<j) (hjm : j≤m)
    (hD : D<Real.exp (2*m*gamma (Real.pi*j/m))) :
    D<Real.exp (2*s*gamma (Real.pi*j/r)) := by
  have hr : 0<r := hm.trans_le hmr
  have hs : 0<s := hr.trans_le hrs
  have hθ : Real.pi*j/r∈Set.Icc 0 Real.pi := by
    refine ⟨by positivity,(div_le_iff₀ hr).mpr ?_⟩
    exact mul_le_mul_of_nonneg_left (hjm.trans hmr) Real.pi_pos.le
  have hg := gamma_nonneg hθ
  have hscale := scaled_gamma_mono hm hmr (mul_pos Real.pi_pos hj)
    (mul_le_mul_of_nonneg_left hjm Real.pi_pos.le)
  have hlong := mul_le_mul_of_nonneg_right hrs hg
  apply hD.trans_le
  apply Real.exp_le_exp.mpr
  nlinarith

end
end SpanningTreeIsoperimetry.RetainedModeBounds
