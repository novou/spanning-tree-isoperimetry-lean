module

public import SpanningTreeIsoperimetry.RegularizedFourierDecay
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.PSeries

@[expose] public section

/-! Actual weighted absolute summability of the regularized logarithmic
strip symbol. A third integration by parts suffices for every z>4. -/
namespace SpanningTreeIsoperimetry.RegularizedFourierWeighted
open RegularizedStripSymbol RegularizedSymbolVariation Set MeasureTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def third (z : ℝ) : ℝ → ℝ := iteratedDeriv 3 (gammaZ z)
def thirdMass (z : ℝ) : ℝ := (∫ θ in (0 : ℝ)..Real.pi,|third z θ|)/Real.pi

theorem second_eq_iterated {z : ℝ} (hz : 4<z) : second z=iteratedDeriv 2 (gammaZ z) := by
  have h1 : iteratedDeriv 1 (gammaZ z)=first z := by
    rw [iteratedDeriv_one]
    funext θ
    exact (hasDerivAt_gamma hz θ).deriv
  rw [show (2 : ℕ)=1+1 by rfl,iteratedDeriv_succ,h1]
  funext θ
  exact (hasDerivAt_first hz θ).deriv.symm

theorem continuous_third {z : ℝ} (hz : 4<z) : Continuous (third z) := by
  change Continuous (iteratedDeriv 3 (gammaZ z))
  exact (contDiff_gammaZ hz).continuous_iteratedDeriv 3 (by simp)

theorem hasDerivAt_second {z : ℝ} (hz : 4<z) (θ : ℝ) :
    HasDerivAt (second z) (third z θ) θ := by
  have hd := (contDiff_gammaZ hz).differentiable_iteratedDeriv 2 (by exact WithTop.coe_lt_top (2 : ℕ∞))
  have h : HasDerivAt (iteratedDeriv 2 (gammaZ z)) (third z θ) θ := by
    simpa only [third,iteratedDeriv_succ] using (hd θ).hasDerivAt
  simpa only [← second_eq_iterated hz] using h

theorem thirdMass_nonneg (z : ℝ) : 0≤thirdMass z := by
  apply div_nonneg _ Real.pi_pos.le
  exact intervalIntegral.integral_nonneg Real.pi_pos.le (fun _ _ => abs_nonneg _)

theorem coefficient_thrice_by_parts {z : ℝ} (hz : 4<z) {j : ℕ} (hj : 0<j) :
    coefficientZ z j= -(∫ θ in (0 : ℝ)..Real.pi,third z θ*Real.sin ((j : ℝ)*θ))/
      (Real.pi*(j : ℝ)^3) := by
  have hj0 : (j : ℝ)≠0 := by exact_mod_cast hj.ne'
  have hs : Continuous (fun θ : ℝ => Real.sin ((j : ℝ)*θ)) := by fun_prop
  have hc : Continuous (fun θ : ℝ => Real.cos ((j : ℝ)*θ)*(j : ℝ)) := by fun_prop
  have hd (θ : ℝ) : HasDerivAt (fun x : ℝ => Real.sin ((j : ℝ)*x))
      (Real.cos ((j : ℝ)*θ)*(j : ℝ)) θ := by
    simpa using ((hasDerivAt_id θ).const_mul (j : ℝ)).sin
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := Real.pi) (continuous_second hz).continuousOn hs.continuousOn
    (fun θ _ => hasDerivAt_second hz θ) (fun θ _ => hd θ)
    ((continuous_third hz).intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  have hsin : Real.sin ((j : ℝ)*Real.pi)=0 := Real.sin_nat_mul_pi j
  simp only [hsin,mul_zero,Real.sin_zero,sub_zero,zero_sub] at hi
  have hp : (∫ θ in (0 : ℝ)..Real.pi,second z θ*(Real.cos ((j : ℝ)*θ)*(j : ℝ)))=
      (∫ θ in (0 : ℝ)..Real.pi,second z θ*Real.cos ((j : ℝ)*θ))*(j : ℝ) := by
    simp only [← mul_assoc,intervalIntegral.integral_mul_const]
  rw [hp] at hi
  have he : (∫ θ in (0 : ℝ)..Real.pi,second z θ*Real.cos ((j : ℝ)*θ))=
      -(∫ θ in (0 : ℝ)..Real.pi,third z θ*Real.sin ((j : ℝ)*θ))/(j : ℝ) :=
    (eq_div_iff hj0).mpr hi
  rw [RegularizedFourierDecay.coefficient_twice_by_parts hz hj,he]
  field_simp
  <;> ring

/-- The constant is the actual third-derivative integral, with no supplied
regularity or variation bound. -/
theorem coefficient_cubic_bound {z : ℝ} (hz : 4<z) {j : ℕ} (hj : 0<j) :
    |coefficientZ z j|≤thirdMass z/(j : ℝ)^3 := by
  have hg := continuous_third hz
  have hp : Continuous (fun θ : ℝ => third z θ*Real.sin ((j : ℝ)*θ)) := hg.mul (by fun_prop)
  have hnum : |∫ θ in (0 : ℝ)..Real.pi,third z θ*Real.sin ((j : ℝ)*θ)|≤
      (∫ θ in (0 : ℝ)..Real.pi,|third z θ|) := by
    apply (intervalIntegral.abs_integral_le_integral_abs Real.pi_pos.le).trans
    apply intervalIntegral.integral_mono_on Real.pi_pos.le
      (hp.abs.intervalIntegrable _ _) (hg.abs.intervalIntegrable _ _)
    intro θ _
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  rw [coefficient_thrice_by_parts hz hj,abs_div,abs_neg,abs_of_pos (by positivity : 0<Real.pi*(j : ℝ)^3)]
  simpa only [thirdMass,div_div] using
    div_le_div_of_nonneg_right hnum (by positivity : 0≤Real.pi*(j : ℝ)^3)

theorem weighted_coefficients_summable {z : ℝ} (hz : 4<z) :
    Summable (fun n : ℕ => (1+((n+1 : ℕ) : ℝ))*|coefficientZ z (n+1)|) := by
  have hs := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by decide : 1<2))
  have hmajor : Summable (fun n : ℕ => 2*thirdMass z/((n+1 : ℕ) : ℝ)^2) := by
    convert hs.mul_left (2*thirdMass z) using 1
    funext n
    ring
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hmajor
  intro n
  have hn : (0 : ℝ)<(n+1 : ℕ) := by positivity
  have hn1 : (1 : ℝ)≤(n+1 : ℕ) := by exact_mod_cast (show 1≤n+1 by omega)
  have hfac : (1+((n+1 : ℕ) : ℝ))/((n+1 : ℕ) : ℝ)≤2 := (div_le_iff₀ hn).mpr (by linarith)
  calc
    (1+((n+1 : ℕ) : ℝ))*|coefficientZ z (n+1)|≤
        (1+((n+1 : ℕ) : ℝ))*(thirdMass z/((n+1 : ℕ) : ℝ)^3) :=
      mul_le_mul_of_nonneg_left (coefficient_cubic_bound hz (by omega)) (by positivity)
    _=((1+((n+1 : ℕ) : ℝ))/((n+1 : ℕ) : ℝ))*(thirdMass z/((n+1 : ℕ) : ℝ)^2) := by
      field_simp
      <;> ring
    _≤2*(thirdMass z/((n+1 : ℕ) : ℝ)^2) :=
      mul_le_mul_of_nonneg_right hfac (div_nonneg (thirdMass_nonneg z) (sq_nonneg _))
    _=2*thirdMass z/((n+1 : ℕ) : ℝ)^2 := by ring

def positivePart (z : ℝ) (n : ℕ) : ℝ := if n=0 then 0 else coefficientZ z n

@[simp] theorem positivePart_zero (z : ℝ) : positivePart z 0=0 := by simp [positivePart]
@[simp] theorem positivePart_succ (z : ℝ) (n : ℕ) : positivePart z (n+1)=coefficientZ z (n+1) := by simp [positivePart]

theorem positivePart_weighted_summable {z : ℝ} (hz : 4<z) :
    Summable (fun n : ℕ => (1+(n : ℝ))*|positivePart z n|) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [positivePart_succ] using weighted_coefficients_summable hz

end
end SpanningTreeIsoperimetry.RegularizedFourierWeighted
