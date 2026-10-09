import Mathlib.Analysis.Fourier.AddCircle

/-! Fourier coefficients of a continuous even2pi-periodic real function,
identified with its actual half-interval cosine integrals. -/
namespace SpanningTreeIsoperimetry.EvenPeriodicFourier
open Set MeasureTheory AddCircle
open scoped ComplexConjugate
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance : Fact (0<(2*Real.pi : ℝ)) := ⟨by positivity⟩

def cosineCoeff (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  (1/Real.pi)*(∫ θ in (0 : ℝ)..Real.pi,f θ*Real.cos ((j : ℝ)*θ))

theorem periodic_complex {f : ℝ → ℝ} (hp : Function.Periodic f (2*Real.pi)) :
    Function.Periodic (fun x => (f x : ℂ)) (2*Real.pi) := by
  intro x
  exact congrArg Complex.ofReal (hp x)

def circleMap (f : ℝ → ℝ) (hc : Continuous f) (hp : Function.Periodic f (2*Real.pi)) :
    C(AddCircle (2*Real.pi),ℂ) where
  toFun := (periodic_complex hp).lift
  continuous_toFun := by
    unfold Function.Periodic.lift
    exact (Complex.continuous_ofReal.comp hc).quotient_liftOn' _

@[simp] theorem circleMap_coe (f : ℝ → ℝ) (hc : Continuous f)
    (hp : Function.Periodic f (2*Real.pi)) (x : ℝ) :
    circleMap f hc hp (x : AddCircle (2*Real.pi))=(f x : ℂ) := rfl

theorem fourier_frequency (n : ℤ) (x : ℝ) :
    fourier n (x : AddCircle (2*Real.pi))=Complex.exp ((((n : ℝ)*x : ℝ) : ℂ)*Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  <;> ring

theorem fourier_pair (n : ℤ) (x : ℝ) :
    fourier (-n) ((-x : ℝ) : AddCircle (2*Real.pi))+
      fourier (-n) (x : AddCircle (2*Real.pi))=((2*Real.cos ((n : ℝ)*x) : ℝ) : ℂ) := by
  rw [fourier_frequency,fourier_frequency]
  have hl : (((-n : ℤ) : ℝ)*(-x))=(n : ℝ)*x := by push_cast; ring
  have hr : (((-n : ℤ) : ℝ)*x)= -((n : ℝ)*x) := by push_cast; ring
  rw [hl,hr,Complex.ofReal_neg]
  simp only [Complex.exp_mul_I,Complex.cos_neg,Complex.sin_neg]
  simp only [← Complex.ofReal_cos,← Complex.ofReal_sin]
  push_cast
  ring

theorem cos_int_natAbs (n : ℤ) (x : ℝ) :
    Real.cos ((n : ℝ)*x)=Real.cos ((n.natAbs : ℝ)*x) := by
  cases n with
  | ofNat n => rfl
  | negSucc n => simp only [Int.cast_negSucc,Int.natAbs_negSucc,neg_mul,Real.cos_neg]

theorem fourier_coefficient (f : ℝ → ℝ) (hc : Continuous f)
    (hp : Function.Periodic f (2*Real.pi)) (he : Function.Even f) (n : ℤ) :
    fourierCoeff (circleMap f hc hp) n=(cosineCoeff f n.natAbs : ℂ) := by
  let H : ℝ → ℂ := fun x => fourier (-n) (x : AddCircle (2*Real.pi))*(f x : ℂ)
  have hH : Continuous H :=
    ((fourier (-n)).continuous.comp (AddCircle.continuous_mk' _)).mul (Complex.continuous_ofReal.comp hc)
  have hsplit : (∫ x in -Real.pi..Real.pi,H x)=
      ∫ x in (0 : ℝ)..Real.pi,H (-x)+H x := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hH.intervalIntegrable (a := -Real.pi) (b := 0)) (hH.intervalIntegrable (a := 0) (b := Real.pi))
    have hneg := intervalIntegral.integral_comp_neg (f := H) (a := (0 : ℝ)) (b := Real.pi)
    simp only [neg_zero] at hneg
    rw [← hadd,← hneg]
    have hi : IntervalIntegrable (fun x => H (-x)) volume (0 : ℝ) Real.pi :=
      (hH.comp continuous_neg).intervalIntegrable _ _
    exact (intervalIntegral.integral_add hi (hH.intervalIntegrable _ _)).symm
  have hpair : (fun x => H (-x)+H x)=
      (fun x => ((2*(f x*Real.cos ((n.natAbs : ℝ)*x)) : ℝ) : ℂ)) := by
    funext x
    dsimp only [H]
    rw [he x,← add_mul,fourier_pair,cos_int_natAbs]
    push_cast
    ring
  rw [fourierCoeff_eq_intervalIntegral (circleMap f hc hp) n (-Real.pi)]
  simp only [circleMap_coe,smul_eq_mul]
  rw [show -Real.pi+2*Real.pi=Real.pi by ring]
  change (1/(2*Real.pi) : ℝ) • (∫ x in -Real.pi..Real.pi,H x)=_
  rw [hsplit,hpair,intervalIntegral.integral_ofReal,intervalIntegral.integral_const_mul]
  unfold cosineCoeff
  simp only [Complex.real_smul,← Complex.ofReal_mul]
  congr 1
  field_simp
  <;> ring

theorem fourier_nat_pi (n : ℕ) :
    fourier (n : ℤ) (Real.pi : AddCircle (2*Real.pi))=(((-1 : ℝ)^n) : ℂ) := by
  rw [fourier_frequency]
  have he : ((((n : ℤ) : ℝ)*Real.pi : ℝ) : ℂ)*Complex.I=(n : ℂ)*(Real.pi*Complex.I) := by
    push_cast
    ring
  rw [he,Complex.exp_nat_mul,Complex.exp_pi_mul_I]
  norm_cast

theorem fourier_pi (n : ℤ) :
    fourier n (Real.pi : AddCircle (2*Real.pi))=(((-1 : ℝ)^n.natAbs) : ℂ) := by
  cases n with
  | ofNat n => exact fourier_nat_pi n
  | negSucc n =>
    change fourier (-((n+1 : ℕ) : ℤ)) (Real.pi : AddCircle (2*Real.pi))=_
    rw [fourier_neg,fourier_nat_pi]
    simp

end
end SpanningTreeIsoperimetry.EvenPeriodicFourier
