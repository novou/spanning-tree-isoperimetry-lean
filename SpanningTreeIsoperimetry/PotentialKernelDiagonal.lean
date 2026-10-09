import SpanningTreeIsoperimetry.PotentialKernelImages
import SpanningTreeIsoperimetry.PeriodicSquareRotation
import SpanningTreeIsoperimetry.PoissonCosineIntegral
import SpanningTreeIsoperimetry.PotentialDiagonalSine

/-! Exact diagonal values of the actual integral-defined lattice potential.
The proof uses a bounded periodic-square rotation, an elementary Poisson
cosine integral and a finite sine sum. -/
namespace SpanningTreeIsoperimetry.PotentialKernelDiagonal
open PotentialKernelIntegral PotentialKernelHarmonic PotentialKernelImages
open PotentialDiagonalSine PeriodicSquareRotation MeasureTheory Set
open scoped BigOperators Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def mixed (j : ℕ) (x y : ℝ) : ℝ :=
  Real.sin ((j : ℝ)*x)*Real.sin ((j : ℝ)*y)/denominator x y

def phase (j : ℕ) (x y : ℝ) : ℝ :=
  (1-Real.cos ((j : ℝ)*(x+y)))/denominator x y

def rotated (j : ℕ) (x y : ℝ) : ℝ :=
  (1-Real.cos (2*(j : ℝ)*x))/(1-Real.cos x*Real.cos y)

theorem phase_eq (j : ℕ) (x y : ℝ) : phase j x y=density j j x y+mixed j x y := by
  unfold phase density mixed
  rw [mul_add,Real.cos_add]
  ring

theorem mixed_bound (j : ℕ) (x y : ℝ) : |mixed j x y|≤2*(j : ℝ)^2 := by
  unfold mixed
  rw [abs_div,abs_of_nonneg (denominator_nonneg x y)]
  by_cases hd : denominator x y=0
  · rw [hd,div_zero]
    positivity
  have hd0 : 0<denominator x y := lt_of_le_of_ne (denominator_nonneg x y) (Ne.symm hd)
  apply (div_le_iff₀ hd0).mpr
  have hmul := mul_le_mul (BoundaryKernelBounds.abs_sin_nat_mul_le j x)
    (BoundaryKernelBounds.abs_sin_nat_mul_le j y) (abs_nonneg _) (by positivity)
  have hp := mul_le_mul_of_nonneg_left (abs_sine_pair_le x y) (sq_nonneg (j : ℝ))
  rw [abs_mul] at hp ⊢
  nlinarith only [hmul,hp]

theorem phase_bound (j : ℕ) (x y : ℝ) : |phase j x y|≤6*(j : ℝ)^2 := by
  rw [phase_eq]
  have h := abs_add_le (density j j x y) (mixed j x y)
  rw [abs_of_nonneg (density_bounds j j x y).1] at h
  nlinarith only [h,(density_bounds j j x y).2,mixed_bound j x y]

theorem phase_measurable (j : ℕ) : Measurable (fun p : ℝ × ℝ => phase j p.1 p.2) := by
  unfold phase denominator
  fun_prop

theorem cos_frequency_periodic (j : ℕ) (x : ℝ) :
    Real.cos ((j : ℝ)*(x+2*Real.pi))=Real.cos ((j : ℝ)*x) := by
  rw [mul_add]
  exact Real.cos_add_nat_mul_two_pi ((j : ℝ)*x) j

theorem cos_frequency_reflection (j : ℕ) (x : ℝ) :
    Real.cos ((j : ℝ)*(2*Real.pi-x))=Real.cos ((j : ℝ)*x) := by
  rw [mul_sub]
  exact Real.cos_nat_mul_two_pi_sub ((j : ℝ)*x) j

theorem sin_frequency_reflection (j : ℕ) (x : ℝ) :
    Real.sin ((j : ℝ)*(2*Real.pi-x))= -Real.sin ((j : ℝ)*x) := by
  rw [mul_sub]
  exact Real.sin_nat_mul_two_pi_sub ((j : ℝ)*x) j

theorem cos_reflection (x : ℝ) : Real.cos (2*Real.pi-x)=Real.cos x := by
  simpa only [Nat.cast_one,one_mul] using cos_frequency_reflection 1 x

theorem phase_periodic_left (j : ℕ) (y : ℝ) : Function.Periodic (fun x => phase j x y) (2*Real.pi) := by
  intro x
  change phase j (x+2*Real.pi) y=phase j x y
  unfold phase denominator
  rw [show (x+2*Real.pi)+y=(x+y)+2*Real.pi by ring,cos_frequency_periodic,Real.cos_add_two_pi]

theorem phase_periodic_right (j : ℕ) (x : ℝ) : Function.Periodic (phase j x) (2*Real.pi) := by
  intro y
  unfold phase denominator
  rw [show x+(y+2*Real.pi)=(x+y)+2*Real.pi by ring,cos_frequency_periodic,Real.cos_add_two_pi]

theorem density_reflect_left (j : ℕ) (x y : ℝ) : density j j (2*Real.pi-x) y=density j j x y := by
  unfold density denominator
  rw [cos_frequency_reflection,cos_reflection]

theorem density_reflect_right (j : ℕ) (x y : ℝ) : density j j x (2*Real.pi-y)=density j j x y := by
  unfold density denominator
  rw [cos_frequency_reflection,cos_reflection]

theorem mixed_reflect_right (j : ℕ) (x y : ℝ) : mixed j x (2*Real.pi-y)= -mixed j x y := by
  unfold mixed denominator
  rw [sin_frequency_reflection,cos_reflection]
  ring

theorem phase_average (j : ℕ) (x y : ℝ) :
    phase j x y+phase j x (2*Real.pi-y)=2*density j j x y := by
  rw [phase_eq,phase_eq,density_reflect_right,mixed_reflect_right]
  ring

theorem phase_inner_eq_density (j : ℕ) (x : ℝ) :
    (∫ y in (0 : ℝ)..2*Real.pi,phase j x y)=∫ y in (0 : ℝ)..2*Real.pi,density j j x y := by
  have hm : Measurable (phase j x) := by
    unfold phase denominator
    fun_prop
  have hmr : Measurable (fun y => phase j x (2*Real.pi-y)) := by
    unfold phase denominator
    fun_prop
  have hi := interval_integrable hm (phase_bound j x) 0 (2*Real.pi)
  have hir := interval_integrable hmr (fun y => phase_bound j x (2*Real.pi-y)) 0 (2*Real.pi)
  have h := intervalIntegral.integral_congr (μ := volume) (a := (0 : ℝ)) (b := 2*Real.pi)
    (f := fun y => phase j x y+phase j x (2*Real.pi-y))
    (g := fun y => 2*density j j x y) (fun y _ => phase_average j x y)
  rw [intervalIntegral.integral_add hi hir,intervalIntegral.integral_const_mul,
    integral_reflection] at h
  linarith only [h]

theorem phase_square_eq_density (j : ℕ) :
    (∫ x in (0 : ℝ)..2*Real.pi,∫ y in (0 : ℝ)..2*Real.pi,phase j x y)=
      ∫ x in (0 : ℝ)..2*Real.pi,∫ y in (0 : ℝ)..2*Real.pi,density j j x y := by
  apply intervalIntegral.integral_congr
  intro x _
  exact phase_inner_eq_density j x

theorem phase_rotation (j : ℕ) (x y : ℝ) : phase j (x+y) (x-y)=rotated j x y := by
  unfold phase denominator rotated
  rw [show (j : ℝ)*((x+y)+(x-y))=2*(j : ℝ)*x by ring,Real.cos_add,Real.cos_sub]
  congr 1
  ring

theorem rotated_measurable (j : ℕ) : Measurable (fun p : ℝ × ℝ => rotated j p.1 p.2) := by
  unfold rotated
  fun_prop

theorem rotated_bound (j : ℕ) (x y : ℝ) : |rotated j x y|≤6*(j : ℝ)^2 := by
  rw [← phase_rotation]
  exact phase_bound j (x+y) (x-y)

theorem rotated_reflect_left (j : ℕ) (x y : ℝ) : rotated j (2*Real.pi-x) y=rotated j x y := by
  have hc := cos_frequency_reflection (2*j) x
  push_cast at hc
  unfold rotated
  rw [hc,cos_reflection]

theorem rotated_reflect_right (j : ℕ) (x y : ℝ) : rotated j x (2*Real.pi-y)=rotated j x y := by
  unfold rotated
  rw [cos_reflection]

theorem potential_diagonal_quarter (j : ℕ) : potential j j=
    (1/Real.pi^2)*∫ x in (0 : ℝ)..Real.pi,∫ y in (0 : ℝ)..Real.pi,density j j x y := by
  have hi : IntegrableOn (fun p : ℝ × ℝ => density j j p.1 p.2)
      (Icc (0 : ℝ) Real.pi ×ˢ Icc (0 : ℝ) Real.pi) (volume.prod volume) := by
    simpa only [frequencySquare,Measure.volume_eq_prod] using density_integrable j j
  have h := setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun p : ℝ × ℝ => density j j p.1 p.2) hi
  simp_rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le Real.pi_pos.le] at h
  unfold potential
  rw [frequencySquare,Measure.volume_eq_prod,h]

theorem potential_diagonal_full (j : ℕ) : potential j j=
    (1/(4*Real.pi^2))*∫ x in (0 : ℝ)..2*Real.pi,
      ∫ y in (0 : ℝ)..2*Real.pi,density j j x y := by
  have hb (x y : ℝ) : |density j j x y|≤4*(j : ℝ)^2 := by
    rw [abs_of_nonneg (density_bounds j j x y).1]
    nlinarith only [(density_bounds j j x y).2]
  have h := square_eq_four_quarter (F := density j j) (density_measurable j j) hb
    (density_reflect_left j) (density_reflect_right j)
  rw [show (2*Real.pi)/2=Real.pi by ring] at h
  rw [potential_diagonal_quarter,h]
  field_simp [Real.pi_ne_zero]
  <;> ring

theorem potential_diagonal_rotated (j : ℕ) : potential j j=
    (1/Real.pi^2)*∫ x in (0 : ℝ)..Real.pi,∫ y in (0 : ℝ)..Real.pi,rotated j x y := by
  have hr := rotation_invariant (F := phase j) (phase_measurable j) (phase_bound j)
    (phase_periodic_left j) (phase_periodic_right j)
  simp_rw [phase_rotation] at hr
  have hh := square_eq_four_quarter (F := rotated j) (rotated_measurable j) (rotated_bound j)
    (rotated_reflect_left j) (rotated_reflect_right j)
  rw [show (2*Real.pi)/2=Real.pi by ring] at hh
  rw [potential_diagonal_full,← phase_square_eq_density,← hr,hh]
  field_simp [Real.pi_ne_zero]
  <;> ring

theorem rotated_inner (j : ℕ) {x : ℝ} (hx : x∈Icc (0 : ℝ) Real.pi) :
    (∫ y in (0 : ℝ)..Real.pi,rotated j x y)=
      Real.pi*((1-Real.cos (2*(j : ℝ)*x))/Real.sin x) := by
  by_cases hx0 : x=0
  · subst x
    simp [rotated]
  by_cases hxp : x=Real.pi
  · subst x
    have hc : Real.cos (2*(j : ℝ)*Real.pi)=1 := by
      rw [show 2*(j : ℝ)*Real.pi=(j : ℝ)*(2*Real.pi) by ring,Real.cos_nat_mul_two_pi]
    simp [rotated,hc]
  have h0 : 0<x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  have hp : x<Real.pi := lt_of_le_of_ne hx.2 hxp
  have hc0 := Real.strictAntiOn_cos ⟨le_rfl,Real.pi_pos.le⟩ ⟨hx.1,hx.2⟩ h0
  have hcp := Real.strictAntiOn_cos ⟨hx.1,hx.2⟩ ⟨Real.pi_pos.le,le_rfl⟩ hp
  simp only [Real.cos_zero,Real.cos_pi] at hc0 hcp
  have hc : |Real.cos x|<1 := abs_lt.mpr ⟨hcp,hc0⟩
  have hpoisson := PoissonCosineIntegral.cosine_integral_reciprocal hc
  have hsin := Real.sin_pos_of_pos_of_lt_pi h0 hp
  have hsqrt : Real.sqrt (1-Real.cos x^2)=Real.sin x := by
    rw [← Real.abs_sin_eq_sqrt_one_sub_cos_sq,abs_of_pos hsin]
  unfold rotated
  simp only [div_eq_mul_inv]
  rw [intervalIntegral.integral_const_mul]
  have hh : (∫ y in (0 : ℝ)..Real.pi,(1-Real.cos x*Real.cos y)⁻¹)=Real.pi/Real.sin x := by
    simpa only [one_div,hsqrt] using hpoisson
  rw [hh]
  ring

/-- Reduction of the actual potential diagonal to the finite sine integral. -/
theorem potential_diagonal_integral (j : ℕ) : potential j j=diagonalIntegral j := by
  rw [potential_diagonal_rotated]
  have h : (∫ x in (0 : ℝ)..Real.pi,∫ y in (0 : ℝ)..Real.pi,rotated j x y)=
      ∫ x in (0 : ℝ)..Real.pi,Real.pi*((1-Real.cos (2*(j : ℝ)*x))/Real.sin x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact rotated_inner j (by simpa only [uIcc_of_le Real.pi_pos.le] using hx)
  rw [h,intervalIntegral.integral_const_mul]
  unfold diagonalIntegral
  field_simp [Real.pi_ne_zero]
  <;> ring

/-- Appendix B's exact diagonal potential-kernel formula. -/
theorem diagonal_formula (j : ℕ) : potential j j=(4/Real.pi)*∑ i ∈ Finset.range j,1/(2*(i : ℝ)+1) := by
  rw [potential_diagonal_integral,diagonalIntegral_eq]
  rfl

end
end SpanningTreeIsoperimetry.PotentialKernelDiagonal
