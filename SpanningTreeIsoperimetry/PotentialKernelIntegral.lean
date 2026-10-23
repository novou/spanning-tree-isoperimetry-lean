module

public import SpanningTreeIsoperimetry.BoundaryKernelBounds
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-! An integrable double-integral construction for the full-plane potential.
This is the analytic starting point for the alternate potential-kernel route
in Appendix B. Identification with the actual quadrant image kernel and the
diagonal odd-harmonic evaluation are separate, not asserted here. -/
namespace SpanningTreeIsoperimetry.PotentialKernelIntegral
open Set MeasureTheory
open scoped ENNReal Topology
noncomputable section

/-- The square-lattice Fourier denominator for the transition operator. -/
def denominator (θ φ : ℝ) : ℝ := 1-(Real.cos θ+Real.cos φ)/2

def density (m n : ℕ) (θ φ : ℝ) : ℝ :=
  (1-Real.cos ((m : ℝ)*θ)*Real.cos ((n : ℝ)*φ))/denominator θ φ

theorem one_sub_cos_half_square (t : ℝ) : 1-Real.cos t=2*Real.sin (t/2)^2 := by
  have h := Real.cos_add (t/2) (t/2)
  have hs := Real.sin_sq_add_cos_sq (t/2)
  rw [show t/2+t/2=t by ring] at h
  nlinarith only [h,hs]

/-- The existing integer-frequency sine bound controls the removable
singularity of the two-dimensional potential integrand. -/
theorem one_sub_cos_nat_mul_le (m : ℕ) (θ : ℝ) :
    1-Real.cos ((m : ℝ)*θ)≤(m : ℝ)^2*(1-Real.cos θ) := by
  have h := mul_self_le_mul_self (abs_nonneg _)
    (BoundaryKernelBounds.abs_sin_nat_mul_le m (θ/2))
  rw [one_sub_cos_half_square,one_sub_cos_half_square]
  have he : ((m : ℝ)*θ)/2=(m : ℝ)*(θ/2) := by ring
  rw [he]
  simp only [← pow_two,mul_pow,sq_abs] at h
  nlinarith only [h]

theorem denominator_nonneg (θ φ : ℝ) : 0≤denominator θ φ := by
  unfold denominator
  linarith [Real.cos_le_one θ,Real.cos_le_one φ]

theorem numerator_nonneg (m n : ℕ) (θ φ : ℝ) :
    0≤1-Real.cos ((m : ℝ)*θ)*Real.cos ((n : ℝ)*φ) := by
  have h : |Real.cos ((m : ℝ)*θ)| * |Real.cos ((n : ℝ)*φ)| ≤ 1 := by
    calc
      _≤1*1 := mul_le_mul (Real.abs_cos_le_one _) (Real.abs_cos_le_one _)
        (abs_nonneg _) (by norm_num)
      _=1 := one_mul 1
  have hh := le_abs_self (Real.cos ((m : ℝ)*θ)*Real.cos ((n : ℝ)*φ))
  rw [abs_mul] at hh
  linarith

/-- Uniform global bound, valid even at zero-denominator points. -/
theorem density_bounds (m n : ℕ) (θ φ : ℝ) :
    0≤density m n θ φ ∧ density m n θ φ≤2*((m : ℝ)^2+(n : ℝ)^2) := by
  have hd := denominator_nonneg θ φ
  have hn := numerator_nonneg m n θ φ
  constructor
  · exact div_nonneg hn hd
  · by_cases hzero : denominator θ φ=0
    · simp only [density,hzero,div_zero]
      positivity
    have hpos : 0<denominator θ φ := lt_of_le_of_ne hd (Ne.symm hzero)
    apply (div_le_iff₀ hpos).mpr
    have hx := one_sub_cos_nat_mul_le m θ
    have hy := one_sub_cos_nat_mul_le n φ
    have hprod := mul_nonneg (sub_nonneg.mpr (Real.cos_le_one ((m : ℝ)*θ)))
      (sub_nonneg.mpr (Real.cos_le_one ((n : ℝ)*φ)))
    have hcross1 := mul_nonneg (sq_nonneg (m : ℝ)) (sub_nonneg.mpr (Real.cos_le_one φ))
    have hcross2 := mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.mpr (Real.cos_le_one θ))
    unfold denominator
    nlinarith only [hx,hy,hprod,hcross1,hcross2]

def frequencySquare : Set (ℝ × ℝ) := Icc (0 : ℝ) Real.pi ×ˢ Icc (0 : ℝ) Real.pi

theorem density_measurable (m n : ℕ) :
    Measurable (fun p : ℝ × ℝ => density m n p.1 p.2) := by
  unfold density denominator
  fun_prop

theorem density_integrable (m n : ℕ) :
    IntegrableOn (fun p : ℝ × ℝ => density m n p.1 p.2) frequencySquare := by
  apply IntegrableOn.of_bound
    (show volume frequencySquare<∞ from (isCompact_Icc.prod isCompact_Icc).measure_lt_top)
    ((density_measurable m n).aestronglyMeasurable.restrict) (2*((m : ℝ)^2+(n : ℝ)^2))
  apply Filter.Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs,abs_of_nonneg (density_bounds m n p.1 p.2).1]
  exact (density_bounds m n p.1 p.2).2

/-- The usual square-lattice potential, normalized by the transition Fourier
operator. Its identification and normalization a(1,0)=1 are later steps. -/
def potential (m n : ℕ) : ℝ :=
  (1/Real.pi^2)*∫ p in frequencySquare,density m n p.1 p.2

theorem potential_zero : potential 0 0=0 := by
  simp [potential,density]

theorem potential_nonneg (m n : ℕ) : 0≤potential m n := by
  unfold potential
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro p
  exact (density_bounds m n p.1 p.2).1

theorem density_swap (m n : ℕ) (θ φ : ℝ) : density m n θ φ=density n m φ θ := by
  unfold density denominator
  congr 1 <;> ring

theorem potential_swap (m n : ℕ) : potential m n=potential n m := by
  unfold potential
  congr 1
  have h := setIntegral_prod_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (Icc (0 : ℝ) Real.pi) (Icc (0 : ℝ) Real.pi)
    (fun p : ℝ × ℝ => density n m p.1 p.2)
  simpa only [frequencySquare,Prod.fst_swap,Prod.snd_swap,← density_swap m n,Measure.volume_eq_prod] using h

end
end SpanningTreeIsoperimetry.PotentialKernelIntegral
