module

public import SpanningTreeIsoperimetry.EvenPeriodicFourier

@[expose] public section

/-! Endpoint reconstruction and the even-mode sum for actual cosine
coefficients of a continuous even periodic function. -/
namespace SpanningTreeIsoperimetry.EvenFourierReconstruction
open EvenPeriodicFourier AddCircle
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance : Fact (0<(2*Real.pi : ℝ)) := ⟨by positivity⟩

theorem summable_natAbs {a : ℕ → ℝ} (ha : Summable a) :
    Summable (fun n : ℤ => a n.natAbs) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor <;> simpa using ha

theorem tsum_natAbs {a : ℕ → ℝ} (ha : Summable a) :
    (∑' n : ℤ,a n.natAbs)=2*(∑' n : ℕ,a n)-a 0 := by
  have hh := tsum_nat_add_neg (summable_natAbs ha)
  simp only [Int.natAbs_natCast,Int.natAbs_neg,Int.natAbs_zero] at hh
  rw [ha.tsum_add ha] at hh
  linarith only [hh]

theorem sum_add_alternating {a : ℕ → ℝ} (ha : Summable a) :
    (∑' n : ℕ,a n)+(∑' n : ℕ,(-1 : ℝ)^n*a n)=2*(∑' n : ℕ,a (2*n)) := by
  have he : Summable (fun n : ℕ => a (2*n)) := ha.comp_injective (fun m n h => by omega)
  have ho : Summable (fun n : ℕ => a (2*n+1)) := ha.comp_injective (fun m n h => by omega)
  have hsum := tsum_even_add_odd he ho
  have halt := tsum_even_add_odd (f := fun n : ℕ => (-1 : ℝ)^n*a n)
    (by simpa [pow_mul] using he) (by simpa [pow_add,pow_mul] using ho.neg)
  simp only [pow_add,pow_mul,neg_one_sq,one_pow,pow_one,one_mul,neg_one_mul,tsum_neg] at halt
  linarith only [hsum,halt]

theorem fourier_summable (f : ℝ → ℝ) (hc : Continuous f)
    (hp : Function.Periodic f (2*Real.pi)) (he : Function.Even f)
    (hs : Summable (cosineCoeff f)) : Summable (fourierCoeff (circleMap f hc hp)) := by
  change Summable (fun n : ℤ => fourierCoeff (circleMap f hc hp) n)
  simp_rw [fourier_coefficient f hc hp he]
  exact Complex.summable_ofReal.mpr (summable_natAbs hs)

theorem endpoint_reconstruction (f : ℝ → ℝ) (hc : Continuous f)
    (hp : Function.Periodic f (2*Real.pi)) (he : Function.Even f)
    (hs : Summable (cosineCoeff f)) :
    f 0=2*(∑' n : ℕ,cosineCoeff f n)-cosineCoeff f 0 ∧
      f Real.pi=2*(∑' n : ℕ,(-1 : ℝ)^n*cosineCoeff f n)-cosineCoeff f 0 := by
  have hsF := fourier_summable f hc hp he hs
  have hzero := has_pointwise_sum_fourier_series_of_summable hsF (0 : AddCircle (2*Real.pi))
  have hpi := has_pointwise_sum_fourier_series_of_summable hsF (Real.pi : AddCircle (2*Real.pi))
  have hzeroR : HasSum (fun n : ℤ => cosineCoeff f n.natAbs) (f 0) := by
    convert Complex.hasSum_re hzero using 1
    · funext n
      simp only [fourier_eval_zero,smul_eq_mul,mul_one,fourier_coefficient f hc hp he,Complex.ofReal_re]
    · have hv : circleMap f hc hp (0 : AddCircle (2*Real.pi))=(f 0 : ℂ) := by
        simpa using circleMap_coe f hc hp (0 : ℝ)
      rw [hv,Complex.ofReal_re]
  have hpiR : HasSum (fun n : ℤ => (-1 : ℝ)^n.natAbs*cosineCoeff f n.natAbs) (f Real.pi) := by
    convert Complex.hasSum_re hpi using 1
    · funext n
      simp only [smul_eq_mul,fourier_coefficient f hc hp he,fourier_pi,
        Complex.mul_re,← Complex.ofReal_pow,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      ring
    · simp only [circleMap_coe,Complex.ofReal_re]
  have h0 := hzeroR.tsum_eq
  have hπ := hpiR.tsum_eq
  have hz := tsum_natAbs hs
  have ha := tsum_natAbs hs.alternating
  simp only [pow_zero,one_mul] at ha
  constructor <;> linarith only [h0,hπ,hz,ha]

theorem even_sum (f : ℝ → ℝ) (hc : Continuous f)
    (hp : Function.Periodic f (2*Real.pi)) (he : Function.Even f)
    (hs : Summable (cosineCoeff f)) :
    (∑' n : ℕ,cosineCoeff f (2*(n+1)))=(f 0+f Real.pi-2*cosineCoeff f 0)/4 := by
  obtain ⟨h0,hπ⟩ := endpoint_reconstruction f hc hp he hs
  have ha := sum_add_alternating hs
  have he : Summable (fun n : ℕ => cosineCoeff f (2*n)) :=
    hs.comp_injective (fun m n h => by omega)
  have hshift := he.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one,mul_zero] at hshift
  linarith only [h0,hπ,ha,hshift]

end
end SpanningTreeIsoperimetry.EvenFourierReconstruction
