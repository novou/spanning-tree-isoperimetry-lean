import SpanningTreeIsoperimetry.StripFourierMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Data.Fin.VecNotation

/-! Exact evaluation of the first five actual cosine coefficients. -/
namespace SpanningTreeIsoperimetry.StripFourierFive
open StripFourierCoefficients StripFourierMoments RectangularRemainder
open Polynomial Set MeasureTheory
open scoped BigOperators
noncomputable section

def weights : Fin 5 → Fin 5 → ℝ :=
  ![![4,0,0,0,0], ![-8,16,0,0,0], ![12,-64,64,0,0],
    ![-16,160,-384,256,0], ![20,-320,1344,-2048,1024]]

def sinePolynomial (j : Fin 5) (x : ℝ) : ℝ :=
  ![1,4*x^2-2,16*x^4-16*x^2+3,
    64*x^6-96*x^4+40*x^2-4,
    256*x^8-512*x^6+336*x^4-80*x^2+5] j

def antiderivative (j : Fin 5) (x : ℝ) : ℝ :=
  ∑ m : Fin 5, weights j m*primitive (m.val+1) x

theorem hasDerivAt_antiderivative (j : Fin 5) {x : ℝ} (hx : x∈Icc (-1) 1) :
    HasDerivAt (antiderivative j) (4*x^2*sinePolynomial j x/root x) x := by
  have hd := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 5)))
    (fun m _ => (hasDerivAt_primitive (m.val+1) hx).const_mul (weights j m))
  change HasDerivAt (antiderivative j) _ x at hd
  convert hd using 1
  fin_cases j <;> norm_num [weights,sinePolynomial,Fin.sum_univ_succ] <;> ring

theorem sine_multiple (j : Fin 5) (θ : ℝ) :
    Real.sin (((j.val : ℝ)+1)*θ)=
      2*Real.sin (θ/2)*Real.cos (θ/2)*sinePolynomial j (Real.cos (θ/2)) := by
  have hu3 : Polynomial.Chebyshev.U ℝ 3=8*X^3-4*X := by
    calc
      _=2*X*Polynomial.Chebyshev.U ℝ 2-Polynomial.Chebyshev.U ℝ 1 := by
        simpa using Polynomial.Chebyshev.U_add_two ℝ 1
      _=_ := by rw [Polynomial.Chebyshev.U_two,Polynomial.Chebyshev.U_one]; ring
  have hu4 : Polynomial.Chebyshev.U ℝ 4=16*X^4-12*X^2+1 := by
    calc
      _=2*X*Polynomial.Chebyshev.U ℝ 3-Polynomial.Chebyshev.U ℝ 2 := by
        simpa using Polynomial.Chebyshev.U_add_two ℝ 2
      _=_ := by rw [hu3,Polynomial.Chebyshev.U_two]; ring
  have h := Polynomial.Chebyshev.U_real_cos θ (j.val : ℤ)
  have hc : Real.cos θ=2*Real.cos (θ/2)^2-1 := by
    have hh := Real.cos_two_mul (θ/2)
    have hs := Real.sin_sq_add_cos_sq (θ/2)
    rw [show 2*(θ/2)=θ by ring] at hh
    nlinarith
  have hs : Real.sin θ=2*Real.sin (θ/2)*Real.cos (θ/2) := by
    simpa only [show 2*(θ/2)=θ by ring] using Real.sin_two_mul (θ/2)
  rw [hc,hs] at h
  fin_cases j <;> norm_num [Polynomial.Chebyshev.U_zero,Polynomial.Chebyshev.U_one,Polynomial.Chebyshev.U_two,hu3,hu4,sinePolynomial] at h ⊢ <;>
    convert h.symm using 1 <;> ring

theorem hasDerivAt_angular_antiderivative (j : Fin 5) {θ : ℝ} (hθ : θ∈Icc 0 Real.pi) :
    HasDerivAt (fun x => antiderivative j (Real.cos (x/2)))
      (-(gammaDeriv θ*Real.sin (((j.val : ℝ)+1)*θ))) θ := by
  have hx : Real.cos (θ/2)∈Icc (-1) 1 := ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  have hd := (hasDerivAt_antiderivative j hx).comp θ (((hasDerivAt_id θ).div_const 2).cos)
  have hroot : root (Real.cos (θ/2))=Real.sqrt (1+Real.sin (θ/2)^2) := by
    unfold root
    congr 1
    nlinarith [Real.sin_sq_add_cos_sq (θ/2)]
  convert hd using 1
  · funext x
    rfl
  · rw [sine_multiple,gammaDeriv,hroot]
    dsimp
    ring

theorem antiderivative_zero (j : Fin 5) : antiderivative j 0=0 := by
  simp [antiderivative,primitive_zero]

theorem coefficient_eq_antiderivative (j : Fin 5) :
    coefficient (j.val+1)=antiderivative j 1/(Real.pi*((j.val : ℝ)+1)) := by
  have hc : Continuous (fun θ : ℝ => -(gammaDeriv θ*Real.sin (((j.val : ℝ)+1)*θ))) :=
    (continuous_gammaDeriv.mul (by fun_prop)).neg
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := Real.pi)
    (fun θ hθ => hasDerivAt_angular_antiderivative j (by simpa only [uIcc_of_le Real.pi_pos.le] using hθ))
    (hc.intervalIntegrable _ _)
  simp only [intervalIntegral.integral_neg,Real.cos_pi_div_two,zero_div,Real.cos_zero,
    antiderivative_zero,zero_sub,neg_inj] at ht
  rw [coefficient_by_parts (by omega : 0<j.val+1)]
  simp only [Nat.cast_add,Nat.cast_one]
  rw [ht]
  ring

def coefficientValues : Fin 5 → ℝ :=
  ![1-2/Real.pi,2-6/Real.pi,19/3-178/(9*Real.pi),
    24-226/(3*Real.pi),501/5-23606/(75*Real.pi)]

/-- The five displayed coefficients are evaluations of the actual cosine
integral, not independent assigned constants. -/
theorem first_five (j : Fin 5) : coefficient (j.val+1)=coefficientValues j := by
  rw [coefficient_eq_antiderivative]
  fin_cases j <;> norm_num [antiderivative,weights,Fin.sum_univ_succ,coefficientValues,
    primitive_one_one,primitive_one_two,primitive_one_three,primitive_one_four,primitive_one_five]
  all_goals field_simp <;> ring

end
end SpanningTreeIsoperimetry.StripFourierFive
