import SpanningTreeIsoperimetry.RectangularRemainder
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! A local polynomial recurrence for the angular lattice-kernel derivatives.
Every derivative is obtained from actual differentiation of the smooth kernel. -/
namespace SpanningTreeIsoperimetry.LatticeKernelDerivatives

open Polynomial RectangularRemainder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def halfSin (θ : ℝ) : ℝ := Real.sin (θ/2)
def halfCos (θ : ℝ) : ℝ := Real.cos (θ/2)
def kernelRoot (θ : ℝ) : ℝ := Real.sqrt (1+halfSin θ^2)

def oddForm (P : ℝ[X]) (n : ℕ) (θ : ℝ) : ℝ :=
  halfCos θ*P.eval (halfSin θ^2)/kernelRoot θ^(n+1)

def evenForm (P : ℝ[X]) (n : ℕ) (θ : ℝ) : ℝ :=
  halfSin θ*P.eval (halfSin θ^2)/kernelRoot θ^(n+1)

def oddTransform (P : ℝ[X]) (n : ℕ) : ℝ[X] :=
  C (1/2)*(C 2*(1-X^2)*P.derivative-(C ((n : ℝ)+2)-C (n : ℝ)*X)*P)

def evenTransform (P : ℝ[X]) (n : ℕ) : ℝ[X] :=
  C (1/2)*((1-C (n : ℝ)*X)*P+C 2*X*(1+X)*P.derivative)

theorem kernelRoot_pos (θ : ℝ) : 0<kernelRoot θ := by unfold kernelRoot; positivity

theorem kernelRoot_sq (θ : ℝ) : kernelRoot θ^2=1+halfSin θ^2 := Real.sq_sqrt (by positivity)

theorem halfCos_sq (θ : ℝ) : halfCos θ^2=1-halfSin θ^2 := by
  have h := Real.sin_sq_add_cos_sq (θ/2)
  change halfSin θ^2+halfCos θ^2=1 at h
  linarith

theorem hasDerivAt_halfSin (θ : ℝ) : HasDerivAt halfSin (halfCos θ/2) θ := by
  unfold halfSin halfCos
  convert ((hasDerivAt_id θ).div_const 2).sin using 1 <;> simp only [id_eq,div_eq_mul_inv,one_mul,mul_one]

theorem hasDerivAt_halfCos (θ : ℝ) : HasDerivAt halfCos (-halfSin θ/2) θ := by
  unfold halfSin halfCos
  convert ((hasDerivAt_id θ).div_const 2).cos using 1 <;> simp only [id_eq,div_eq_mul_inv,one_mul,mul_one]

theorem hasDerivAt_kernelRoot (θ : ℝ) :
    HasDerivAt kernelRoot (halfSin θ*halfCos θ/(2*kernelRoot θ)) θ := by
  have h := ((hasDerivAt_halfSin θ).fun_pow 2).const_add 1 |>.sqrt (by positivity : 1+halfSin θ^2≠0)
  unfold kernelRoot
  convert h using 1 <;> dsimp <;> ring

theorem hasDerivAt_poly_halfSin_sq (P : ℝ[X]) (θ : ℝ) :
    HasDerivAt (fun x => P.eval (halfSin x^2))
      (P.derivative.eval (halfSin θ^2)*halfSin θ*halfCos θ) θ := by
  have h := (P.hasDerivAt (halfSin θ^2)).comp θ ((hasDerivAt_halfSin θ).fun_pow 2)
  convert h using 1 <;> dsimp [Function.comp_def] <;> ring

private theorem odd_derivative_algebra (s c d p q : ℝ) (n : ℕ) (hd : d≠0)
    (hd2 : d^2=1+s^2) (hc2 : c^2=1-s^2) :
    (((-s/2)*p+c*(q*s*c))*d^(n+1)-(c*p)*(((n : ℝ)+1)*d^n*(s*c/(2*d))))/(d^(n+1))^2=
      s*((2*(1-(s^2)^2)*q-(((n : ℝ)+2)-n*s^2)*p)/2)/d^(n+3) := by
  calc
    _=s/(2*d^(n+3))*(-p*d^2+2*c^2*q*d^2-((n : ℝ)+1)*c^2*p) := by
      simp only [pow_add,pow_succ,mul_pow]
      field_simp [hd,pow_ne_zero n hd] <;> ring
    _=_ := by rw [hd2,hc2]; ring

private theorem even_derivative_algebra (s c d p q : ℝ) (n : ℕ) (hd : d≠0)
    (hd2 : d^2=1+s^2) :
    (((c/2)*p+s*(q*s*c))*d^(n+1)-(s*p)*(((n : ℝ)+1)*d^n*(s*c/(2*d))))/(d^(n+1))^2=
      c*(((1-n*s^2)*p+2*s^2*(1+s^2)*q)/2)/d^(n+3) := by
  calc
    _=c/(2*d^(n+3))*(p*d^2+2*s^2*q*d^2-((n : ℝ)+1)*s^2*p) := by
      simp only [pow_add,pow_succ,mul_pow]
      field_simp [hd,pow_ne_zero n hd] <;> ring
    _=_ := by rw [hd2]; ring

theorem hasDerivAt_oddForm (P : ℝ[X]) (n : ℕ) (θ : ℝ) :
    HasDerivAt (oddForm P n) (evenForm (oddTransform P n) (n+2) θ) θ := by
  have hn := (hasDerivAt_halfCos θ).fun_mul (hasDerivAt_poly_halfSin_sq P θ)
  have hd := (hasDerivAt_kernelRoot θ).fun_pow (n+1)
  have h := hn.fun_div hd (pow_ne_zero _ (kernelRoot_pos θ).ne')
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at h
  have he := odd_derivative_algebra (halfSin θ) (halfCos θ) (kernelRoot θ)
    (P.eval (halfSin θ^2)) (P.derivative.eval (halfSin θ^2)) n
    (kernelRoot_pos θ).ne' (kernelRoot_sq θ) (halfCos_sq θ)
  rw [he] at h
  have hv : evenForm (oddTransform P n) (n+2) θ=
      halfSin θ*((2*(1-(halfSin θ^2)^2)*P.derivative.eval (halfSin θ^2)-
        (((n : ℝ)+2)-n*halfSin θ^2)*P.eval (halfSin θ^2))/2)/kernelRoot θ^(n+3) := by
    simp only [evenForm,oddTransform,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_add,
      Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_one,Polynomial.eval_X]
    ring
  rw [← hv] at h
  exact h

theorem hasDerivAt_evenForm (P : ℝ[X]) (n : ℕ) (θ : ℝ) :
    HasDerivAt (evenForm P n) (oddForm (evenTransform P n) (n+2) θ) θ := by
  have hn := (hasDerivAt_halfSin θ).fun_mul (hasDerivAt_poly_halfSin_sq P θ)
  have hd := (hasDerivAt_kernelRoot θ).fun_pow (n+1)
  have h := hn.fun_div hd (pow_ne_zero _ (kernelRoot_pos θ).ne')
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at h
  have he := even_derivative_algebra (halfSin θ) (halfCos θ) (kernelRoot θ)
    (P.eval (halfSin θ^2)) (P.derivative.eval (halfSin θ^2)) n
    (kernelRoot_pos θ).ne' (kernelRoot_sq θ)
  rw [he] at h
  have hv : oddForm (evenTransform P n) (n+2) θ=
      halfCos θ*(((1-n*halfSin θ^2)*P.eval (halfSin θ^2)+
        2*halfSin θ^2*(1+halfSin θ^2)*P.derivative.eval (halfSin θ^2))/2)/kernelRoot θ^(n+3) := by
    simp only [oddForm,evenTransform,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_add,
      Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_one,Polynomial.eval_X]
    ring
  rw [← hv] at h
  exact h
theorem continuous_oddForm (P : ℝ[X]) (n : ℕ) : Continuous (oddForm P n) := by
  unfold oddForm
  apply Continuous.div
  · unfold halfSin halfCos
    fun_prop
  · unfold kernelRoot halfSin
    fun_prop
  · intro θ
    exact pow_ne_zero _ (kernelRoot_pos θ).ne'

theorem continuous_evenForm (P : ℝ[X]) (n : ℕ) : Continuous (evenForm P n) := by
  unfold evenForm
  apply Continuous.div
  · unfold halfSin
    fun_prop
  · unfold kernelRoot halfSin
    fun_prop
  · intro θ
    exact pow_ne_zero _ (kernelRoot_pos θ).ne'

def P2 : ℝ[X] := -1
def P3 : ℝ[X] := X-C (1/2)
def P4 : ℝ[X] := C (5/2)-C 4*X+X^2
def P5 : ℝ[X] := C (5/4)-C (27/2)*X+C (21/2)*X^2-X^3
def P6 : ℝ[X] := -C (79/4)+C (187/2)*X-C 96*X^2+C 26*X^3-X^4

def gammaD2 : ℝ → ℝ := evenForm P2 2
def gammaD3 : ℝ → ℝ := oddForm P3 4
def gammaD4 : ℝ → ℝ := evenForm P4 6
def gammaD5 : ℝ → ℝ := oddForm P5 8
def gammaD6 : ℝ → ℝ := evenForm P6 10

private theorem polynomial_ladder :
    oddTransform 1 0=P2 ∧ evenTransform P2 2=P3 ∧ oddTransform P3 4=P4 ∧
      evenTransform P4 6=P5 ∧ oddTransform P5 8=P6 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals
    apply Polynomial.funext
    intro x
    norm_num [oddTransform,evenTransform,P2,P3,P4,P5,P6,
      Polynomial.derivative_add,Polynomial.derivative_sub,Polynomial.derivative_mul,
      Polynomial.derivative_pow] <;> ring

theorem hasDerivAt_gammaDeriv (θ : ℝ) : HasDerivAt gammaDeriv (gammaD2 θ) θ := by
  have h := hasDerivAt_oddForm 1 0 θ
  rw [polynomial_ladder.1] at h
  have he : oddForm 1 0=gammaDeriv := by
    funext x
    simp [oddForm,gammaDeriv,kernelRoot,halfSin,halfCos]
  rw [he] at h
  exact h

theorem hasDerivAt_gammaD2 (θ : ℝ) : HasDerivAt gammaD2 (gammaD3 θ) θ := by
  have h := hasDerivAt_evenForm P2 2 θ
  rw [polynomial_ladder.2.1] at h
  exact h

theorem hasDerivAt_gammaD3 (θ : ℝ) : HasDerivAt gammaD3 (gammaD4 θ) θ := by
  have h := hasDerivAt_oddForm P3 4 θ
  rw [polynomial_ladder.2.2.1] at h
  exact h

theorem hasDerivAt_gammaD4 (θ : ℝ) : HasDerivAt gammaD4 (gammaD5 θ) θ := by
  have h := hasDerivAt_evenForm P4 6 θ
  rw [polynomial_ladder.2.2.2.1] at h
  exact h

theorem hasDerivAt_gammaD5 (θ : ℝ) : HasDerivAt gammaD5 (gammaD6 θ) θ := by
  have h := hasDerivAt_oddForm P5 8 θ
  rw [polynomial_ladder.2.2.2.2] at h
  exact h

theorem iteratedDeriv_gamma_one : iteratedDeriv 1 gamma=gammaDeriv := by
  rw [iteratedDeriv_succ,iteratedDeriv_zero]
  funext θ
  exact (hasDerivAt_gamma θ).deriv

theorem iteratedDeriv_gamma_two : iteratedDeriv 2 gamma=gammaD2 := by
  rw [iteratedDeriv_succ,iteratedDeriv_gamma_one]
  funext θ
  exact (hasDerivAt_gammaDeriv θ).deriv

theorem iteratedDeriv_gamma_three : iteratedDeriv 3 gamma=gammaD3 := by
  rw [iteratedDeriv_succ,iteratedDeriv_gamma_two]
  funext θ
  exact (hasDerivAt_gammaD2 θ).deriv

theorem iteratedDeriv_gamma_four : iteratedDeriv 4 gamma=gammaD4 := by
  rw [iteratedDeriv_succ,iteratedDeriv_gamma_three]
  funext θ
  exact (hasDerivAt_gammaD3 θ).deriv

theorem iteratedDeriv_gamma_five : iteratedDeriv 5 gamma=gammaD5 := by
  rw [iteratedDeriv_succ,iteratedDeriv_gamma_four]
  funext θ
  exact (hasDerivAt_gammaD4 θ).deriv

theorem iteratedDeriv_gamma_six : iteratedDeriv 6 gamma=gammaD6 := by
  rw [iteratedDeriv_succ,iteratedDeriv_gamma_five]
  funext θ
  exact (hasDerivAt_gammaD5 θ).deriv

@[simp] theorem gammaD2_zero : gammaD2 0=0 := by simp [gammaD2,evenForm,halfSin]
@[simp] theorem gammaD3_zero : gammaD3 0= -(1/2) := by
  norm_num [gammaD3,oddForm,P3,halfSin,halfCos,kernelRoot]
@[simp] theorem gammaD4_zero : gammaD4 0=0 := by simp [gammaD4,evenForm,halfSin]
@[simp] theorem gammaD5_zero : gammaD5 0=5/4 := by
  norm_num [gammaD5,oddForm,P5,halfSin,halfCos,kernelRoot]
@[simp] theorem gammaD3_pi : gammaD3 Real.pi=0 := by simp [gammaD3,oddForm,halfCos]
@[simp] theorem gammaD5_pi : gammaD5 Real.pi=0 := by simp [gammaD5,oddForm,halfCos]

theorem halfSin_mem {θ : ℝ} (hθ : θ∈Set.Icc 0 Real.pi) : halfSin θ∈Set.Icc 0 1 :=
  ⟨Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2,Real.pi_pos]),
    Real.sin_le_one _⟩

theorem halfCos_nonneg {θ : ℝ} (hθ : θ∈Set.Icc 0 Real.pi) : 0≤halfCos θ :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1,Real.pi_pos],by linarith [hθ.2]⟩

theorem kernelRoot_ge_one (θ : ℝ) : 1≤kernelRoot θ := by
  nlinarith [kernelRoot_pos θ,kernelRoot_sq θ,sq_nonneg (halfSin θ)]

/-- Uniform third-derivative bound, including both endpoints. -/
theorem gammaD3_abs_le {θ : ℝ} (hθ : θ∈Set.Icc 0 Real.pi) : |gammaD3 θ|≤1/2 := by
  have hs := halfSin_mem hθ
  have hz : 0≤halfSin θ^2 ∧ halfSin θ^2≤1 := ⟨sq_nonneg _,by nlinarith [hs.1,hs.2]⟩
  have hc0 := halfCos_nonneg hθ
  have hc1 : halfCos θ≤1 := Real.cos_le_one _
  have hp : |P3.eval (halfSin θ^2)|≤1/2 := by
    simp only [P3,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
    rw [abs_le]
    constructor <;> linarith [hz.1,hz.2]
  have hd := kernelRoot_pos θ
  have hd5 : 1≤kernelRoot θ^5 := one_le_pow₀ (kernelRoot_ge_one θ)
  change |halfCos θ*P3.eval (halfSin θ^2)/kernelRoot θ^5|≤1/2
  rw [abs_div,abs_mul,abs_of_nonneg hc0,abs_of_pos (pow_pos hd 5)]
  apply (div_le_iff₀ (pow_pos hd 5)).mpr
  have hm := mul_le_mul hc1 hp (abs_nonneg _) (by norm_num : (0 : ℝ)≤1)
  nlinarith

private theorem P5_bound {z : ℝ} (hz : z∈Set.Icc 0 1) :
    |P5.eval z|≤(5/4)*(1+z)^4 := by
  have hz2 : z^2≤z := by nlinarith [hz.1,hz.2]
  have hz3 : 0≤z^3 := pow_nonneg hz.1 _
  have hz4 : 0≤z^4 := pow_nonneg hz.1 _
  have hpower : 1≤(1+z)^4 := one_le_pow₀ (by linarith [hz.1])
  have hupper : P5.eval z≤5/4 := by
    simp only [P5,Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow]
    nlinarith
  have he : 4*((5/4)*(1+z)^4+P5.eval z)=
      72*(z-17/72)^2+431/72+16*z^3+5*z^4 := by
    simp only [P5,Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_pow]
    ring
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (z-17/72)]

/-- Uniform fifth-derivative bound obtained from the explicit numerator
polynomial; it is not supplied as a Taylor-remainder premise. -/
theorem gammaD5_abs_le {θ : ℝ} (hθ : θ∈Set.Icc 0 Real.pi) : |gammaD5 θ|≤5/4 := by
  have hs := halfSin_mem hθ
  have hz : halfSin θ^2∈Set.Icc 0 1 := ⟨sq_nonneg _,by nlinarith [hs.1,hs.2]⟩
  have hc0 := halfCos_nonneg hθ
  have hd := kernelRoot_pos θ
  have hcd : halfCos θ≤kernelRoot θ := by
    nlinarith [halfCos_sq θ,kernelRoot_sq θ,sq_nonneg (halfSin θ)]
  have hp := P5_bound hz
  have hd8 : kernelRoot θ^8=(1+halfSin θ^2)^4 := by
    calc
      kernelRoot θ^8=(kernelRoot θ^2)^4 := by ring
      _=(1+halfSin θ^2)^4 := by rw [kernelRoot_sq]
  rw [← hd8] at hp
  change |halfCos θ*P5.eval (halfSin θ^2)/kernelRoot θ^9|≤5/4
  rw [abs_div,abs_mul,abs_of_nonneg hc0,abs_of_pos (pow_pos hd 9)]
  apply (div_le_iff₀ (pow_pos hd 9)).mpr
  calc
    halfCos θ*|P5.eval (halfSin θ^2)|≤halfCos θ*((5/4)*kernelRoot θ^8) :=
      mul_le_mul_of_nonneg_left hp hc0
    _≤kernelRoot θ*((5/4)*kernelRoot θ^8) := mul_le_mul_of_nonneg_right hcd (by positivity)
    _=(5/4)*kernelRoot θ^9 := by ring

end
end SpanningTreeIsoperimetry.LatticeKernelDerivatives
