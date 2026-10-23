module

public import SpanningTreeIsoperimetry.RectangularQuadrature
public import SpanningTreeIsoperimetry.KernelDerivativeVariation

@[expose] public section

/-! The actual rectangular epsilon has explicit third- and fifth-order
remainders, obtained from local quadrature and the proved kernel derivatives. -/
namespace SpanningTreeIsoperimetry.TrapezoidalKernelError

open Set MeasureTheory SquareMaximality SquareMaximality.Rectangle
open Concrete Trapezoid Entropy RectangularRemainder RectangularQuadrature
open LatticeKernelDerivatives KernelDerivativeVariation
open scoped BigOperators Interval
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def gammaLadder : ℕ → ℝ → ℝ
  | 0 => gamma
  | 1 => gammaDeriv
  | 2 => gammaD2
  | 3 => gammaD3
  | 4 => gammaD4
  | 5 => gammaD5
  | 6 => gammaD6
  | _ => 0

theorem gammaLadder_continuous {n : ℕ} (hn : n≤6) : Continuous (gammaLadder n) := by
  interval_cases n
  · exact contDiff_gamma.continuous
  · exact continuous_gammaDeriv
  · exact continuous_evenForm P2 2
  · exact continuous_oddForm P3 4
  · exact continuous_evenForm P4 6
  · exact continuous_oddForm P5 8
  · exact continuous_evenForm P6 10

theorem gammaLadder_derivative {n : ℕ} (hn : n<6) (θ : ℝ) :
    HasDerivAt (gammaLadder n) (gammaLadder (n+1) θ) θ := by
  interval_cases n
  · exact hasDerivAt_gamma θ
  · exact hasDerivAt_gammaDeriv θ
  · exact hasDerivAt_gammaD2 θ
  · exact hasDerivAt_gammaD3 θ
  · exact hasDerivAt_gammaD4 θ
  · exact hasDerivAt_gammaD5 θ

@[simp] theorem gammaDeriv_zero : gammaDeriv 0=1 := by norm_num [gammaDeriv]
@[simp] theorem gammaDeriv_pi : gammaDeriv Real.pi=0 := by simp [gammaDeriv]

theorem integral_gamma : (∫ θ in (0 : ℝ)..Real.pi, gamma θ)=Real.pi*squareLatticeEntropy := by
  calc
    (∫ θ in (0 : ℝ)..Real.pi, gamma θ)=∫ θ in (0 : ℝ)..Real.pi, kernel (θ/Real.pi) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      exact gamma_eq_kernel (by simpa only [uIcc_of_le Real.pi_pos.le] using hθ)
    _=Real.pi*(∫ x in (0 : ℝ)..1, kernel x) := by
      rw [intervalIntegral.integral_comp_div kernel Real.pi_ne_zero]
      simp only [zero_div,div_self Real.pi_ne_zero,smul_eq_mul]
    _=Real.pi*squareLatticeEntropy := by
      rw [← kernelIntegral,Entropy.kernelIntegral_eq_squareLatticeEntropy]

theorem gamma_trapezoidal_error {r : ℕ} (hr : 0<r) :
    trapezoidal_error gamma r 0 Real.pi= -(Real.pi/r)*epsilon squareLatticeEntropy r := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hsum : (∑ k∈Finset.range (r-1), gamma (((k : ℝ)+1)*Real.pi/r))=C r := by
    rw [C,Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k+1≤r := by have hh := Finset.mem_range.mp hk; omega
    have hkR : (k : ℝ)+1≤r := by exact_mod_cast hk'
    have hθ : ((k : ℝ)+1)*Real.pi/r∈Set.Icc 0 Real.pi := by
      constructor
      · positivity
      · apply (div_le_iff₀ hrR).mpr
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hkR Real.pi_pos.le
    rw [gamma_eq_kernel hθ]
    simp only [Nat.cast_add,Nat.cast_one]
    congr 1
    field_simp [hrR.ne',Real.pi_ne_zero]
    ring
  rw [trapezoidal_error,trapezoidal_integral,integral_gamma,gamma_zero,gamma_pi]
  simp only [sub_zero,zero_add]
  rw [hsum]
  unfold epsilon
  field_simp [hrR.ne',Real.pi_ne_zero]
  ring

/-- Uniform bound on the first lattice correction, with the actual epsilon. -/
theorem epsilon_first_error {r : ℕ} (hr : 0<r) :
    |epsilon squareLatticeEntropy r-Real.pi/(12*r)|≤Real.pi^3/(360*(r : ℝ)^3) := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  let h : ℝ := Real.pi/r
  have hh : 0<h := div_pos Real.pi_pos hrR
  have he : 0+(r : ℝ)*h=Real.pi := by dsimp [h]; field_simp [hrR.ne',Real.pi_ne_zero]; simp
  have hform := composite_four 0 h hh.ne' hr gammaLadder
    (fun n hn => gammaLadder_continuous (n := n) (by omega)) (fun n hn => gammaLadder_derivative (n := n) (by omega))
  rw [he] at hform
  norm_num only [gammaLadder,gammaDeriv_zero,gammaDeriv_pi,gammaD3_zero,gammaD3_pi] at hform
  have hrem := compositeRemainder_bound 0 h hh r 4 gammaD4 (continuous_evenForm P4 6)
    (1/720) (fun x hx => quadraturePolynomial_four_bound hx)
  rw [he] at hrem
  have hrem' : |compositeRemainder 0 h r 4 gammaD4|≤(h^4/720)*(3/2) := by
    have hm := mul_le_mul_of_nonneg_left integral_abs_gammaD4_le (show 0≤h^4*(1/720) by positivity)
    convert hrem.trans hm using 1 <;> ring
  have hbound : |trapezoidal_error gamma r 0 Real.pi+h^2/12|≤h^4/360 := by
    calc
      _=|-(h^4/1440)-compositeRemainder 0 h r 4 gammaD4| := by congr 1; linarith
      _≤|-(h^4/1440)|+|compositeRemainder 0 h r 4 gammaD4| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (-(h^4/1440)) (0 : ℝ) (compositeRemainder 0 h r 4 gammaD4)
      _≤h^4/1440+(h^4/720)*(3/2) := by
        rw [abs_neg,abs_of_nonneg (by positivity : 0≤h^4/1440)]
        linarith
      _=h^4/360 := by ring
  rw [gamma_trapezoidal_error hr] at hbound
  have hf : -(Real.pi/r)*epsilon squareLatticeEntropy r+h^2/12=
      -h*(epsilon squareLatticeEntropy r-Real.pi/(12*r)) := by dsimp [h]; field_simp [hrR.ne',Real.pi_ne_zero] <;> ring
  rw [hf,abs_mul,abs_neg,abs_of_pos hh] at hbound
  calc
    |epsilon squareLatticeEntropy r-Real.pi/(12*r)|≤(h^4/360)/h :=
      (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hbound)
    _=Real.pi^3/(360*(r : ℝ)^3) := by dsimp [h]; field_simp [hrR.ne',Real.pi_ne_zero] <;> ring

/-- Sixth-order quadrature yields the explicit next lattice correction and
its fifth-order epsilon remainder, without assuming a Fourier error bound. -/
theorem epsilon_next_error {r : ℕ} (hr : 0<r) :
    |epsilon squareLatticeEntropy r-Real.pi/(12*r)-Real.pi^3/(1440*(r : ℝ)^3)|≤
      Real.pi^5/(6048*(r : ℝ)^5) := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  let h : ℝ := Real.pi/r
  have hh : 0<h := div_pos Real.pi_pos hrR
  have he : 0+(r : ℝ)*h=Real.pi := by dsimp [h]; field_simp [hrR.ne',Real.pi_ne_zero]; simp
  have hform := composite_six 0 h hh.ne' hr gammaLadder
    (fun n hn => gammaLadder_continuous hn) (fun n hn => gammaLadder_derivative hn)
  rw [he] at hform
  norm_num only [gammaLadder,gammaDeriv_zero,gammaDeriv_pi,gammaD3_zero,gammaD3_pi,
    gammaD5_zero,gammaD5_pi] at hform
  have hrem := compositeRemainder_bound 0 h hh r 6 gammaD6 (continuous_evenForm P6 10)
    (1/30240) (fun x hx => quadraturePolynomial_six_bound hx)
  rw [he] at hrem
  have hrem' : |compositeRemainder 0 h r 6 gammaD6|≤(h^6/30240)*(15/4) := by
    have hm := mul_le_mul_of_nonneg_left integral_abs_gammaD6_le (show 0≤h^6*(1/30240) by positivity)
    convert hrem.trans hm using 1 <;> ring
  have hbound : |trapezoidal_error gamma r 0 Real.pi+h^2/12+h^4/1440|≤h^6/6048 := by
    calc
      _=|-(h^6/30240*(5/4))-compositeRemainder 0 h r 6 gammaD6| := by congr 1; linarith
      _≤|-(h^6/30240*(5/4))|+|compositeRemainder 0 h r 6 gammaD6| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le (-(h^6/30240*(5/4))) (0 : ℝ) (compositeRemainder 0 h r 6 gammaD6)
      _≤(h^6/30240)*(5/4)+(h^6/30240)*(15/4) := by
        rw [abs_neg,abs_of_nonneg (by positivity : 0≤h^6/30240*(5/4))]
        linarith
      _=h^6/6048 := by ring
  rw [gamma_trapezoidal_error hr] at hbound
  have hf : -(Real.pi/r)*epsilon squareLatticeEntropy r+h^2/12+h^4/1440=
      -h*(epsilon squareLatticeEntropy r-Real.pi/(12*r)-Real.pi^3/(1440*(r : ℝ)^3)) := by
    dsimp [h]
    field_simp [hrR.ne',Real.pi_ne_zero]
    ring
  rw [hf,abs_mul,abs_neg,abs_of_pos hh] at hbound
  calc
    |epsilon squareLatticeEntropy r-Real.pi/(12*r)-Real.pi^3/(1440*(r : ℝ)^3)|≤(h^6/6048)/h :=
      (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hbound)
    _=Real.pi^5/(6048*(r : ℝ)^5) := by dsimp [h]; field_simp [hrR.ne',Real.pi_ne_zero] <;> ring

end
end SpanningTreeIsoperimetry.TrapezoidalKernelError
