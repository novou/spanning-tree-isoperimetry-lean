module

public import SpanningTreeIsoperimetry.ShortDefectDensities
public import SpanningTreeIsoperimetry.BoundaryShortPolynomial
public import SpanningTreeIsoperimetry.BoundaryShortMoments

@[expose] public section

set_option backward.privateInPublic true

/-! Actual fourth-order finite correction lower bounds for the two-cell
vertical strip and the 2×2 corner square. -/
namespace SpanningTreeIsoperimetry.FiniteShortDefectError
open Ferrers CornerEnergy CornerStripBridge Set MeasureTheory RectangularRemainder
  BoundaryKernelBounds BoundaryKernelMajorant BoundarySingletonIntegral
  BoundaryBoseMoments BoundaryShortWeight BoundaryShortPolynomial BoundaryShortMoments
  BoundaryLowerIntegral BoundaryProfileTransfer ShortDefectDensities ShortDefectPolynomials
open scoped Classical
noncomputable section

def stripProfile (r t : ℝ) : ℝ := (73/6)*bose 3 r t-(1127/120)*bose 5 r t
def squareProfile (r t : ℝ) : ℝ := 40*bose 3 r t+(29/5)*bose 5 r t-11*bose 7 r t

private theorem interval_three {r : ℝ} (hr : 0 < r) : IntervalIntegrable (bose 3 r) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)]
  exact (bose_three_integrable hr).mono_set (fun x hx => hx.1)

private theorem interval_five {r : ℝ} (hr : 0 < r) : IntervalIntegrable (bose 5 r) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)]
  exact (bose_five_integrable hr).mono_set (fun x hx => hx.1)

private theorem interval_seven {r : ℝ} (hr : 0 < r) : IntervalIntegrable (bose 7 r) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)]
  exact (bose_seven_integrable hr).mono_set (fun x hx => hx.1)

theorem stripProfile_integrable {r : ℝ} (hr : 0 < r) : IntervalIntegrable (stripProfile r) volume 0 1 := by
  change IntervalIntegrable (fun t : ℝ => (73/6)*bose 3 r t-(1127/120)*bose 5 r t) volume 0 1
  exact ((interval_three hr).const_mul (73/6)).sub ((interval_five hr).const_mul (1127/120))

theorem squareProfile_integrable {r : ℝ} (hr : 0 < r) : IntervalIntegrable (squareProfile r) volume 0 1 := by
  change IntervalIntegrable (fun t : ℝ => 40*bose 3 r t+(29/5)*bose 5 r t-11*bose 7 r t) volume 0 1
  exact (((interval_three hr).const_mul 40).add ((interval_five hr).const_mul (29/5))).sub
    ((interval_seven hr).const_mul 11)

theorem stripProfile_integral {r : ℝ} (hr : 0 < r) :
    (∫ t in (0 : ℝ)..1, stripProfile r t)=(73/6)*(∫ t in (0 : ℝ)..1, bose 3 r t)-
      (1127/120)*(∫ t in (0 : ℝ)..1, bose 5 r t) := by
  unfold stripProfile
  rw [intervalIntegral.integral_sub ((interval_three hr).const_mul _) ((interval_five hr).const_mul _)]
  simp only [intervalIntegral.integral_const_mul]

theorem squareProfile_integral {r : ℝ} (hr : 0 < r) :
    (∫ t in (0 : ℝ)..1, squareProfile r t)=40*(∫ t in (0 : ℝ)..1, bose 3 r t)+
      (29/5)*(∫ t in (0 : ℝ)..1, bose 5 r t)-11*(∫ t in (0 : ℝ)..1, bose 7 r t) := by
  unfold squareProfile
  rw [intervalIntegral.integral_sub (((interval_three hr).const_mul _).add ((interval_five hr).const_mul _))
    ((interval_seven hr).const_mul _),
    intervalIntegral.integral_add ((interval_three hr).const_mul _) ((interval_five hr).const_mul _)]
  simp only [intervalIntegral.integral_const_mul]

theorem weight_transfer {r θ q P : ℝ} (hr : 0 < r) (hθ : θ∈Ioo (0 : ℝ) Real.pi)
    (hq : q≤(Real.sin θ*Real.sinh (gamma θ)^2)*P) :
    q/(Real.exp (2*r*gamma θ)-1)*gammaDeriv θ≤density r 1 1 1 1 θ*P := by
  have hg := gamma_pos hθ
  have hd := gammaDeriv_nonneg ⟨hθ.1.le,hθ.2.le⟩
  have hE : 0 < Real.exp (2*r*gamma θ)-1 := by
    have h := Real.one_lt_exp_iff.mpr (show 0 < 2*r*gamma θ by positivity)
    linarith
  have h := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hq hE.le) hd
  calc
    _≤((Real.sin θ*Real.sinh (gamma θ)^2)*P)/(Real.exp (2*r*gamma θ)-1)*gammaDeriv θ := h
    _=(Real.sin θ*Real.sinh (gamma θ))*(Real.sinh (gamma θ)*gammaDeriv θ)*P/
        (Real.exp (2*r*gamma θ)-1) := by ring
    _=density r 1 1 1 1 θ*P := by rw [sinh_gamma_mul_deriv,density_singleton_eq]; ring

theorem stripProfile_pointwise (R : ℕ) {θ : ℝ} (hθ : θ∈Ioo (0 : ℝ) Real.pi) (hγ : gamma θ<1) :
    stripProfile ((R : ℝ)+1) (gamma θ)*gammaDeriv θ≤densityTrace R (verticalDiagram 2) θ := by
  have hg := gamma_pos hθ
  have hw := transformed_weight_lower ⟨hθ.1.le,hθ.2.le⟩ hγ.le
  have hx : 0≤Real.cosh (gamma θ)-1 := by linarith [Real.one_le_cosh (gamma θ)]
  have hp := strip_profile ⟨hg,hγ.le⟩ hw (two_quadratic_lower hx)
  have h := weight_transfer (by positivity : (0 : ℝ)<(R : ℝ)+1) hθ hp.le
  rw [two_density R hθ]
  convert h using 1
  unfold stripProfile bose
  ring

theorem squareProfile_pointwise (R : ℕ) {θ : ℝ} (hθ : θ∈Ioo (0 : ℝ) Real.pi) (hγ : gamma θ<1) :
    squareProfile ((R : ℝ)+1) (gamma θ)*gammaDeriv θ≤densityTrace R (faceRectangle 2 2) θ := by
  have hg := gamma_pos hθ
  have hw := transformed_weight_lower ⟨hθ.1.le,hθ.2.le⟩ hγ.le
  have hp := square_profile ⟨hg,hγ.le⟩ hw (square_quadratic_lower (Real.cosh (gamma θ)-1))
  have h := weight_transfer (by positivity : (0 : ℝ)<(R : ℝ)+1) hθ hp.le
  rw [square_density R hθ]
  convert h using 1
  unfold squareProfile bose
  ring

/-- Actual finite correction for a two-cell strip. R counts faces, so the
retained far boundary has primal coordinate R+1. -/
theorem two_cell_correction_lower {R S : ℕ} (hR : 4≤R) (hS : 2≤S) :
    21/(4*((R : ℝ)+1)^4)<correction (faceRectangle R S) (verticalDiagram 2) := by
  have hfit := verticalDiagram_subset (by omega : 1≤R) hS
  have hc := profile_le_correction (verticalDiagram_ferrers 2) hfit
    (stripProfile_integrable (by positivity : (0 : ℝ)<(R : ℝ)+1))
    (fun θ hθ hγ => stripProfile_pointwise R hθ hγ)
  have hm := strip_moment_lower (r := (R : ℝ)+1) (by exact_mod_cast (show 5≤R+1 by omega))
  rw [← stripProfile_integral (by positivity : (0 : ℝ)<(R : ℝ)+1)] at hm
  have hh := hm.trans_le (mul_le_mul_of_nonneg_left hc (show 0≤((R : ℝ)+1)^4 by positivity))
  rw [div_lt_iff₀ (by positivity : 0 < 4*((R : ℝ)+1)^4)]
  nlinarith only [hh]

/-- Actual finite correction for the 2×2 corner square. -/
theorem square_defect_correction_lower {R S : ℕ} (hR : 4≤R) (hS : 2≤S) :
    20/((R : ℝ)+1)^4<correction (faceRectangle R S) (faceRectangle 2 2) := by
  have hfit : faceRectangle 2 2⊆faceRectangle R S :=
    FiniteGreenMonotonicity.rectangle_subset (by omega) hS
  have hc := profile_le_correction (faceRectangle_isFerrers 2 2) hfit
    (squareProfile_integrable (by positivity : (0 : ℝ)<(R : ℝ)+1))
    (fun θ hθ hγ => squareProfile_pointwise R hθ hγ)
  have hm := square_moment_lower (r := (R : ℝ)+1) (by exact_mod_cast (show 5≤R+1 by omega))
  rw [← squareProfile_integral (by positivity : (0 : ℝ)<(R : ℝ)+1)] at hm
  have hh := hm.trans_le (mul_le_mul_of_nonneg_left hc (show 0≤((R : ℝ)+1)^4 by positivity))
  rw [div_lt_iff₀ (by positivity : 0 < ((R : ℝ)+1)^4)]
  nlinarith only [hh]

/-- Primal-side formulation of both short-defect lower corrections. -/
theorem short_defect_lower_primal {r s : ℕ} (hr : 5≤r) (hrs : r≤s) :
    21/(4*(r : ℝ)^4)<correction (faceRectangle (r-1) (s-1)) (verticalDiagram 2) ∧
    20/(r : ℝ)^4<correction (faceRectangle (r-1) (s-1)) (faceRectangle 2 2) := by
  have h2 := two_cell_correction_lower (R := r-1) (S := s-1) (by omega) (by omega)
  have h4 := square_defect_correction_lower (R := r-1) (S := s-1) (by omega) (by omega)
  have he : ((r-1 : ℕ) : ℝ)+1=(r : ℝ) := by exact_mod_cast (show r-1+1=r by omega)
  rw [he] at h2 h4
  exact ⟨h2,h4⟩

end
end SpanningTreeIsoperimetry.FiniteShortDefectError
