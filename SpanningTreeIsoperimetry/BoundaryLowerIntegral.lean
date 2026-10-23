module

public import SpanningTreeIsoperimetry.QuadrantLowerTrace
public import SpanningTreeIsoperimetry.BoundaryLossKernel

@[expose] public section

/-! The lower Green trace is the integral of its actual finite quadratic
kernel, including signed inverse coefficients. -/
namespace SpanningTreeIsoperimetry.BoundaryLowerIntegral
open Ferrers CornerEnergy BoundaryGreenBounds QuadrantLowerTrace BoundaryKernelMajorant
  MeasureTheory Set
open scoped Classical BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def densityTrace (R : ℕ) (M : Diagram) (θ : ℝ) : ℝ :=
  ∑ i : {p // p∈M}, ∑ j : {p // p∈M}, (minor M)⁻¹ i j*
    density ((R : ℝ)+1) ((j.val.1 : ℝ)+1) ((i.val.1 : ℝ)+1) (j.val.2+1) (i.val.2+1) θ

def rawMode (M : Diagram) (θ : ℝ) (i : {p // p∈M}) : ℝ :=
  Real.sin (((i.val.2 : ℝ)+1)*θ)*Real.sinh (((i.val.1 : ℝ)+1)*RectangularRemainder.gamma θ)

theorem densityTrace_eq_quadratic (R : ℕ) (M : Diagram) (θ : ℝ) :
    densityTrace R M θ=
      (star (rawMode M θ) ⬝ᵥ ((minor M)⁻¹ *ᵥ rawMode M θ))/
        (Real.sinh (RectangularRemainder.gamma θ)*(Real.exp (2*((R : ℝ)+1)*RectangularRemainder.gamma θ)-1)) := by
  calc
    _=∑ i : {p // p∈M}, ∑ j : {p // p∈M},
        (rawMode M θ i*(minor M)⁻¹ i j*rawMode M θ j)/
        (Real.sinh (RectangularRemainder.gamma θ)*(Real.exp (2*((R : ℝ)+1)*RectangularRemainder.gamma θ)-1)) := by
      unfold densityTrace
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      unfold rawMode density
      push_cast
      ring
    _=(∑ i : {p // p∈M}, ∑ j : {p // p∈M}, rawMode M θ i*(minor M)⁻¹ i j*rawMode M θ j)/
        (Real.sinh (RectangularRemainder.gamma θ)*(Real.exp (2*((R : ℝ)+1)*RectangularRemainder.gamma θ)-1)) := by
      simp_rw [Finset.sum_div]
    _=_ := by
      congr 1
      simp only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem densityTrace_nonneg {R : ℕ} {M : Diagram} (hM : IsFerrers M)
    {θ : ℝ} (hθ : θ∈Icc (0 : ℝ) Real.pi) : 0≤densityTrace R M θ := by
  rw [densityTrace_eq_quadratic]
  have hq := (minor_posDef hM).inv.posSemidef.dotProduct_mulVec_nonneg (rawMode M θ)
  have hg := RectangularRemainder.gamma_nonneg hθ
  have hs := Real.sinh_nonneg_iff.mpr hg
  have he := Real.one_le_exp_iff.mpr
    (show 0≤2*((R : ℝ)+1)*RectangularRemainder.gamma θ by positivity)
  exact div_nonneg hq (mul_nonneg hs (by linarith))

theorem entry_integrable {R S : ℕ} {M : Diagram} (hfit : M⊆faceRectangle R S)
    (i j : {p // p∈M}) : IntervalIntegrable
      (fun θ => (minor M)⁻¹ i j*density ((R : ℝ)+1) ((j.val.1 : ℝ)+1)
        ((i.val.1 : ℝ)+1) (j.val.2+1) (i.val.2+1) θ) volume 0 Real.pi := by
  have hi := (mem_faceRectangle.mp (hfit i.property)).1
  have hj := (mem_faceRectangle.mp (hfit j.property)).1
  have hR : (0 : ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have hi' : (i.val.1 : ℝ)+1≤R := by exact_mod_cast (show i.val.1+1≤R by omega)
  have hj' : (j.val.1 : ℝ)+1≤R := by exact_mod_cast (show j.val.1+1≤R by omega)
  exact (density_intervalIntegrable (by positivity) (by positivity) hR hj' hi'
    (by linarith : (R : ℝ)<(R : ℝ)+1) (j.val.2+1) (i.val.2+1)).const_mul _

theorem densityTrace_integrable {R S : ℕ} {M : Diagram} (hfit : M⊆faceRectangle R S) :
    IntervalIntegrable (densityTrace R M) volume 0 Real.pi := by
  convert IntervalIntegrable.sum Finset.univ (fun i _ =>
    IntervalIntegrable.sum Finset.univ (fun j _ => entry_integrable hfit i j)) using 1
  funext θ
  simp only [densityTrace,Finset.sum_apply]

theorem trace_eq_integral {R S : ℕ} {M : Diagram} (hfit : M⊆faceRectangle R S) :
    Matrix.trace ((minor M)⁻¹*(minor M-stripMinorX R M))=
      (4/Real.pi)*(∫ θ in (0 : ℝ)..Real.pi, densityTrace R M θ) := by
  have he (i j : {p // p∈M}) : (minor M-stripMinorX R M) j i=
      (4/Real.pi)*(∫ θ in (0 : ℝ)..Real.pi,
        density ((R : ℝ)+1) ((j.val.1 : ℝ)+1) ((i.val.1 : ℝ)+1) (j.val.2+1) (i.val.2+1) θ) := by
    have hi := (mem_faceRectangle.mp (hfit i.property)).1
    have hj := (mem_faceRectangle.mp (hfit j.property)).1
    exact BoundaryLossKernel.stripX_loss_integral R ⟨j.val.1,hj⟩ ⟨i.val.1,hi⟩ j.val.2 i.val.2
  have hs : (∫ θ in (0 : ℝ)..Real.pi, densityTrace R M θ)=
      ∑ i : {p // p∈M}, ∑ j : {p // p∈M}, (minor M)⁻¹ i j*
        (∫ θ in (0 : ℝ)..Real.pi, density ((R : ℝ)+1) ((j.val.1 : ℝ)+1)
          ((i.val.1 : ℝ)+1) (j.val.2+1) (i.val.2+1) θ) := by
    unfold densityTrace
    have hi (i : {p // p∈M}) : IntervalIntegrable
        (fun θ => ∑ j : {p // p∈M}, (minor M)⁻¹ i j*density ((R : ℝ)+1)
          ((j.val.1 : ℝ)+1) ((i.val.1 : ℝ)+1) (j.val.2+1) (i.val.2+1) θ) volume 0 Real.pi := by
      convert IntervalIntegrable.sum Finset.univ (fun j _ => entry_integrable hfit i j) using 1
      funext θ
      simp only [Finset.sum_apply]
    rw [intervalIntegral.integral_finsetSum (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finsetSum (fun j _ => entry_integrable hfit i j)]
    simp_rw [intervalIntegral.integral_const_mul]
  rw [hs]
  change (∑ i, ∑ j, (minor M)⁻¹ i j*(minor M-stripMinorX R M) j i)=_
  simp_rw [he,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The entire finite-domain lower integral comparison has no kernel,
positive-definiteness, sign, or convergence premise. -/
theorem correction_ge_integral {R S : ℕ} {M : Diagram} (hM : IsFerrers M)
    (hfit : M⊆faceRectangle R S) :
    (4/Real.pi)*(∫ θ in (0 : ℝ)..Real.pi, densityTrace R M θ)≤correction (faceRectangle R S) M := by
  rw [← trace_eq_integral hfit]
  exact strip_lower_trace hM hfit

end
end SpanningTreeIsoperimetry.BoundaryLowerIntegral
