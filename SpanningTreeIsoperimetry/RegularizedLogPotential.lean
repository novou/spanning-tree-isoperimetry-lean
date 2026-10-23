module

public import SpanningTreeIsoperimetry.RegularizedStripSymbol
public import SquareMaximality.Rectangle.SharpTrapezoid
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! The symmetric logarithmic potential whose one-variable average is the
actual regularized angular kernel. This allows the Fourier--Laplace identity
to be proved above the critical spectral parameter without singular Fubini. -/
namespace SpanningTreeIsoperimetry.RegularizedLogPotential
open RegularizedStripSymbol MeasureTheory Set
noncomputable section

def potential (z x y : ℝ) : ℝ := Real.log (z-2*Real.cos x-2*Real.cos y)

theorem potential_comm (z x y : ℝ) : potential z x y=potential z y x := by
  unfold potential
  congr 1
  ring

theorem argument_pos {z : ℝ} (hz : 4<z) (x y : ℝ) : 0<z-2*Real.cos x-2*Real.cos y := by
  linarith [Real.cos_le_one x,Real.cos_le_one y]

theorem continuous_potential {z : ℝ} (hz : 4<z) :
    Continuous (fun p : ℝ×ℝ => potential z p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hi : ContinuousAt (fun q : ℝ×ℝ => z-2*Real.cos q.1-2*Real.cos q.2) p := by fun_prop
  exact (Real.continuousAt_log (argument_pos hz p.1 p.2).ne').comp_of_eq hi rfl

theorem cosh_gamma {z : ℝ} (hz : 4<z) (θ : ℝ) :
    Real.cosh (gammaZ z θ)=z/2-Real.cos θ := by
  apply Real.cosh_arcosh
  linarith [Real.cos_le_one θ]

theorem potential_integral {z : ℝ} (hz : 4<z) (θ : ℝ) :
    (∫ φ in (0 : ℝ)..Real.pi,potential z θ φ)=Real.pi*gammaZ z θ := by
  have hg := gammaZ_pos hz θ
  have hpos (φ : ℝ) : 0<Real.cosh (gammaZ z θ)-Real.cos φ := by
    rw [cosh_gamma hz]
    linarith [Real.cos_le_one θ,Real.cos_le_one φ]
  have hc : Continuous (fun φ : ℝ => Real.log (Real.cosh (gammaZ z θ)-Real.cos φ)) := by
    apply continuous_iff_continuousAt.mpr
    intro φ
    have hi : ContinuousAt (fun x : ℝ => Real.cosh (gammaZ z θ)-Real.cos x) φ := by fun_prop
    exact (Real.continuousAt_log (hpos φ).ne').comp_of_eq hi rfl
  have he (φ : ℝ) : potential z θ φ=Real.log 2+Real.log (Real.cosh (gammaZ z θ)-Real.cos φ) := by
    unfold potential
    have ha : z-2*Real.cos θ-2*Real.cos φ=2*(Real.cosh (gammaZ z θ)-Real.cos φ) := by
      rw [cosh_gamma hz]
      ring
    rw [ha,Real.log_mul (by norm_num : (2 : ℝ)≠0) (hpos φ).ne']
  simp_rw [he]
  rw [intervalIntegral.integral_add intervalIntegrable_const (hc.intervalIntegrable _ _),
    intervalIntegral.integral_const,SquareMaximality.Rectangle.SharpTrapezoid.integral_log_cosh_sub_cos hg]
  simp only [sub_zero,smul_eq_mul]
  ring

/-- All order exchanges for the regularized log-potential cosine integral
are justified by compact-set integrability of a continuous function. -/
theorem potential_cosine_swap {z : ℝ} (hz : 4<z) (j : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi,∫ φ in (0 : ℝ)..Real.pi,
      potential z θ φ*Real.cos ((j : ℝ)*θ))=
    ∫ φ in (0 : ℝ)..Real.pi,∫ θ in (0 : ℝ)..Real.pi,
      potential z θ φ*Real.cos ((j : ℝ)*θ) := by
  have hc : Continuous (fun p : ℝ×ℝ => potential z p.1 p.2*Real.cos ((j : ℝ)*p.1)) :=
    (continuous_potential hz).mul (by fun_prop)
  apply intervalIntegral_intervalIntegral_swap
  exact hc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc) |>.mono_set
    (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)

end
end SpanningTreeIsoperimetry.RegularizedLogPotential
