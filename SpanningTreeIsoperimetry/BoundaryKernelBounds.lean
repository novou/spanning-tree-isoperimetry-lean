import SpanningTreeIsoperimetry.RectangularRemainder
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-! Pointwise sine/hyperbolic bounds for the separated boundary-loss kernel. -/
namespace SpanningTreeIsoperimetry.BoundaryKernelBounds
open Set RectangularRemainder
open scoped Topology
noncomputable section

theorem sinh_convex_nonnegative : ConvexOn ℝ (Ici (0 : ℝ)) Real.sinh := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ici 0)
    Real.continuous_sinh.continuousOn Real.differentiable_sinh.differentiableOn
  intro x hx y hy hxy
  simp only [Real.deriv_sinh]
  have hx0 : 0≤x := by
    have h : 0<x := by simpa only [interior_Ici,mem_Ioi] using hx
    exact h.le
  have hy0 : 0≤y := by
    have h : 0<y := by simpa only [interior_Ici,mem_Ioi] using hy
    exact h.le
  exact Real.cosh_strictMonoOn.monotoneOn hx0 hy0 hxy

/-- Convexity at the absorbing endpoint gives the exact sinh scaling bound. -/
theorem sinh_scale_le {a c t : ℝ} (ha : 0≤a) (hc : 0<c) (hac : a≤c) (ht : 0≤t) :
    Real.sinh (a*t)≤(a/c)*Real.sinh (c*t) := by
  have hq : 0≤a/c := div_nonneg ha hc.le
  have hq1 : a/c≤1 := (div_le_one₀ hc).mpr hac
  have h := sinh_convex_nonnegative.2 (x := (0 : ℝ)) (y := c*t)
    (show (0 : ℝ)∈Ici (0 : ℝ) by norm_num) (show c*t∈Ici (0 : ℝ) by exact mul_nonneg hc.le ht)
    (show 0≤1-a/c by linarith) hq (show (1-a/c)+a/c=1 by ring)
  have he : (a/c)*(c*t)=a*t := by field_simp
  simpa only [smul_eq_mul,mul_zero,zero_add,Real.sinh_zero,he] using h

theorem sinh_pair_le {a b c t : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0<c)
    (hac : a≤c) (hbc : b≤c) (ht : 0≤t) :
    Real.sinh (a*t)*Real.sinh (b*t)≤(a*b/c^2)*Real.sinh (c*t)^2 := by
  have h := mul_le_mul (sinh_scale_le ha hc hac ht) (sinh_scale_le hb hc hbc ht)
    (Real.sinh_nonneg_iff.mpr (mul_nonneg hb ht))
    (mul_nonneg (div_nonneg ha hc.le) (Real.sinh_nonneg_iff.mpr (mul_nonneg hc.le ht)))
  convert h using 1 <;> ring

/-- The integer-frequency sine bound, with no Fourier-coefficient premise. -/
theorem abs_sin_nat_mul_le (n : ℕ) (x : ℝ) : |Real.sin ((n : ℝ)*x)|≤n*|Real.sin x| := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    rw [add_mul,one_mul,Real.sin_add]
    calc
      _≤|Real.sin ((n : ℝ)*x)*Real.cos x| + |Real.cos ((n : ℝ)*x)*Real.sin x| := abs_add_le _ _
      _=|Real.sin ((n : ℝ)*x)| * |Real.cos x| + |Real.cos ((n : ℝ)*x)| * |Real.sin x| := by rw [abs_mul,abs_mul]
      _≤(n : ℝ)*|Real.sin x| + |Real.sin x| :=
        add_le_add ((mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one x)).trans ih)
          (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one ((n : ℝ)*x)))
      _=((n : ℝ)+1)*|Real.sin x| := by ring

theorem sin_pair_le (a b : ℕ) (x : ℝ) :
    Real.sin ((a : ℝ)*x)*Real.sin ((b : ℝ)*x)≤(a : ℝ)*b*Real.sin x^2 := by
  calc
    _≤|Real.sin ((a : ℝ)*x)*Real.sin ((b : ℝ)*x)| := le_abs_self _
    _=|Real.sin ((a : ℝ)*x)| * |Real.sin ((b : ℝ)*x)| := abs_mul _ _
    _≤((a : ℝ)*|Real.sin x|)*((b : ℝ)*|Real.sin x|) :=
      mul_le_mul (abs_sin_nat_mul_le a x) (abs_sin_nat_mul_le b x)
        (abs_nonneg _) (by positivity)
    _=(a : ℝ)*b*Real.sin x^2 := by rw [mul_mul_mul_comm,← pow_two,sq_abs]

theorem gamma_pos {θ : ℝ} (hθ : θ∈Ioo (0 : ℝ) Real.pi) : 0<gamma θ := by
  have h := gamma_strictMonoOn ⟨le_rfl,Real.pi_pos.le⟩ ⟨hθ.1.le,hθ.2.le⟩ hθ.1
  simpa only [gamma_zero] using h

theorem gammaDeriv_nonneg {θ : ℝ} (hθ : θ∈Icc (0 : ℝ) Real.pi) : 0≤gammaDeriv θ := by
  unfold gammaDeriv
  apply div_nonneg
  · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos,hθ.1],by linarith [hθ.2]⟩
  · positivity

/-- The exact Jacobian relation and the angular bound give the t-factor
in the upper majorant after the gamma substitution. -/
theorem sin_sq_div_sinh_gamma_le {θ : ℝ} (hθ : θ∈Ioo (0 : ℝ) Real.pi) :
    Real.sin θ^2/Real.sinh (gamma θ)≤gamma θ*gammaDeriv θ := by
  have hg : 0<gamma θ := gamma_pos hθ
  have hs : Real.sinh (gamma θ)≠0 := (Real.sinh_pos_iff.mpr hg).ne'
  have he : Real.sin θ^2/Real.sinh (gamma θ)=Real.sin θ*gammaDeriv θ := by
    apply (div_eq_iff hs).mpr
    rw [mul_assoc,← mul_comm (Real.sinh (gamma θ)) (gammaDeriv θ),sinh_gamma_mul_deriv]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (sin_le_gamma ⟨hθ.1.le,hθ.2.le⟩)
    (gammaDeriv_nonneg ⟨hθ.1.le,hθ.2.le⟩)

end
end SpanningTreeIsoperimetry.BoundaryKernelBounds
