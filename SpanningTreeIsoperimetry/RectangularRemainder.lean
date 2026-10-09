import SpanningTreeIsoperimetry.RectangularComparison
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! Exact normalized remainder of the actual rectangle tree count and the
convergent aspect profiles. Quantitative higher-order bounds are separate. -/
namespace SpanningTreeIsoperimetry.RectangularRemainder

open SquareMaximality SquareMaximality.Rectangle
open Concrete Kernel Trapezoid
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

/-- Smooth angular form of the lattice kernel. -/
def gamma (θ : ℝ) : ℝ := 2*Real.arsinh (Real.sin (θ/2))

def gammaDeriv (θ : ℝ) : ℝ :=
  Real.cos (θ/2)/Real.sqrt (1+Real.sin (θ/2)^2)

theorem hasDerivAt_gamma (θ : ℝ) : HasDerivAt gamma (gammaDeriv θ) θ := by
  have hs := ((hasDerivAt_id θ).div_const 2).sin
  have h := ((Real.hasDerivAt_arsinh (Real.sin (θ/2))).comp θ hs).const_mul 2
  unfold gamma gammaDeriv
  convert h using 1 <;> dsimp [Function.comp_def] <;> ring

@[simp] theorem gamma_zero : gamma 0=0 := by simp [gamma]
@[simp] theorem gamma_pi : gamma Real.pi=2*alpha := by simp [gamma,alpha]

theorem gamma_eq_kernel {θ : ℝ} (hθ : θ∈Set.Icc 0 Real.pi) :
    gamma θ=kernel (θ/Real.pi) := by
  rw [kernel_eq_two_mul_arsinh_halfSine (show θ/Real.pi∈Set.Icc 0 1 by
    constructor
    · exact div_nonneg hθ.1 Real.pi_pos.le
    · exact (div_le_one Real.pi_pos).mpr hθ.2)]
  unfold gamma halfSine
  congr 2
  field_simp <;> ring

theorem sinh_gamma_mul_deriv (θ : ℝ) : Real.sinh (gamma θ)*gammaDeriv θ=Real.sin θ := by
  rw [gamma,Real.sinh_two_mul,Real.sinh_arsinh,Real.cosh_arsinh,gammaDeriv]
  have hs : Real.sqrt (1+Real.sin (θ/2)^2)≠0 := by positivity
  have hsin : Real.sin θ=2*Real.sin (θ/2)*Real.cos (θ/2) := by
    calc
      Real.sin θ=Real.sin (2*(θ/2)) := by congr 1; ring
      _=2*Real.sin (θ/2)*Real.cos (θ/2) := Real.sin_two_mul _
  rw [hsin]
  field_simp <;> ring

theorem gamma_strictMonoOn : StrictMonoOn gamma (Set.Icc 0 Real.pi) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 Real.pi)
  · exact fun θ _ => (hasDerivAt_gamma θ).continuousAt.continuousWithinAt
  · intro θ hθ
    have hθ' : θ∈Set.Ioo 0 Real.pi := by simpa only [interior_Icc] using hθ
    rw [(hasDerivAt_gamma θ).deriv,gammaDeriv]
    apply div_pos
    · apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith [Real.pi_pos,hθ'.1,hθ'.2]
    · positivity

private theorem arsinh_lower {v : ℝ} (hv : v∈Set.Icc 0 1) :
    v/Real.sqrt (1+v^2)≤Real.arsinh v := by
  by_cases hv0 : v=0
  · simp [hv0]
  · have hvpos : 0<v := lt_of_le_of_ne hv.1 (Ne.symm hv0)
    have h := arsinh_concaveOn.le_slope_of_hasDerivAt
      (show (0 : ℝ)∈Set.Icc 0 1 by constructor <;> norm_num) hv hvpos (Real.hasDerivAt_arsinh v)
    simp only [slope_def_field,Real.arsinh_zero,sub_zero] at h
    have hm := (le_div_iff₀ hvpos).mp h
    simpa only [div_eq_mul_inv,mul_comm] using hm

/-- Angular bound needed by the boundary-loss change of variables. -/
theorem sin_le_gamma {θ : ℝ} (hθ : θ∈Set.Icc 0 Real.pi) : Real.sin θ≤gamma θ := by
  let v := Real.sin (θ/2)
  let c := Real.cos (θ/2)
  let d := Real.sqrt (1+v^2)
  have hv0 : 0≤v := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2,Real.pi_pos])
  have hv1 : v≤1 := Real.sin_le_one _
  have hc0 : 0≤c := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1,Real.pi_pos],by linarith [hθ.2]⟩
  have hd : 0<d := by dsimp [d]; positivity
  have hd2 : d^2=1+v^2 := Real.sq_sqrt (by positivity)
  have hc2 : c^2=1-v^2 := by
    have h := Real.sin_sq_add_cos_sq (θ/2)
    change v^2+c^2=1 at h
    linarith
  have hprod : c*d≤1 := by
    have he : (c*d)^2=1-v^4 := by rw [mul_pow,hd2,hc2]; ring
    nlinarith [sq_nonneg (v^2)]
  have hcos : c≤1/d := (le_div_iff₀ hd).mpr hprod
  have ha := arsinh_lower (show v∈Set.Icc 0 1 from ⟨hv0,hv1⟩)
  have hm := mul_le_mul_of_nonneg_left hcos (show 0≤2*v by positivity)
  have hs : Real.sin θ=2*v*c := by
    calc
      Real.sin θ=Real.sin (2*(θ/2)) := by congr 1; ring
      _=2*v*c := Real.sin_two_mul _
  rw [hs]
  change 2*v*c≤2*Real.arsinh v
  dsimp [d] at hm
  calc
    2*v*c≤2*v*(1/Real.sqrt (1+v^2)) := hm
    _=2*(v/Real.sqrt (1+v^2)) := by ring
    _≤2*Real.arsinh v := mul_le_mul_of_nonneg_left ha (by norm_num)

theorem contDiff_gamma : ContDiff ℝ ⊤ gamma := by
  unfold gamma
  fun_prop

theorem analyticAt_gamma (θ : ℝ) : AnalyticAt ℝ gamma θ := by
  unfold gamma
  fun_prop

theorem continuous_gammaDeriv : Continuous gammaDeriv := by
  unfold gammaDeriv
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro θ
    positivity

theorem gamma_nonneg {θ : ℝ} (hθ : θ∈Set.Icc 0 Real.pi) : 0≤gamma θ := by
  have h := gamma_strictMonoOn.monotoneOn
    (show (0 : ℝ)∈Set.Icc 0 Real.pi by exact ⟨le_rfl,Real.pi_pos.le⟩) hθ hθ.1
  simpa only [gamma_zero] using h

theorem gamma_le_theta {θ : ℝ} (hθ : θ∈Set.Icc 0 Real.pi) : gamma θ≤θ := by
  rw [gamma_eq_kernel hθ]
  have h := EpsilonBounds.kernel_le_pi_mul (show θ/Real.pi∈Set.Icc 0 1 from
    ⟨div_nonneg hθ.1 Real.pi_pos.le,(div_le_one Real.pi_pos).mpr hθ.2⟩)
  have he : Real.pi*(θ/Real.pi)=θ := by field_simp
  simpa only [he] using h

theorem gamma_chord_lower {θ : ℝ} (hθ : θ∈Set.Icc 0 Real.pi) :
    (2*alpha/Real.pi)*θ≤gamma θ := by
  have h := kernel_chord_lower_real (div_nonneg hθ.1 Real.pi_pos.le)
    ((div_le_one Real.pi_pos).mpr hθ.2)
  rw [← gamma_eq_kernel hθ] at h
  convert h using 1 <;> ring

/-- The actual logarithmic area-boundary remainder. -/
def F (r s : ℕ) : ℝ :=
  Real.log (SpanningTreeIsoperimetry.treeCount (SpanningTreeIsoperimetry.rectangle r s) : ℝ)-
    squareLatticeEntropy*r*s+alpha*((r : ℝ)+s)

theorem F_eq_neg_remainder {r s : ℕ} (hr : 0<r) (hs : 0<s) :
    F r s= -RectangularComparison.remainder r s := by
  rw [F,RectangularComparison.remainder,RectangularComparison.ell_nat_eq_log_treeCount hr hs]
  ring

private def cosineLogSum (r : ℕ) (a : ℝ) : ℝ :=
  ∑ k∈Finset.range (r-1), Real.log (a-Real.cos (((k : ℝ)+1)*Real.pi/r))

private theorem node_kernel_pos {r k : ℕ} (hr : 0<r) (hk : k∈Finset.range (r-1)) :
    0<kernel (((k : ℝ)+1)/r) := by
  have h := Product.kernel_pos_of_mem_Ico hr (j := k+1) (Finset.mem_Ico.mpr ⟨by omega,by
    have h := Finset.mem_range.mp hk
    omega⟩)
  simpa only [Nat.cast_add,Nat.cast_one] using h

private theorem node_cos_lt_one {r k : ℕ} (hr : 0<r) (hk : k∈Finset.range (r-1)) :
    Real.cos (((k : ℝ)+1)*Real.pi/r)<1 := by
  have h := Real.one_lt_cosh.mpr (ne_of_gt (node_kernel_pos hr hk))
  rw [Product.cosh_kernel] at h
  have he : Real.pi*(((k : ℝ)+1)/r)=((k : ℝ)+1)*Real.pi/r := by ring
  rw [he] at h
  linarith

private theorem log_tanh_half (z : ℝ) (hz : 0<z) :
    2*Real.log (Real.tanh (z/2))=Real.log (Real.cosh z-1)-Real.log (Real.cosh z+1) := by
  have h := congrArg Real.log (Product.cosh_sub_one_eq_sinh_mul_tanh_half z)
  rw [Real.log_mul (Real.sinh_pos_iff.mpr hz).ne' (Product.tanh_half_pos hz).ne'] at h
  have hhalf := SharpTrapezoid.endpoint_halfLog_eq_log_sinh hz
  linarith

private theorem cosineLogSum_one {r : ℕ} (hr : 0<r) :
    cosineLogSum r 1=Real.log (r : ℝ)-((r : ℝ)-1)*Real.log 2 := by
  have h := congrArg Real.log (Product.zeroRowProduct_eq hr)
  unfold Product.zeroRowProduct at h
  rw [Real.log_prod (fun k hk => (mul_pos (by norm_num) (sub_pos.mpr (node_cos_lt_one hr hk))).ne')] at h
  have he : (∑ k∈Finset.range (r-1), Real.log (2*(1-Real.cos (((k : ℝ)+1)*Real.pi/r))))=
      ((r : ℝ)-1)*Real.log 2+cosineLogSum r 1 := by
    calc
      _=∑ k∈Finset.range (r-1), (Real.log 2+Real.log (1-Real.cos (((k : ℝ)+1)*Real.pi/r))) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact Real.log_mul (by norm_num) (sub_pos.mpr (node_cos_lt_one hr hk)).ne'
      _=_ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,cosineLogSum]
        rw [Nat.cast_sub (by omega)]
        norm_num
  rw [he] at h
  linarith

private theorem cosh_two_alpha : Real.cosh (2*alpha)=3 := by
  rw [Real.cosh_two_mul,alpha,Real.cosh_arsinh,Real.sinh_arsinh]
  norm_num

private theorem cosineLogSum_three {r : ℕ} (hr : 0<r) :
    cosineLogSum r 3=2*r*alpha-((r : ℝ)+3/2)*Real.log 2+
      Real.log (1-Real.exp (-4*r*alpha)) := by
  have h := SharpTrapezoid.halfGridLogSum_eq (r-1) (show 0<2*alpha from mul_pos (by norm_num) alpha_pos)
  have hc : ((r-1 : ℕ) : ℝ)+1=r := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hfour : Real.log (4 : ℝ)=2*Real.log 2 := by
    rw [show (4 : ℝ)=(2 : ℝ)^2 by norm_num,Real.log_pow]
    norm_num
  unfold SharpTrapezoid.halfGridLogSum at h
  rw [cosh_two_alpha,hc] at h
  norm_num only [show (3 : ℝ)-1=2 by norm_num,show (3 : ℝ)+1=4 by norm_num] at h
  rw [hfour] at h
  have hex : -2*((r : ℝ)*(2*alpha))= -4*r*alpha := by ring
  rw [hex] at h
  change (Real.log 2+2*Real.log 2)/2+cosineLogSum r 3=
    (r : ℝ)*(2*alpha-Real.log 2)+Real.log (1-Real.exp (-4*r*alpha)) at h
  linarith

/-- Explicit normalization of the already verified hyperbolic spectral base. -/
theorem spectralBase_exact {r : ℕ} (hr : 0<r) :
    Product.spectralBase r= -(1/2)*Real.log (r : ℝ)+(5/4)*Real.log 2-
      (r : ℝ)*alpha-(1/2)*Real.log (1-Real.exp (-4*r*alpha)) := by
  have hsum : 2*(∑ j∈Finset.Ico 1 r,Real.log (Real.tanh (kernel ((j : ℝ)/r)/2)))=
      cosineLogSum r 1-cosineLogSum r 3 := by
    rw [Finset.sum_Ico_eq_sum_range,Finset.mul_sum]
    unfold cosineLogSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Nat.cast_add,Nat.cast_one]
    have h := log_tanh_half (kernel (((k : ℝ)+1)/r)) (node_kernel_pos hr hk)
    rw [Product.cosh_kernel] at h
    have he : Real.pi*(((k : ℝ)+1)/r)=((k : ℝ)+1)*Real.pi/r := by ring
    rw [he] at h
    convert h using 1 <;> congr 2 <;> ring
  rw [cosineLogSum_one hr,cosineLogSum_three hr] at hsum
  unfold Product.spectralBase
  rw [Real.log_inv]
  linarith

/-- Appendix A's exact formula, attached to the actual graph tree count. -/
theorem F_exact {r s : ℕ} (hr : 0<r) (hs : 0<s) :
    F r s= -(1/2)*Real.log (r : ℝ)+(5/4)*Real.log 2-
      (s : ℝ)*epsilon squareLatticeEntropy r+RectangularComparison.realResidual r s-
      (1/2)*Real.log (1-Real.exp (-4*r*alpha)) := by
  rw [F,← RectangularComparison.ell_nat_eq_log_treeCount hr hs,RectangularComparison.ell,spectralBase_exact hr]
  unfold epsilon
  ring

/-- Linearized residual; indexing by `n+1` excludes its singular zero mode. -/
def linearResidual (u : ℝ) : ℝ :=
  ∑' n : ℕ, Real.log (1-Real.exp (-2*Real.pi*u*(n+1)))

def B (u : ℝ) : ℝ := (5/4)*Real.log 2-Real.pi*u/12+linearResidual u

def J (u : ℝ) : ℝ := B u+(1/4)*Real.log u

def K (u : ℝ) : ℝ := B u+(1/2)*Real.log (1+u)

def error (r s : ℕ) : ℝ := F r s+(1/2)*Real.log (r : ℝ)-B ((s : ℝ)/r)

theorem linearResidual_summable {u : ℝ} (hu : 0<u) :
    Summable (fun n : ℕ => Real.log (1-Real.exp (-2*Real.pi*u*(n+1)))) := by
  let q := Real.exp (-2*Real.pi*u)
  have hq0 : 0<q := Real.exp_pos _
  have hq1 : q<1 := by rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have hgeom : Summable (fun n : ℕ => q^n) :=
    (hasSum_geometric_of_abs_lt_one (by rwa [abs_of_pos hq0])).summable
  have hs : Summable (fun n : ℕ => -(q^(n+1))) := by
    simpa only [pow_succ] using (hgeom.mul_right q).neg
  have hlog := Real.summable_log_one_add_of_summable hs
  apply hlog.congr
  intro n
  have he : q^(n+1)=Real.exp (-2*Real.pi*u*(n+1)) := by
    dsimp only [q]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [he]
  rfl

theorem linearResidual_mono {u v : ℝ} (hu : 0<u) (huv : u≤v) : linearResidual u≤linearResidual v := by
  unfold linearResidual
  apply (linearResidual_summable hu).tsum_le_tsum _ (linearResidual_summable (by linarith))
  intro n
  have hpos : 0<1-Real.exp (-2*Real.pi*u*(n+1)) := by
    rw [sub_pos,Real.exp_lt_one_iff]
    have hh : 0<2*Real.pi*u*((n : ℝ)+1) := by positivity
    nlinarith
  apply Real.log_le_log hpos
  apply sub_le_sub_left
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right huv (show 0≤2*Real.pi*((n : ℝ)+1) by positivity)
  nlinarith

end
end SpanningTreeIsoperimetry.RectangularRemainder
