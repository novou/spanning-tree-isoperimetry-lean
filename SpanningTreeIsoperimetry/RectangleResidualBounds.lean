import SpanningTreeIsoperimetry.AngularKernelTaylor
import SpanningTreeIsoperimetry.CoupledRectangleError

/-! Pointwise logarithmic-residual bounds and convergent geometric tails for
the actual rectangular remainder. -/
namespace SpanningTreeIsoperimetry.RectangleResidualBounds

open RectangularRemainder AngularKernelTaylor SquareMaximality SquareMaximality.Rectangle
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def logTerm (s x : ℝ) : ℝ := Real.log (1-Real.exp (-2*s*x))

theorem logTerm_arg_pos {s x : ℝ} (hs : 0<s) (hx : 0<x) : 0<1-Real.exp (-2*s*x) := by
  rw [sub_pos,Real.exp_lt_one_iff]
  nlinarith

theorem hasDerivAt_logTerm {s x : ℝ} (hs : 0<s) (hx : 0<x) :
    HasDerivAt (logTerm s) (2*s/(Real.exp (2*s*x)-1)) x := by
  have hl : HasDerivAt (fun y : ℝ => -2*s*y) (-2*s) x := by
    simpa only [id_eq,mul_one] using (hasDerivAt_id x).const_mul (-2*s)
  have hd := ((hasDerivAt_const x 1).fun_sub hl.exp).log (logTerm_arg_pos hs hx).ne'
  have he : Real.exp (2*s*x)≠0 := (Real.exp_pos _).ne'
  have hden : Real.exp (2*s*x)-1≠0 := by
    apply (sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))).ne'
  unfold logTerm
  convert hd using 1
  have hn : -2*s*x= -(2*s*x) := by ring
  rw [hn,Real.exp_neg]
  field_simp
  ring

theorem logTerm_mono {s x y : ℝ} (hs : 0<s) (hx : 0<x) (hxy : x≤y) : logTerm s x≤logTerm s y := by
  unfold logTerm
  apply Real.log_le_log (logTerm_arg_pos hs hx)
  apply sub_le_sub_left
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hxy hs.le
  nlinarith

theorem logTerm_derivative_antitone {s x y : ℝ} (hs : 0<s) (hx : 0<x) (hxy : x≤y) :
    2*s/(Real.exp (2*s*y)-1)≤2*s/(Real.exp (2*s*x)-1) := by
  have hy : 0<y := lt_of_lt_of_le hx hxy
  have hdx : 0<Real.exp (2*s*x)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  have hdy : 0<Real.exp (2*s*y)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  have he : Real.exp (2*s*x)≤Real.exp (2*s*y) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hxy hs.le
    nlinarith
  apply (div_le_div_iff₀ hdy hdx).mpr
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right he 1) (by positivity)

theorem logTerm_difference_le {s x y : ℝ} (hs : 0<s) (hx : 0<x) (hxy : x≤y) :
    |logTerm s x-logTerm s y|≤(2*s/(Real.exp (2*s*x)-1))*(y-x) := by
  have hmono := logTerm_mono hs hx hxy
  rw [abs_of_nonpos (sub_nonpos.mpr hmono),neg_sub]
  apply (convex_Icc x y).image_sub_le_mul_sub_of_deriv_le
  · intro z hz
    exact (hasDerivAt_logTerm hs (hx.trans_le hz.1)).continuousAt.continuousWithinAt
  · intro z hz
    have hz' : z∈Set.Ioo x y := by simpa only [interior_Icc] using hz
    exact (hasDerivAt_logTerm hs (hx.trans hz'.1)).differentiableAt.differentiableWithinAt
  · intro z hz
    have hz' : z∈Set.Ioo x y := by simpa only [interior_Icc] using hz
    rw [(hasDerivAt_logTerm hs (hx.trans hz'.1)).deriv]
    exact logTerm_derivative_antitone hs hx hz'.1.le
  · exact ⟨le_rfl,hxy⟩
  · exact ⟨hxy,le_rfl⟩
  · exact hxy

theorem gamma_log_difference_le {s θ : ℝ} (hs : 0<s) (hθ : θ∈Set.Ioc 0 Real.pi) :
    |logTerm s (gamma θ)-logTerm s θ|≤s*θ^3/(6*(Real.exp (2*s*gamma θ)-1)) := by
  have hγ : 0<gamma θ := by
    have h := gamma_strictMonoOn ⟨le_rfl,Real.pi_pos.le⟩ ⟨hθ.1.le,hθ.2⟩ hθ.1
    simpa only [gamma_zero] using h
  have hden : 0<Real.exp (2*s*gamma θ)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  have h := logTerm_difference_le hs hγ (gamma_le_theta ⟨hθ.1.le,hθ.2⟩)
  have ht := mul_le_mul_of_nonneg_left (gamma_cubic_defect ⟨hθ.1.le,hθ.2⟩).2
    (show 0≤2*s/(Real.exp (2*s*gamma θ)-1) by positivity)
  refine (h.trans ht).trans_eq ?_
  field_simp [hden.ne'] <;> ring

/-- The scaled exponential reciprocal decreases, by convexity of exp. -/
theorem scaled_exp_reciprocal_antitone {c : ℝ} (hc : 0<c) :
    AntitoneOn (fun u : ℝ => u/(Real.exp (c*u)-1)) (Set.Ioi 0) := by
  intro u hu v hv huv
  by_cases heq : u=v
  · simp [heq]
  · have huv' : u<v := lt_of_le_of_ne huv heq
    have hcu : 0<c*u := mul_pos hc hu
    have hcv : 0<c*v := mul_pos hc hv
    have hcuv : c*u<c*v := mul_lt_mul_of_pos_left huv' hc
    have hs := strictConvexOn_exp.convexOn.slope_mono_adjacent (show (0 : ℝ)∈Set.univ from trivial)
      (show c*v∈Set.univ from trivial) hcu hcuv
    rw [Real.exp_zero,sub_zero] at hs
    have hx := (div_le_div_iff₀ hcu (sub_pos.mpr hcuv)).mp hs
    have hc' : c*((Real.exp (c*u)-1)*v)≤c*((Real.exp (c*v)-1)*u) := by nlinarith
    have hh := (mul_le_mul_iff_right₀ hc).mp hc'
    apply (div_le_div_iff₀ (sub_pos.mpr (Real.one_lt_exp_iff.mpr hcv))
      (sub_pos.mpr (Real.one_lt_exp_iff.mpr hcu))).mpr
    simpa only [mul_comm] using hh

/-- A retained nonlinear mode is controlled by a fixed geometric mode,
uniformly in every long side s at least r. -/
theorem scaled_mode_difference_le {r s j : ℝ} (hr : 0<r) (hrs : r≤s)
    (hj : 0<j) (hjr : j≤r) :
    |logTerm s (gamma (Real.pi*j/r))-logTerm s (Real.pi*j/r)|≤
      (Real.pi^3/(6*r^2))*(j^3/(Real.exp (4*Concrete.alpha*j)-1)) := by
  have hs : 0<s := hr.trans_le hrs
  let θ := Real.pi*j/r
  let u := s/r
  let c := 4*Concrete.alpha*j
  have hu : 1≤u := (one_le_div hr).mpr hrs
  have hu0 : 0<u := lt_of_lt_of_le zero_lt_one hu
  have hc : 0<c := by dsimp [c]; have := Concrete.alpha_pos; positivity
  have hθ : θ∈Set.Ioc 0 Real.pi := by
    refine ⟨by dsimp [θ]; positivity,?_⟩
    exact (div_le_iff₀ hr).mpr (mul_le_mul_of_nonneg_left hjr Real.pi_pos.le)
  have hchord : 2*Concrete.alpha*j/r≤gamma θ := by
    convert gamma_chord_lower ⟨hθ.1.le,hθ.2⟩ using 1
    dsimp [θ]
    field_simp [Real.pi_ne_zero] <;> ring
  have hex : c*u≤2*s*gamma θ := by
    have hm := mul_le_mul_of_nonneg_left hchord (show 0≤2*s by positivity)
    convert hm using 1 <;> dsimp [c,u] <;> ring
  have hd : 0<Real.exp (c*u)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hc hu0))
  have hden : Real.exp (c*u)-1≤Real.exp (2*s*gamma θ)-1 :=
    sub_le_sub_right (Real.exp_le_exp.mpr hex) 1
  have hp := gamma_log_difference_le hs hθ
  have hupper : s*θ^3/(6*(Real.exp (2*s*gamma θ)-1))≤
      s*θ^3/(6*(Real.exp (c*u)-1)) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left hden (by norm_num)
  have hmono := scaled_exp_reciprocal_antitone hc
    (by change (0 : ℝ)<1; norm_num) hu0 hu
  simp only [mul_one] at hmono
  calc
    _≤s*θ^3/(6*(Real.exp (c*u)-1)) := hp.trans hupper
    _=(Real.pi^3/(6*r^2)*j^3)*(u/(Real.exp (c*u)-1)) := by
      dsimp [θ,u]
      field_simp <;> ring
    _≤(Real.pi^3/(6*r^2)*j^3)*(1/(Real.exp c-1)) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _=_ := by dsimp [c]; ring

/-- The error in the genuine rectangle profile separates into the kernel
quadrature error, the finite logarithmic residual, and its endpoint term. -/
theorem error_exact {r s : ℕ} (hr : 0<r) (hs : 0<s) :
    error r s= -(s : ℝ)*(Concrete.epsilon squareLatticeEntropy r-Real.pi/(12*r))+
      (RectangularComparison.realResidual r s-linearResidual ((s : ℝ)/r))-
      (1/2)*Real.log (1-Real.exp (-4*r*Concrete.alpha)) := by
  rw [error,F_exact hr hs,B]
  ring

private theorem reciprocal_exp_sub {x : ℝ} (hx : 0<x) :
    1/(Real.exp x-1)=Real.exp (-x)/(1-Real.exp (-x)) := by
  have he : Real.exp x≠0 := (Real.exp_pos _).ne'
  have hd : Real.exp x-1≠0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)).ne'
  rw [Real.exp_neg]
  field_simp <;> ring

/-- A finite Bose sum is bounded by the locally evaluated cubic geometric
moment. The denominator is controlled uniformly for every retained mode. -/
theorem cubic_bose_sum_le (r : ℕ) :
    (∑ j∈Finset.Ico 1 r, (j : ℝ)^3/(Real.exp (4*Concrete.alpha*j)-1))≤
      (1+4*Concrete.q+Concrete.q^2)/(32*(1-Concrete.q)^3) := by
  have hq := Concrete.q_pos
  have hq1 := Concrete.q_lt_one
  have hqn : |Concrete.q|<1 := by rwa [abs_of_pos hq]
  have hsum := (CoupledRectangleError.geometricMoment_summable 3 hqn).hasSum
  rw [← CoupledRectangleError.geometricMoment,
    CoupledRectangleError.geometricMoment_three hqn] at hsum
  have hfinite : (∑ j∈Finset.Ico 1 r, (j : ℝ)^3*Concrete.q^j)≤
      CoupledRectangleError.moment3 Concrete.q :=
    sum_le_hasSum (Finset.Ico 1 r) (fun j _ => by positivity) hsum
  have hpoint (j : ℕ) (hj : j∈Finset.Ico 1 r) :
      (j : ℝ)^3/(Real.exp (4*Concrete.alpha*j)-1)≤
        ((j : ℝ)^3*Concrete.q^j)/(1-Concrete.q) := by
    have hjpos : 0<j := (Finset.mem_Ico.mp hj).1
    have hpower : Real.exp (-(4*Concrete.alpha*j))=Concrete.q^j := by
      rw [Concrete.q,← Real.exp_nat_mul]
      congr 1
      ring
    have hsmall : Concrete.q^j≤Concrete.q := by
      simpa using pow_le_pow_of_le_one hq.le hq1.le (show 1≤j by omega)
    have hrep : (j : ℝ)^3/(Real.exp (4*Concrete.alpha*j)-1)=
        (j : ℝ)^3*Concrete.q^j/(1-Concrete.q^j) := by
      rw [div_eq_mul_one_div,reciprocal_exp_sub (by have := Concrete.alpha_pos; positivity),hpower]
      ring
    rw [hrep]
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  calc
    _≤∑ j∈Finset.Ico 1 r, ((j : ℝ)^3*Concrete.q^j)/(1-Concrete.q) :=
      Finset.sum_le_sum hpoint
    _=(∑ j∈Finset.Ico 1 r, (j : ℝ)^3*Concrete.q^j)/(1-Concrete.q) := by rw [Finset.sum_div]
    _≤CoupledRectangleError.moment3 Concrete.q/(1-Concrete.q) :=
      div_le_div_of_nonneg_right hfinite (by linarith)
    _=(Concrete.q/(1-Concrete.q)^2)*(1+4*Concrete.q+Concrete.q^2)/(1-Concrete.q)^3 := by
      unfold CoupledRectangleError.moment3
      field_simp [(sub_pos.mpr hq1).ne'] <;> ring
    _=_ := by rw [Concrete.q_fraction]; field_simp [(sub_pos.mpr hq1).ne'] <;> ring

/-- The actual finite rectangular residual written in angular coordinates. -/
theorem realResidual_as_gamma {r : ℕ} (hr : 0<r) (s : ℝ) :
    RectangularComparison.realResidual r s=
      ∑ j∈Finset.Ico 1 r, logTerm s (gamma (Real.pi*j/r)) := by
  unfold RectangularComparison.realResidual
  apply Finset.sum_congr rfl
  intro j hj
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hjr : (j : ℝ)≤r := by exact_mod_cast (Finset.mem_Ico.mp hj).2.le
  have hθ : Real.pi*j/r∈Set.Icc 0 Real.pi := by
    refine ⟨by positivity,(div_le_iff₀ hrR).mpr ?_⟩
    exact mul_le_mul_of_nonneg_left hjr Real.pi_pos.le
  rw [gamma_eq_kernel hθ]
  have harg : (Real.pi*j/r)/Real.pi=(j : ℝ)/r := by field_simp <;> ring
  rw [harg]
  rfl

private theorem linear_mode_as_logTerm (r s j : ℝ) :
    Real.log (1-Real.exp (-2*Real.pi*(s/r)*j))=logTerm s (Real.pi*j/r) := by
  unfold logTerm
  congr 2
  ring

/-- Uniform comparison of all retained actual rectangle modes with their
linearized modes; the bound is the evaluated cubic geometric moment. -/
theorem retained_residual_bound {r s : ℕ} (hr : 0<r) (hrs : r≤s) :
    |RectangularComparison.realResidual r s-
      ∑ j∈Finset.Ico 1 r, Real.log (1-Real.exp (-2*Real.pi*((s : ℝ)/r)*j))|≤
      (Real.pi^3/(6*(r : ℝ)^2))*
        ((1+4*Concrete.q+Concrete.q^2)/(32*(1-Concrete.q)^3)) := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hrsR : (r : ℝ)≤s := by exact_mod_cast hrs
  rw [realResidual_as_gamma hr]
  simp_rw [linear_mode_as_logTerm]
  rw [← Finset.sum_sub_distrib]
  calc
    _≤∑ j∈Finset.Ico 1 r,
        |logTerm s (gamma (Real.pi*j/r))-logTerm s (Real.pi*j/r)| :=
      Finset.abs_sum_le_sum_abs _ _
    _≤∑ j∈Finset.Ico 1 r, (Real.pi^3/(6*(r : ℝ)^2))*
        ((j : ℝ)^3/(Real.exp (4*Concrete.alpha*j)-1)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj0 : (0 : ℝ)<j := by
        exact_mod_cast (show 0<j from (Finset.mem_Ico.mp hj).1)
      have hjr : (j : ℝ)≤r := by exact_mod_cast (Finset.mem_Ico.mp hj).2.le
      exact scaled_mode_difference_le hrR hrsR hj0 hjr
    _=(Real.pi^3/(6*(r : ℝ)^2))*(∑ j∈Finset.Ico 1 r,
        (j : ℝ)^3/(Real.exp (4*Concrete.alpha*j)-1)) := by rw [← Finset.mul_sum]
    _≤_ := mul_le_mul_of_nonneg_left (cubic_bose_sum_le r) (by positivity)

/-- The quadratic factor can be absorbed into a geometric tail uniformly
from its first positive integer index. -/
theorem quadratic_geometric_decay {q : ℝ} (hq0 : 0≤q) (hq : q≤1/4)
    {r : ℕ} (hr : 1≤r) : (r : ℝ)^2*q^r≤q := by
  induction r, hr using Nat.le_induction with
  | base => simp
  | succ r hr ih =>
    have hrR : (1 : ℝ)≤r := by exact_mod_cast hr
    have hsq : ((r : ℝ)+1)^2≤4*(r : ℝ)^2 := by nlinarith [sq_nonneg ((r : ℝ)-1)]
    have hstep : q*((r : ℝ)+1)^2≤(r : ℝ)^2 := by
      have hm := mul_le_mul_of_nonneg_right hq (sq_nonneg ((r : ℝ)+1))
      nlinarith
    calc
      ((r+1 : ℕ) : ℝ)^2*q^(r+1)=q^r*(q*((r : ℝ)+1)^2) := by push_cast; ring
      _≤q^r*(r : ℝ)^2 := mul_le_mul_of_nonneg_left hstep (pow_nonneg hq0 r)
      _≤q := by simpa only [mul_comm] using ih

def logTail (q : ℝ) (r : ℕ) : ℝ := ∑' n : ℕ, Real.log (1-q^(r+n))

theorem logTail_summable {q : ℝ} (hq0 : 0<q) (hq1 : q<1) (r : ℕ) :
    Summable (fun n : ℕ => Real.log (1-q^(r+n))) := by
  have hgeom := (hasSum_geometric_of_abs_lt_one (by rwa [abs_of_pos hq0])).summable
  have hs := (hgeom.mul_left (q^r)).neg
  have h := Real.summable_log_one_add_of_summable hs
  simpa only [pow_add,sub_eq_add_neg] using h

private theorem exp_natural_mode (u : ℝ) (n : ℕ) :
    Real.exp (-2*Real.pi*u)^n=Real.exp (-2*Real.pi*u*n) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Exact split of the convergent linear profile into retained rectangle modes
and the omitted geometric logarithmic tail. -/
theorem linearResidual_decomposition {u : ℝ} (hu : 0<u) {r : ℕ} (hr : 0<r) :
    linearResidual u=(∑ j∈Finset.Ico 1 r, Real.log (1-Real.exp (-2*Real.pi*u*j)))+
      logTail (Real.exp (-2*Real.pi*u)) r := by
  have hs := linearResidual_summable hu
  unfold linearResidual
  rw [← hs.sum_add_tsum_nat_add (r-1),Finset.sum_Ico_eq_sum_range]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    congr 2
    push_cast
    ring
  · unfold logTail
    apply tsum_congr
    intro n
    rw [exp_natural_mode]
    congr 2
    push_cast [Nat.cast_sub (show 1≤r by omega)]
    ring

theorem logTail_bound {q : ℝ} (hq0 : 0<q) (hq1 : q<1) {r : ℕ} (hr : 0<r) :
    |logTail q r|≤q^r/(1-q)^2 := by
  have hs := logTail_summable hq0 hq1 r
  have hnonpos : logTail q r≤0 := by
    have h := hs.tsum_le_tsum (fun n => Real.log_nonpos
      (sub_pos.mpr (pow_lt_one₀ hq0.le hq1 (by omega : r+n≠0))).le
      (by have hh := pow_nonneg hq0.le (r+n); linarith)) summable_zero
    simpa only [logTail,tsum_zero] using h
  rw [abs_of_nonpos hnonpos,logTail,← tsum_neg]
  have hg := (hasSum_geometric_of_abs_lt_one (by rwa [abs_of_pos hq0])).mul_left (q^r)
  have hg' := hg.div_const (1-q)
  have hsum : HasSum (fun n : ℕ => q^(r+n)/(1-q)) (q^r/(1-q)^2) := by
    convert hg' using 1 <;> (try simp only [pow_add]) <;> (try rfl) <;>
      field_simp [(sub_pos.mpr hq1).ne'] <;> ring
  refine (hs.neg.tsum_le_tsum (fun n => ?_) hsum.summable).trans_eq hsum.tsum_eq
  have hpow : q^(r+n)≤q := pow_le_of_le_one hq0.le hq1.le (by omega)
  have hpow1 : q^(r+n)<1 := pow_lt_one₀ hq0.le hq1 (by omega)
  refine (Concrete.Inputs.neg_log_one_sub_le (pow_nonneg hq0.le _) hpow1).trans ?_
  apply (div_le_div_iff₀ (sub_pos.mpr hpow1) (sub_pos.mpr hq1)).mpr
  exact mul_le_mul_of_nonneg_left (by linarith : 1-q≤1-q^(r+n)) (pow_nonneg hq0.le _)

/-- The omitted linear modes have a uniform quadratic error bound. -/
theorem logTail_quadratic_bound {q : ℝ} (hq0 : 0<q) (hq : q≤1/4)
    {r : ℕ} (hr : 0<r) : |logTail q r|≤q/((1-q)^2*(r : ℝ)^2) := by
  have hq1 : q<1 := by linarith
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hdecay := quadratic_geometric_decay hq0.le hq (show 1≤r by omega)
  have hpow : q^r≤q/(r : ℝ)^2 :=
    (le_div_iff₀ (sq_pos_of_pos hrR)).mpr (by simpa only [mul_comm] using hdecay)
  calc
    |logTail q r|≤q^r/(1-q)^2 := logTail_bound hq0 hq1 hr
    _≤(q/(r : ℝ)^2)/(1-q)^2 := div_le_div_of_nonneg_right hpow (sq_nonneg _)
    _=q/((1-q)^2*(r : ℝ)^2) := by
      field_simp [hrR.ne',(sub_pos.mpr hq1).ne'] <;> ring

end
end SpanningTreeIsoperimetry.RectangleResidualBounds
