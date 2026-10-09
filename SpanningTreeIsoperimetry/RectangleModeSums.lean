import SpanningTreeIsoperimetry.LogResidualTaylor
import SpanningTreeIsoperimetry.RetainedModeBounds

/-! Actual finite mode-sum estimates for the fourth-order rectangle expansion. -/
namespace SpanningTreeIsoperimetry.RectangleModeSums

open SquareMaximality.Rectangle RectangularRemainder RectangleResidualBounds
open LogResidualTaylor RetainedModeBounds CoupledRectangleError
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem alpha_gt_half : (1 : ℝ)/2<Concrete.alpha := by
  have hs : 1<Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤2),Real.sqrt_nonneg (2 : ℝ)]
  have hl := Real.log_lt_log (by norm_num : (0 : ℝ)<2) (by linarith : (2 : ℝ)<1+Real.sqrt 2)
  rw [← Concrete.exp_alpha,Real.log_exp] at hl
  linarith [Real.log_two_gt_d9]

theorem q_alpha_le : Concrete.q≤(1 : ℝ)/33 := by
  rw [Concrete.q,show -4*Concrete.alpha= -(4*Concrete.alpha) by ring,Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<33)
    exp_four_alpha_gt_thirtythree.le

theorem q_pi_le : Real.exp (-2*Real.pi)≤(1 : ℝ)/500 := by
  rw [show -2*Real.pi= -(2*Real.pi) by ring,Real.exp_neg]
  have h : (500 : ℝ)≤Real.exp (2*Real.pi) := by linarith [exp_two_pi_gt_fivehundredthirty]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<500) h

private theorem reciprocal_exp_sub {x : ℝ} (hx : 0<x) :
    1/(Real.exp x-1)=Real.exp (-x)/(1-Real.exp (-x)) := by
  have he : Real.exp x≠0 := (Real.exp_pos _).ne'
  have hd : Real.exp x-1≠0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)).ne'
  rw [Real.exp_neg]
  field_simp <;> ring

/-- Any retained Bose moment is bounded by its full geometric moment. -/
theorem bose_finite_moment_bound (p r : ℕ) {c : ℝ} (hc : 0<c) :
    (∑ j∈Finset.Ico 1 r, (j : ℝ)^p/(Real.exp (c*j)-1))≤
      geometricMoment p (Real.exp (-c))/(1-Real.exp (-c)) := by
  let q := Real.exp (-c)
  have hq0 : 0<q := Real.exp_pos _
  have hq1 : q<1 := by rw [Real.exp_lt_one_iff]; linarith
  have hsum := (geometricMoment_summable p (show |q|<1 by rwa [abs_of_pos hq0])).hasSum
  have hfinite : (∑ j∈Finset.Ico 1 r, (j : ℝ)^p*q^j)≤geometricMoment p q :=
    sum_le_hasSum (Finset.Ico 1 r) (fun j _ => by positivity) hsum
  have hpoint (j : ℕ) (hj : j∈Finset.Ico 1 r) :
      (j : ℝ)^p/(Real.exp (c*j)-1)≤((j : ℝ)^p*q^j)/(1-q) := by
    have hj0 : 0<j := (Finset.mem_Ico.mp hj).1
    have hjR : (0 : ℝ)<j := by exact_mod_cast hj0
    have he : Real.exp (-(c*j))=q^j := by
      dsimp [q]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hpow : q^j≤q := pow_le_of_le_one hq0.le hq1.le (by omega)
    have hrep : (j : ℝ)^p/(Real.exp (c*j)-1)=(j : ℝ)^p*q^j/(1-q^j) := by
      rw [div_eq_mul_one_div,reciprocal_exp_sub (mul_pos hc hjR),he]
      ring
    rw [hrep]
    exact div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  calc
    _≤∑ j∈Finset.Ico 1 r, ((j : ℝ)^p*q^j)/(1-q) := Finset.sum_le_sum hpoint
    _=(∑ j∈Finset.Ico 1 r, (j : ℝ)^p*q^j)/(1-q) := by rw [Finset.sum_div]
    _≤_ := div_le_div_of_nonneg_right hfinite (by linarith)

theorem fifth_bose_bound (r : ℕ) :
    (∑ j∈Finset.Ico 1 r, (j : ℝ)^5/(Real.exp (2*Real.pi*j)-1))≤
      moment5 (1/500)/(1-1/500) := by
  let q := Real.exp (-2*Real.pi)
  have hq0 : 0<q := Real.exp_pos _
  have hq1 : q<1 := by rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  have hq : q≤1/500 := q_pi_le
  have h := bose_finite_moment_bound 5 r (show 0<2*Real.pi by positivity)
  have he : Real.exp (-(2*Real.pi))=q := by dsimp [q]; congr 1; ring
  rw [he] at h
  rw [geometricMoment_five (show |q|<1 by rwa [abs_of_pos hq0])] at h
  refine h.trans ?_
  unfold moment5
  gcongr

/-- The chord lower bound, scaled to the actual rectangle exponent. -/
theorem scaled_gamma_chord {r j : ℝ} (hr : 0<r) (hj : 0≤j) (hjr : j≤r) :
    4*Concrete.alpha*j≤2*r*gamma (Real.pi*j/r) := by
  have hθ : Real.pi*j/r∈Set.Icc 0 Real.pi :=
    ⟨by positivity,(div_le_iff₀ hr).mpr (mul_le_mul_of_nonneg_left hjr Real.pi_pos.le)⟩
  have h := mul_le_mul_of_nonneg_left (gamma_chord_lower hθ) (show 0≤2*r by positivity)
  convert h using 1 <;> field_simp [hr.ne',Real.pi_ne_zero] <;> ring

theorem mode_exponent_ge_two {r : ℕ} (hr : 0<r) {j : ℕ} (hj : j∈Finset.Ico 1 r) :
    2≤2*(r : ℝ)*gamma (Real.pi*j/r) := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hj1 : (1 : ℝ)≤j := by exact_mod_cast (Finset.mem_Ico.mp hj).1
  have hjr : (j : ℝ)≤r := by exact_mod_cast (Finset.mem_Ico.mp hj).2.le
  have h := scaled_gamma_chord hrR (by positivity) hjr
  have hm := mul_le_mul_of_nonneg_left hj1 (show 0≤4*Concrete.alpha by have := Concrete.alpha_pos; positivity)
  linarith [alpha_gt_half]

theorem exponential_curvature_bound {c D : ℝ} (hc : 0<c) (hD : 1<D) (hDc : D≤Real.exp c) :
    Real.exp (-c)/(1-Real.exp (-c))^2≤D/(D-1)^2 := by
  have hD0 : 0<D := by linarith
  have hq : Real.exp (-c)≤1/D := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le hD0 hDc
  have hq1 : Real.exp (-c)<1 := by rw [Real.exp_lt_one_iff]; linarith
  have hi : 1/D<1 := (div_lt_one hD0).mpr hD
  calc
    _≤(1/D)/(1-1/D)^2 := by gcongr
    _=D/(D-1)^2 := by field_simp [hD0.ne',(sub_pos.mpr hD).ne'] <;> ring

/-- Every mode past the explicit low-mode block has a geometric majorant. -/
theorem curvature_mode_tail {r : ℕ} (hr : 0<r) {j : ℕ} (hj : j∈Finset.Ico 1 r) :
    Real.exp (-2*(r : ℝ)*gamma (Real.pi*j/r))/(1-Real.exp (-2*(r : ℝ)*gamma (Real.pi*j/r)))^2≤
      (1/33 : ℝ)^j/(1-1/33)^2 := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hjr : (j : ℝ)≤r := by exact_mod_cast (Finset.mem_Ico.mp hj).2.le
  have hchord := scaled_gamma_chord hrR (by positivity) hjr
  have he : Real.exp (-4*Concrete.alpha*j)=Concrete.q^j := by
    rw [Concrete.q,← Real.exp_nat_mul]
    congr 1
    ring
  have hq : Real.exp (-2*(r : ℝ)*gamma (Real.pi*j/r))≤(1/33 : ℝ)^j := by
    calc
      _≤Real.exp (-4*Concrete.alpha*j) := Real.exp_le_exp.mpr (by linarith)
      _=Concrete.q^j := he
      _≤_ := pow_le_pow_left₀ Concrete.q_pos.le q_alpha_le j
  have hj0 : 0<j := (Finset.mem_Ico.mp hj).1
  have hsmall : (1/33 : ℝ)^j≤1/33 := pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have hden : 1-1/33≤1-Real.exp (-2*(r : ℝ)*gamma (Real.pi*j/r)) := by linarith
  calc
    _≤(1/33 : ℝ)^j/(1-Real.exp (-2*(r : ℝ)*gamma (Real.pi*j/r)))^2 :=
      div_le_div_of_nonneg_right hq (sq_nonneg _)
    _≤_ := div_le_div_of_nonneg_left (by positivity) (by norm_num)
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤1-1/33) hden 2)

/-- A fixed linear mode has a simple geometric bound, also usable on tails. -/
theorem linear_bose_term_le (p : ℕ) {j : ℕ} (hj : 0<j) :
    (j : ℝ)^p/(Real.exp (2*Real.pi*j)-1)≤(j : ℝ)^p*(1/500)^j/(1-1/500) := by
  let q := Real.exp (-2*Real.pi)
  have hq0 : 0<q := Real.exp_pos _
  have hq : q≤1/500 := q_pi_le
  have hq1 : q<1 := by linarith
  have hjR : (0 : ℝ)<j := by exact_mod_cast hj
  have he : Real.exp (-(2*Real.pi*j))=q^j := by
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsmall : q^j≤q := pow_le_of_le_one hq0.le hq1.le (by omega)
  have hpow : q^j≤(1/500 : ℝ)^j := pow_le_pow_left₀ hq0.le hq j
  calc
    _=(j : ℝ)^p*q^j/(1-q^j) := by
      rw [div_eq_mul_one_div,reciprocal_exp_sub (by positivity : 0<2*Real.pi*j),he]
      ring
    _≤(j : ℝ)^p*(1/500)^j/(1-q^j) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (pow_nonneg (Nat.cast_nonneg j) p)) (by linarith)
    _≤_ := div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)

def baseExponent (r j : ℕ) : ℝ := 2*(r : ℝ)*gamma (Real.pi*j/r)
def curvatureMode (r j : ℕ) : ℝ := Real.exp (-baseExponent r j)/(1-Real.exp (-baseExponent r j))^2

def lowSixth (D1 D2 : ℝ) : ℝ :=
  D1/(D1-1)^2+2^6*D2/(D2-1)^2+3^6*550000/(550000-1)^2+4^6*22000000/(22000000-1)^2

def highSixth : ℝ :=
  (moment6 (1/33)-((1/33)+2^6*(1/33)^2+3^6*(1/33)^3+4^6*(1/33)^4))/(1-1/33)^2

def curvatureMajorant (D1 D2 : ℝ) (j : ℕ) : ℝ :=
  if j=1 then D1/(D1-1)^2 else if j=2 then 2^6*D2/(D2-1)^2 else
  if j=3 then 3^6*550000/(550000-1)^2 else if j=4 then 4^6*22000000/(22000000-1)^2 else
  (j : ℝ)^6*(1/33)^j/(1-1/33)^2

private theorem curvatureMajorant_nonneg {D1 D2 : ℝ} (h1 : 1<D1) (h2 : 1<D2) (j : ℕ) :
    0≤curvatureMajorant D1 D2 j := by
  have h10 : 0<D1 := by linarith
  have h20 : 0<D2 := by linarith
  unfold curvatureMajorant
  split_ifs <;> positivity

theorem curvatureMajorant_hasSum (D1 D2 : ℝ) :
    HasSum (curvatureMajorant D1 D2) (lowSixth D1 D2+highSixth) := by
  have hg := (geometricMoment_summable 6 (q := (1 : ℝ)/33) (by norm_num)).hasSum
  rw [← geometricMoment,geometricMoment_six (by norm_num : |(1 : ℝ)/33|<1)] at hg
  have h := ((((hg.div_const ((1-1/33)^2)).add
    (hasSum_ite_eq (1 : ℕ) (D1/(D1-1)^2-(1/33)/(1-1/33)^2))).add
    (hasSum_ite_eq (2 : ℕ) (2^6*D2/(D2-1)^2-2^6*(1/33)^2/(1-1/33)^2))).add
    (hasSum_ite_eq (3 : ℕ) (3^6*550000/(550000-1)^2-3^6*(1/33)^3/(1-1/33)^2))).add
    (hasSum_ite_eq (4 : ℕ) (4^6*22000000/(22000000-1)^2-4^6*(1/33)^4/(1-1/33)^2))
  convert h using 1
  · funext j
    by_cases h1 : j=1
    · subst j
      norm_num [curvatureMajorant] <;> ring
    by_cases h2 : j=2
    · subst j
      norm_num [curvatureMajorant] <;> ring
    by_cases h3 : j=3
    · subst j
      norm_num [curvatureMajorant] <;> ring
    by_cases h4 : j=4
    · subst j
      norm_num [curvatureMajorant] <;> ring
    simp [curvatureMajorant,h1,h2,h3,h4]
  · unfold lowSixth highSixth
    ring

private theorem exp_mode_transfer {m r j : ℕ} {D : ℝ} (hm : 0<m) (hmr : m≤r)
    (hj : 0<j) (hjm : j≤m) (hD : D<Real.exp (baseExponent m j)) :
    D<Real.exp (baseExponent r j) := by
  exact exp_mode_lower_transfer (m := (m : ℝ)) (r := (r : ℝ)) (s := (r : ℝ)) (j := (j : ℝ))
    (by exact_mod_cast hm) (by exact_mod_cast hmr) le_rfl
    (by exact_mod_cast hj) (by exact_mod_cast hjm) hD

private theorem exponent_four_one : baseExponent 4 1=8*gamma (Real.pi/4) := by
  norm_num [baseExponent]
private theorem exponent_four_two : baseExponent 4 2=8*gamma (Real.pi/2) := by
  simp only [baseExponent,Nat.cast_ofNat]
  rw [show Real.pi*2/4=Real.pi/2 by ring]
  norm_num
private theorem exponent_four_three : baseExponent 4 3=8*gamma (3*Real.pi/4) := by
  norm_num [baseExponent] <;> congr 2 <;> ring
private theorem exponent_five_four : baseExponent 5 4=10*gamma (4*Real.pi/5) := by
  norm_num [baseExponent] <;> congr 2 <;> ring
private theorem exponent_three_one : baseExponent 3 1=6*gamma (Real.pi/3) := by
  norm_num [baseExponent]
private theorem exponent_three_two : baseExponent 3 2=6*gamma (2*Real.pi/3) := by
  norm_num [baseExponent] <;> congr 2 <;> ring

/-- The finite curvature sum, with its explicit four-mode block and geometric tail. -/
private theorem curvature_sum_of_modes {r : ℕ} (hr : 0<r) {D1 D2 : ℝ} (hD1 : 1<D1) (hD2 : 1<D2)
    (h1 : 1<r → D1<Real.exp (baseExponent r 1))
    (h2 : 2<r → D2<Real.exp (baseExponent r 2))
    (h3 : 3<r → (550000 : ℝ)<Real.exp (baseExponent r 3))
    (h4 : 4<r → (22000000 : ℝ)<Real.exp (baseExponent r 4)) :
    (∑ j∈Finset.Ico 1 r, (j : ℝ)^6*curvatureMode r j)≤lowSixth D1 D2+highSixth := by
  have hp (j : ℕ) (hj : j∈Finset.Ico 1 r) :
      (j : ℝ)^6*curvatureMode r j≤curvatureMajorant D1 D2 j := by
    have hc : 0<baseExponent r j := by
      have h := mode_exponent_ge_two hr hj
      change 2≤baseExponent r j at h
      linarith
    by_cases hj1 : j=1
    · subst j
      have h := exponential_curvature_bound hc hD1 (h1 (Finset.mem_Ico.mp hj).2).le
      simpa [curvatureMode,curvatureMajorant] using h
    by_cases hj2 : j=2
    · subst j
      have h := exponential_curvature_bound hc hD2 (h2 (Finset.mem_Ico.mp hj).2).le
      have hh := mul_le_mul_of_nonneg_left h (show (0 : ℝ)≤2^6 by norm_num)
      simpa [curvatureMode,curvatureMajorant,mul_div_assoc] using hh
    by_cases hj3 : j=3
    · subst j
      have h := exponential_curvature_bound hc (by norm_num : (1 : ℝ)<550000)
        (h3 (Finset.mem_Ico.mp hj).2).le
      have hh := mul_le_mul_of_nonneg_left h (show (0 : ℝ)≤3^6 by norm_num)
      simpa [curvatureMode,curvatureMajorant,mul_div_assoc] using hh
    by_cases hj4 : j=4
    · subst j
      have h := exponential_curvature_bound hc (by norm_num : (1 : ℝ)<22000000)
        (h4 (Finset.mem_Ico.mp hj).2).le
      have hh := mul_le_mul_of_nonneg_left h (show (0 : ℝ)≤4^6 by norm_num)
      simpa [curvatureMode,curvatureMajorant,mul_div_assoc] using hh
    have h := mul_le_mul_of_nonneg_left (curvature_mode_tail hr hj) (show 0≤(j : ℝ)^6 by positivity)
    simpa only [curvatureMode,baseExponent,neg_mul,curvatureMajorant,if_neg hj1,if_neg hj2,
      if_neg hj3,if_neg hj4,mul_div_assoc] using h
  exact (Finset.sum_le_sum hp).trans (sum_le_hasSum (Finset.Ico 1 r)
    (fun j _ => curvatureMajorant_nonneg hD1 hD2 j) (curvatureMajorant_hasSum D1 D2))

theorem curvature_sum_four {r : ℕ} (hr : 4≤r) :
    (∑ j∈Finset.Ico 1 r, (j : ℝ)^6*curvatureMode r j)≤lowSixth 396 37600+highSixth := by
  apply curvature_sum_of_modes (by omega) (by norm_num) (by norm_num)
  · intro _
    apply exp_mode_transfer (m := 4) (by omega) hr (by omega) (by omega)
    rw [exponent_four_one]
    exact first_mode_four
  · intro _
    apply exp_mode_transfer (m := 4) (by omega) hr (by omega) (by omega)
    rw [exponent_four_two]
    exact second_mode_four
  · intro _
    apply exp_mode_transfer (m := 4) (by omega) hr (by omega) (by omega)
    rw [exponent_four_three]
    exact third_mode_four
  · intro hj
    apply exp_mode_transfer (m := 5) (by omega) (by omega) (by omega) (by omega)
    rw [exponent_five_four]
    exact fourth_mode_five

theorem curvature_sum_three {r : ℕ} (hr : 3≤r) :
    (∑ j∈Finset.Ico 1 r, (j : ℝ)^6*curvatureMode r j)≤lowSixth 321 12000+highSixth := by
  apply curvature_sum_of_modes (by omega) (by norm_num) (by norm_num)
  · intro _
    apply exp_mode_transfer (m := 3) (by omega) hr (by omega) (by omega)
    rw [exponent_three_one]
    exact first_mode_three
  · intro _
    apply exp_mode_transfer (m := 3) (by omega) hr (by omega) (by omega)
    rw [exponent_three_two]
    exact second_mode_three
  · intro hj
    apply exp_mode_transfer (m := 4) (by omega) (by omega) (by omega) (by omega)
    rw [exponent_four_three]
    exact third_mode_four
  · intro hj
    apply exp_mode_transfer (m := 5) (by omega) (by omega) (by omega) (by omega)
    rw [exponent_five_four]
    exact fourth_mode_five

end
end SpanningTreeIsoperimetry.RectangleModeSums
