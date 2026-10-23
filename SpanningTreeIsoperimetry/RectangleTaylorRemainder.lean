module

public import SpanningTreeIsoperimetry.RectangleModeSums
public import SpanningTreeIsoperimetry.SharpRectangleExpansion

@[expose] public section

set_option backward.privateInPublic true

/-! Actual retained Taylor errors, summed with the sharp mode bounds. -/
namespace SpanningTreeIsoperimetry.RectangleTaylorRemainder

open SquareMaximality.Rectangle RectangularRemainder RectangleResidualBounds
open LogResidualTaylor RectangleModeSums SharpRectangleExpansion CoupledRectangleError
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

private theorem fifth_node_le {r s : ℕ} (hr : 0<r) (hrs : r≤s) {j : ℕ} (hj : j∈Finset.Ico 1 r) :
    (s : ℝ)*(Real.pi*j/r)^5/(48*(Real.exp (2*s*(Real.pi*j/r))-1))≤
      (Real.pi^5/(48*(r : ℝ)^4))*((j : ℝ)^5/(Real.exp (2*Real.pi*j)-1)) := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hsR : (r : ℝ)≤s := by exact_mod_cast hrs
  have hj0 : 0<j := (Finset.mem_Ico.mp hj).1
  have hjR : (0 : ℝ)<j := by exact_mod_cast hj0
  let u := (s : ℝ)/r
  let c := 2*Real.pi*j
  have hu : 1≤u := (one_le_div hrR).mpr hsR
  have hu0 : 0<u := by linarith
  have hc : 0<c := by dsimp [c]; positivity
  have h := scaled_exp_reciprocal_antitone hc (by change (0 : ℝ)<1; norm_num) hu0 hu
  simp only [mul_one] at h
  have harg : 2*(s : ℝ)*(Real.pi*j/r)=c*u := by dsimp [c,u]; ring
  have hd : 0<Real.exp (c*u)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hc hu0))
  calc
    _=(Real.pi^5/(48*(r : ℝ)^4)*(j : ℝ)^5)*(u/(Real.exp (c*u)-1)) := by
      rw [harg]
      dsimp [u]
      field_simp [hrR.ne',hd.ne'] <;> ring
    _≤(Real.pi^5/(48*(r : ℝ)^4)*(j : ℝ)^5)*(1/(Real.exp c-1)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _=_ := by dsimp [c]; ring

private theorem sixth_node_le {r s : ℕ} (hr : 0<r) (hrs : r≤s) {j : ℕ} (hj : j∈Finset.Ico 1 r) :
    ((s : ℝ)^2*(Real.pi*j/r)^6/72)*Real.exp (-2*s*gamma (Real.pi*j/r))/
      (1-Real.exp (-2*s*gamma (Real.pi*j/r)))^2≤
      (Real.pi^6/(72*(r : ℝ)^4))*((j : ℝ)^6*curvatureMode r j) := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hsR : (r : ℝ)≤s := by exact_mod_cast hrs
  let u := (s : ℝ)/r
  let c := baseExponent r j
  have hu : 1≤u := (one_le_div hrR).mpr hsR
  have hu0 : 0<u := by linarith
  have hc : 2≤c := mode_exponent_ge_two hr hj
  have hc0 : 0<c := by linarith
  have h := scaled_curvature_antitone hc (by simp : (1 : ℝ)∈Set.Ici 1) hu hu
  simp only [one_pow,mul_one,one_mul] at h
  have harg : -2*(s : ℝ)*gamma (Real.pi*j/r)= -c*u := by
    dsimp [c,baseExponent,u]
    field_simp [hrR.ne'] <;> ring
  have hd : 0<1-Real.exp (-c*u) := by
    rw [sub_pos,Real.exp_lt_one_iff]
    nlinarith
  calc
    _=(Real.pi^6/(72*(r : ℝ)^4)*(j : ℝ)^6)*
        (u^2*Real.exp (-c*u)/(1-Real.exp (-c*u))^2) := by
      rw [harg]
      dsimp [u]
      field_simp [hrR.ne',hd.ne'] <;> ring
    _≤(Real.pi^6/(72*(r : ℝ)^4)*(j : ℝ)^6)*
        (Real.exp (-c)/(1-Real.exp (-c))^2) := mul_le_mul_of_nonneg_left h (by positivity)
    _=_ := by dsimp [c,curvatureMode]; ring

private theorem retained_sum_le {r s : ℕ} (hr : 0<r) (hrs : r≤s) {M : ℝ}
    (hM : (∑ j∈Finset.Ico 1 r, (j : ℝ)^6*curvatureMode r j)≤M) :
    |retainedCorrection r s|≤
      (((22/7 : ℝ)^5)*moment5 (1/500)/(48*(1-1/500))+(22/7)^6/72*M)/(r : ℝ)^4 := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hs : 0<s := hr.trans_le hrs
  have hsR : (0 : ℝ)<s := by exact_mod_cast hs
  have hM0 : 0≤M := (Finset.sum_nonneg (fun j _ => by unfold curvatureMode; positivity)).trans hM
  have hm50 : 0≤moment5 (1/500)/(1-1/500) := by norm_num [moment5]
  have hpi : Real.pi≤(22 : ℝ)/7 := by linarith [Real.pi_lt_d4]
  have hpoint (j : ℕ) (hj : j∈Finset.Ico 1 r) :
      |logTerm s (gamma (Real.pi*j/r))-logTerm s (Real.pi*j/r)+
        (s : ℝ)*(Real.pi*j/r)^3/(6*(Real.exp (2*s*(Real.pi*j/r))-1))|≤
        (Real.pi^5/(48*(r : ℝ)^4))*((j : ℝ)^5/(Real.exp (2*Real.pi*j)-1))+
        (Real.pi^6/(72*(r : ℝ)^4))*((j : ℝ)^6*curvatureMode r j) := by
    have hj0 : 0<j := (Finset.mem_Ico.mp hj).1
    have hjR : (0 : ℝ)<j := by exact_mod_cast hj0
    have hjr : (j : ℝ)≤r := by exact_mod_cast (Finset.mem_Ico.mp hj).2.le
    have hθ : Real.pi*j/r∈Set.Ioc 0 Real.pi :=
      ⟨by positivity,(div_le_iff₀ hrR).mpr (mul_le_mul_of_nonneg_left hjr Real.pi_pos.le)⟩
    exact (gamma_log_next_error hsR hθ).trans (add_le_add (fifth_node_le hr hrs hj) (sixth_node_le hr hrs hj))
  calc
    _≤∑ j∈Finset.Ico 1 r,
        |logTerm s (gamma (Real.pi*j/r))-logTerm s (Real.pi*j/r)+
          (s : ℝ)*(Real.pi*j/r)^3/(6*(Real.exp (2*s*(Real.pi*j/r))-1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _≤∑ j∈Finset.Ico 1 r,
        ((Real.pi^5/(48*(r : ℝ)^4))*((j : ℝ)^5/(Real.exp (2*Real.pi*j)-1))+
        (Real.pi^6/(72*(r : ℝ)^4))*((j : ℝ)^6*curvatureMode r j)) := Finset.sum_le_sum hpoint
    _=(Real.pi^5/(48*(r : ℝ)^4))*(∑ j∈Finset.Ico 1 r, (j : ℝ)^5/(Real.exp (2*Real.pi*j)-1))+
        (Real.pi^6/(72*(r : ℝ)^4))*(∑ j∈Finset.Ico 1 r, (j : ℝ)^6*curvatureMode r j) := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    _≤(Real.pi^5/(48*(r : ℝ)^4))*(moment5 (1/500)/(1-1/500))+
        (Real.pi^6/(72*(r : ℝ)^4))*M := by
      exact add_le_add (mul_le_mul_of_nonneg_left (fifth_bose_bound r) (by positivity))
        (mul_le_mul_of_nonneg_left hM (by positivity))
    _≤(((22/7 : ℝ)^5)/(48*(r : ℝ)^4))*(moment5 (1/500)/(1-1/500))+
        ((22/7)^6/(72*(r : ℝ)^4))*M := by gcongr
    _=_ := by field_simp [hrR.ne'] <;> ring

theorem retainedCorrection_four {r s : ℕ} (hr : 4≤r) (hrs : r≤s) :
    |retainedCorrection r s|≤
      (((22/7 : ℝ)^5)*moment5 (1/500)/(48*(1-1/500))+
        (22/7)^6/72*(lowSixth 396 37600+highSixth))/(r : ℝ)^4 :=
  retained_sum_le (by omega) hrs (curvature_sum_four hr)

theorem retainedCorrection_three {r s : ℕ} (hr : 3≤r) (hrs : r≤s) :
    |retainedCorrection r s|≤
      (((22/7 : ℝ)^5)*moment5 (1/500)/(48*(1-1/500))+
        (22/7)^6/72*(lowSixth 321 12000+highSixth))/(r : ℝ)^4 :=
  retained_sum_le (by omega) hrs (curvature_sum_three hr)

end
end SpanningTreeIsoperimetry.RectangleTaylorRemainder
