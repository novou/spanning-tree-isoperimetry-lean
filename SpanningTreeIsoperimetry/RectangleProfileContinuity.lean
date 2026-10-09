import SpanningTreeIsoperimetry.RectangularRemainder
import Mathlib.Analysis.Normed.Group.Tannery

/-! Continuity of the actual first rectangular aspect profile, obtained by
dominating its logarithmic series on a positive local interval. -/
namespace SpanningTreeIsoperimetry.RectangleProfileContinuity
open RectangularRemainder Filter
open scoped Topology BigOperators
noncomputable section

def term (u : ℝ) (n : ℕ) : ℝ := Real.log (1-Real.exp (-2*Real.pi*u*((n : ℝ)+1)))

private theorem argument_pos {u : ℝ} (hu : 0<u) (n : ℕ) :
    0<1-Real.exp (-2*Real.pi*u*((n : ℝ)+1)) := by
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  have hp : 0<2*Real.pi*u*((n : ℝ)+1) := by positivity
  linarith

theorem term_nonpos {u : ℝ} (hu : 0<u) (n : ℕ) : term u n≤0 := by
  apply Real.log_nonpos (argument_pos hu n).le
  linarith [Real.exp_pos (-2*Real.pi*u*((n : ℝ)+1))]

theorem term_mono {u v : ℝ} (hu : 0<u) (huv : u≤v) (n : ℕ) : term u n≤term v n := by
  apply Real.log_le_log (argument_pos hu n)
  have hp : 0≤2*Real.pi*((n : ℝ)+1) := by positivity
  have hh : -2*Real.pi*v*((n : ℝ)+1)≤-2*Real.pi*u*((n : ℝ)+1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr huv) hp]
  have he := Real.exp_le_exp.mpr hh
  linarith

theorem continuousAt_term {u : ℝ} (hu : 0<u) (n : ℕ) :
    ContinuousAt (fun v => term v n) u := by
  unfold term
  exact (show ContinuousAt (fun v : ℝ => 1-Real.exp (-2*Real.pi*v*((n : ℝ)+1))) u
    from by fun_prop).log (argument_pos hu n).ne'

theorem norm_term_le {c v : ℝ} (hc : 0<c) (hcv : c≤v) (n : ℕ) :
    ‖term v n‖≤‖term c n‖ := by
  rw [Real.norm_eq_abs,abs_of_nonpos (term_nonpos (hc.trans_le hcv) n),
    Real.norm_eq_abs,abs_of_nonpos (term_nonpos hc n)]
  linarith [term_mono hc hcv n]

theorem linearResidual_tendsto {α : Type*} {l : Filter α} {f : α → ℝ} {c u : ℝ}
    (hc : 0<c) (hu : 0<u) (hf : Tendsto f l (𝓝 u)) (hlower : ∀ᶠ x in l, c≤f x) :
    Tendsto (fun x => linearResidual (f x)) l (𝓝 (linearResidual u)) := by
  have hs : Summable (fun n => ‖term c n‖) := (linearResidual_summable hc).norm
  have hh := tendsto_tsum_of_dominated_convergence hs
    (f := fun x n => term (f x) n) (g := fun n => term u n)
    (fun n => (continuousAt_term hu n).tendsto.comp hf)
    (hlower.mono (fun x hx n => norm_term_le hc hx n))
  simpa only [linearResidual,term] using hh

theorem continuousAt_linearResidual {u : ℝ} (hu : 0<u) : ContinuousAt linearResidual u := by
  exact linearResidual_tendsto (half_pos hu) hu tendsto_id
    (eventually_ge_nhds (show u/2<u by linarith))

theorem continuousAt_B {u : ℝ} (hu : 0<u) : ContinuousAt B u := by
  change ContinuousAt (fun v : ℝ => (5/4)*Real.log 2-Real.pi*v/12+linearResidual v) u
  exact (continuousAt_const.sub ((continuousAt_id.const_mul Real.pi).div_const 12)).add
    (continuousAt_linearResidual hu)

theorem continuousAt_J {u : ℝ} (hu : 0<u) : ContinuousAt J u := by
  change ContinuousAt (fun v : ℝ => B v+(1/4)*Real.log v) u
  exact (continuousAt_B hu).add ((continuousAt_id.log hu.ne').const_mul (1/4))

theorem continuousAt_K {u : ℝ} (hu : 0<u) : ContinuousAt K u := by
  change ContinuousAt (fun v : ℝ => B v+(1/2)*Real.log (1+v)) u
  exact (continuousAt_B hu).add (((continuousAt_id.const_add 1).log
    (by change 1+u≠0; linarith)).const_mul (1/2))

theorem F_eq_J {r s : ℕ} (hr : 0<r) (hs : 0<s) :
    F r s= -(1/4)*Real.log ((r : ℝ)*s)+J ((s : ℝ)/r)+error r s := by
  have hr0 : (r : ℝ)≠0 := by exact_mod_cast hr.ne'
  have hs0 : (s : ℝ)≠0 := by exact_mod_cast hs.ne'
  unfold J error
  rw [Real.log_mul hr0 hs0,Real.log_div hs0 hr0]
  ring

theorem F_eq_K {r s : ℕ} (hr : 0<r) (hs : 0<s) :
    F r s= -(1/2)*Real.log ((r : ℝ)+s)+K ((s : ℝ)/r)+error r s := by
  have hr0 : (r : ℝ)≠0 := by exact_mod_cast hr.ne'
  have hsR : (0 : ℝ)<s := by exact_mod_cast hs
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hsum : (r : ℝ)+s≠0 := by positivity
  unfold K error
  rw [show 1+(s : ℝ)/r=((r : ℝ)+s)/r by field_simp [hr0] <;> ring,
    Real.log_div hsum hr0]
  ring

end
end SpanningTreeIsoperimetry.RectangleProfileContinuity
