import SpanningTreeIsoperimetry.SmallFamilyDefinitions
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! A common derivative comparison for every weighted inverse-fourth
correction in the small noncanonical families. -/
namespace SpanningTreeIsoperimetry.SmallFamilyMonotonicity
open Set AspectCost
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


private theorem monoOn_Ici {f : ℝ → ℝ} {a : ℝ}
    (h : ∀ x∈Ici a, ∃ d, HasDerivAt f d x ∧ 0≤d) : MonotoneOn f (Ici a) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici a)
  · intro x hx
    obtain ⟨d,hd,hp⟩ := h x hx
    exact hd.continuousAt.continuousWithinAt
  · intro x hx
    obtain ⟨d,hd,hp⟩ := h x (interior_subset hx)
    exact hd.differentiableAt.differentiableWithinAt
  · intro x hx
    obtain ⟨d,hd,hp⟩ := h x (interior_subset hx)
    rwa [hd.deriv]

private theorem cube_div_monotone {h : ℝ} (hh : 0<h) :
    MonotoneOn (fun r : ℝ => r^3/(r-h)) (Ici (3*h)) := by
  apply monoOn_Ici
  intro x hx
  have hx' : 3*h≤x := hx
  have hden : 0<x-h := by linarith
  have hx0 : 0<x := by linarith
  have hd : HasDerivAt (fun r : ℝ => r^3/(r-h)) (x^2*(2*x-3*h)/(x-h)^2) x := by
    convert ((hasDerivAt_id x).pow 3).div ((hasDerivAt_id x).sub_const h) hden.ne' using 1 <;>
      (try funext y) <;> dsimp [Pi.div_apply,id_eq] <;> field_simp [hden.ne'] <;> ring
  refine ⟨_,hd,?_⟩
  have hp : 0≤2*x-3*h := by linarith
  positivity

private theorem cube_div_sq_monotone {h : ℝ} (hh : 0<h) :
    MonotoneOn (fun r : ℝ => r^3/(r-h)^2) (Ici (3*h)) := by
  apply monoOn_Ici
  intro x hx
  have hx' : 3*h≤x := hx
  have hden : 0<x-h := by linarith
  have hd : HasDerivAt (fun r : ℝ => r^3/(r-h)^2) (x^2*(x-3*h)/(x-h)^3) x := by
    convert ((hasDerivAt_id x).pow 3).div (((hasDerivAt_id x).sub_const h).pow 2)
      (pow_ne_zero 2 hden.ne') using 1 <;>
      (try funext y) <;> dsimp [Pi.div_apply,Pi.pow_apply,id_eq] <;> field_simp [hden.ne'] <;> ring
  refine ⟨_,hd,?_⟩
  have hp : 0≤x-3*h := by linarith
  positivity

/-- Multiplying the negative aspect derivative by r^5 makes it monotone
throughout r≥3h, uniformly for every nonnegative initial hull gap. -/
theorem normalizedSlope_monotone {a h : ℝ} (ha : 0≤a) (hh : 0<h) :
    MonotoneOn (normalizedSlope a h) (Ici (3*h)) := by
  intro x hx y hy hxy
  have hx' : 3*h≤x := hx
  have hy' : 3*h≤y := hy
  have hx0 : 0<x := by linarith
  have hy0 : 0<y := by linarith
  have hxden : 0<x-h := by linarith
  have hyden : 0<y-h := by linarith
  have hq1 := cube_div_monotone hh hx hy hxy
  have hq2 := cube_div_sq_monotone hh hx hy hxy
  have hp := pow_le_pow_left₀ hx0.le hxy 3
  have hL : 2*x*(a+h)-a*h≤2*y*(a+h)-a*h := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (show 0≤a+h by linarith)]
  have hL0 : 0≤2*x*(a+h)-a*h := by
    have hm := mul_nonneg (sub_nonneg.mpr hx') (show 0≤a+h by linarith)
    nlinarith [mul_nonneg ha hh.le,sq_nonneg h]
  have ht1 := mul_le_mul_of_nonneg_left (mul_le_mul hq2 hL hL0 (by positivity : 0≤y^3/(y-h)^2))
    (show 0≤h/4 by positivity)
  have ht2 := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ)≤2))
    (mul_le_mul_of_nonneg_left hq1 (show 0≤4*h+2*a by positivity)))
    (mul_le_mul_of_nonneg_left hq2 (show 0≤2*h^2+a*h by positivity))
  have hπ : 0≤h*(Real.pi-3)/12 := by have hp := Real.pi_gt_three; positivity
  exact add_le_add ht1 (mul_le_mul_of_nonneg_left ht2 hπ)

set_option maxHeartbeats 1000000 in
theorem aspectStep_hasDeriv {a h r : ℝ} (ha : 0≤a) (hh : 0<h) (hr : h<r) :
    HasDerivAt (aspectStep a h) (-(normalizedSlope a h r)/r^5) r := by
  have hr0 : 0<r := lt_trans hh hr
  have hden : 0<r-h := by linarith
  have hnum : 0<a+2*r := by positivity
  have hnum' : 0<2*r+a := by positivity
  have harg : 0<a/r+2 := by positivity
  have harg' : 0<(a+2*h)/(r-h)+2 := by positivity
  have hd := hasDerivAt_shifted_difference (A := a+2*h) (B := a) (a := -h) (b := 0)
    (x := r) ha (by linarith) (by linarith) (by linarith)
  simp only [add_zero, ←sub_eq_add_neg] at hd
  convert hd using 1
  · funext x
    simp only [aspectStep,add_zero,sub_eq_add_neg]
  · unfold normalizedSlope Dprime
    field_simp [hr0.ne',hden.ne',hnum.ne',hnum'.ne',harg.ne',harg'.ne']
    <;> ring

variable {ι : Type*}

theorem normalizedWeight_antitone (I : Finset ι) (c shift : ι → ℝ)
    (hc : ∀ i∈I, 0≤c i) (hs : ∀ i∈I, 0≤shift i) {x y : ℝ}
    (hx : ∀ i∈I, shift i<x) (hxy : x≤y) : normalizedWeight I c shift y≤normalizedWeight I c shift x := by
  unfold normalizedWeight
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i hi
  have hxden : 0<x-shift i := by linarith [hx i hi]
  have hyden : 0<y-shift i := by linarith [hx i hi]
  have hx0 : 0<x := lt_of_le_of_lt (hs i hi) (hx i hi)
  have hy0 : 0<y := hx0.trans_le hxy
  have hrat : y/(y-shift i)≤x/(x-shift i) := by
    rw [div_le_div_iff₀ hyden hxden]
    nlinarith only [mul_nonneg (hs i hi) (sub_nonneg.mpr hxy)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrat 5) (hc i hi)

theorem normalizedWeight_eq (I : Finset ι) (c shift : ι → ℝ) (r : ℝ) :
    normalizedWeight I c shift r=r^5*(4*∑ i∈I,c i/(r-shift i)^5) := by
  unfold normalizedWeight
  simp_rw [div_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem weightedLoss_hasDeriv (I : Finset ι) (c shift : ι → ℝ) {r : ℝ}
    (hr : ∀ i∈I, shift i<r) :
    HasDerivAt (weightedLoss I c shift) (-(4*∑ i∈I,c i/(r-shift i)^5)) r := by
  have hd (i : ι) (hi : i∈I) : HasDerivAt (fun x : ℝ => c i/(x-shift i)^4)
      (-4*c i/(r-shift i)^5) r := by
    have hn : r-shift i≠0 := by linarith [hr i hi]
    convert (hasDerivAt_const r (c i)).div (((hasDerivAt_id r).sub_const (shift i)).pow 4)
      (pow_ne_zero 4 hn) using 1 <;>
      (try funext x) <;> dsimp [Pi.div_apply,Pi.pow_apply,id_eq] <;> field_simp [hn] <;> ring
  have h := HasDerivAt.fun_sum hd
  convert h using 1
  · rfl
  · simp_rw [Finset.mul_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- A single finite endpoint inequality certifies the whole weighted
family. Concrete table rows discharge this arithmetic premise explicitly. -/
theorem corrected_aspect_antitone (I : Finset ι) (c shift : ι → ℝ)
    {a h r₀ : ℝ} (ha : 0≤a) (hh : 0<h) (hr : 3*h≤r₀)
    (hc : ∀ i∈I, 0≤c i) (hs : ∀ i∈I, 0≤shift i) (hpole : ∀ i∈I, shift i<r₀)
    (hend : normalizedWeight I c shift r₀≤normalizedSlope a h r₀) :
    AntitoneOn (fun r : ℝ => aspectStep a h r-weightedLoss I c shift r) (Ici r₀) := by
  have hdata (r : ℝ) (hrr : r₀≤r) : ∃ d, HasDerivAt
      (fun r : ℝ => aspectStep a h r-weightedLoss I c shift r) d r ∧ d≤0 := by
    have hrh : h<r := by linarith
    have hr0 : 0<r := by linarith
    have hweights := normalizedWeight_antitone I c shift hc hs hpole hrr
    have hslope := normalizedSlope_monotone ha hh hr (show 3*h≤r by linarith) hrr
    have hws := hweights.trans (hend.trans hslope)
    have hd := (aspectStep_hasDeriv ha hh hrh).sub (weightedLoss_hasDeriv I c shift
      (fun i hi => (hpole i hi).trans_le hrr))
    refine ⟨_,hd,?_⟩
    have he : -(normalizedSlope a h r)/r^5-(-(4*∑ i∈I,c i/(r-shift i)^5))=
        (normalizedWeight I c shift r-normalizedSlope a h r)/r^5 := by
      rw [normalizedWeight_eq]
      field_simp
      <;> ring
    rw [he]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hws) (pow_nonneg hr0.le _)
  apply antitoneOn_of_deriv_nonpos (convex_Ici r₀)
  · intro r hr
    obtain ⟨d,hd,hle⟩ := hdata r hr
    exact hd.continuousAt.continuousWithinAt
  · intro r hr
    obtain ⟨d,hd,hle⟩ := hdata r (interior_subset hr)
    exact hd.differentiableAt.differentiableWithinAt
  · intro r hr
    obtain ⟨d,hd,hle⟩ := hdata r (interior_subset hr)
    rwa [hd.deriv]

end
end SpanningTreeIsoperimetry.SmallFamilyMonotonicity
