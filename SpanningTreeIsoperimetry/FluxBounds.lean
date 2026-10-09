import SpanningTreeIsoperimetry.FluxDefinition
import SpanningTreeIsoperimetry.RectangularRemainder
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The actual rational boundary-flux envelope B(r,s,k) used in the finite
strip comparison. These scalar bounds do not assume a Green-error estimate. -/
namespace SpanningTreeIsoperimetry.FluxBounds

open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

@[simp] theorem fluxBound_zero (r s : ℝ) : fluxBound r s 0 = 0 := by
  simp [fluxBound,cubic,quadratic]

theorem fluxBound_nonneg (r s : ℝ) {k : ℝ} (hk : 0≤k) : 0≤fluxBound r s k := by
  unfold fluxBound cubic quadratic
  positivity

private theorem recip_sq_antitone {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    1/b^2 ≤ 1/a^2 := by
  apply one_div_le_one_div_of_le (sq_pos_of_pos ha)
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (show 0≤a+b by linarith)]

/-- Increasing the short side decreases the displayed flux envelope. -/
theorem fluxBound_antitone_left {r R s k : ℝ} (hr : 2<r) (hrR : r≤R) (hk : 0≤k) :
    fluxBound R s k ≤ fluxBound r s k := by
  have h4 : 0<r^2-4 := by nlinarith
  have h1 : 0<r^2-1 := by nlinarith
  have hsquare : r^2≤R^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrR) (show 0≤R+r by linarith)]
  have hrec4 : 1/(R^2-4)^2≤1/(r^2-4)^2 := recip_sq_antitone (b := R^2-4) h4 (by linarith)
  have hrec1 : 1/(R^2-1)^2≤1/(r^2-1)^2 := recip_sq_antitone (b := R^2-1) h1 (by linarith)
  have hc : 0≤cubic k/3 := by unfold cubic; positivity
  have hq : 0≤quadratic k := by unfold quadratic; positivity
  have hmul4 := mul_le_mul_of_nonneg_left hrec4 hc
  have hmul1 := mul_le_mul_of_nonneg_left hrec1 hq
  unfold fluxBound
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith only [hmul4,hmul1]

/-- Increasing the long side decreases the displayed flux envelope. -/
theorem fluxBound_antitone_right {r s S k : ℝ} (hk : 0≤k) (hs : k+1<s) (hsS : s≤S) :
    fluxBound r S k ≤ fluxBound r s k := by
  have hs0 : 0<s := by linarith
  have hsk : 0<s^2-k^2 := by
    nlinarith [mul_pos (show 0<s-k by linarith) (show 0<s+k by linarith)]
  have hsk1 : 0<s^2-(k+1)^2 := by
    nlinarith [mul_pos (show 0<s-(k+1) by linarith) (show 0<s+(k+1) by linarith)]
  have hsquare : s^2≤S^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsS) (show 0≤S+s by linarith)]
  have hrec0 : 1/(S^2-k^2)^2≤1/(s^2-k^2)^2 := recip_sq_antitone (b := S^2-k^2) hsk (by linarith)
  have hrec1 : 1/(S^2-(k+1)^2)^2≤1/(s^2-(k+1)^2)^2 := recip_sq_antitone (b := S^2-(k+1)^2) hsk1 (by linarith)
  have hc : 0≤cubic k/3 := by unfold cubic; positivity
  have hq : 0≤quadratic k := by unfold quadratic; positivity
  have hmul0 := mul_le_mul_of_nonneg_left hrec0 hc
  have hmul1 := mul_le_mul_of_nonneg_left hrec1 hq
  unfold fluxBound
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith only [hmul0,hmul1]

/-- Increasing the strip length increases the envelope inside its domain. -/
theorem fluxBound_monotone_length {r s k l : ℝ} (hk : 0≤k) (hkl : k≤l) (hs : l+1<s) :
    fluxBound r s k ≤ fluxBound r s l := by
  have hl : 0≤l := hk.trans hkl
  have hs0 : 0<s := by linarith
  have hd : 0<s^2-l^2 := by
    nlinarith [mul_pos (show 0<s-l by linarith) (show 0<s+l by linarith)]
  have hd1 : 0<s^2-(l+1)^2 := by
    nlinarith [mul_pos (show 0<s-(l+1) by linarith) (show 0<s+(l+1) by linarith)]
  have hsq : k^2≤l^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hkl) (show 0≤l+k by linarith)]
  have hsq1 : (k+1)^2≤(l+1)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hkl) (show 0≤l+k+2 by linarith)]
  have hc : cubic k/3≤cubic l/3 := by unfold cubic; gcongr
  have hq : quadratic k≤quadratic l := by unfold quadratic; gcongr
  have hrec0 : 1/(s^2-k^2)^2≤1/(s^2-l^2)^2 := recip_sq_antitone (b := s^2-k^2) hd (by linarith)
  have hrec1 : 1/(s^2-(k+1)^2)^2≤1/(s^2-(l+1)^2)^2 := recip_sq_antitone (b := s^2-(k+1)^2) hd1 (by linarith)
  have hs0' := add_le_add (le_refl (1/(r^2-4)^2)) hrec0
  have hs1' := add_le_add (le_refl (1/(r^2-1)^2)) hrec1
  have hm0 := mul_le_mul hc hs0' (by positivity : 0≤1/(r^2-4)^2+1/(s^2-k^2)^2)
    (by unfold cubic; positivity : 0≤cubic l/3)
  have hm1 := mul_le_mul hq hs1' (by positivity : 0≤1/(r^2-1)^2+1/(s^2-(k+1)^2)^2)
    (by unfold quadratic; positivity : 0≤quadratic l)
  unfold fluxBound
  exact mul_le_mul_of_nonneg_left (add_le_add hm0 hm1) (by positivity)

/-- If the unused long-side distance dominates the short side, all four
terms are bounded by one short-side denominator. -/
theorem fluxBound_le_cubic {r s k : ℝ} (hr : 2<r) (hk : 0≤k) (hs : r+k≤s) :
    fluxBound r s k ≤ Real.pi^3*k*(k+1)*(k+2)/(45*(r^2-4)^2) := by
  have hs0 : 0≤s := by linarith
  have hsum : 0≤r+k := by linarith
  have hss : (r+k)^2≤s^2 := by
    nlinarith [mul_nonneg (show 0≤s-(r+k) by linarith) (show 0≤s+(r+k) by linarith)]
  have h4 : 0<r^2-4 := by nlinarith
  have hS0 : r^2-4≤s^2-k^2 := by nlinarith [mul_nonneg hk (by linarith : 0≤r)]
  have hS1 : r^2-4≤s^2-(k+1)^2 := by nlinarith [mul_nonneg hk (by linarith : 0≤r-1)]
  have hR1 : r^2-4≤r^2-1 := by linarith
  calc
    fluxBound r s k ≤ Real.pi^3/60 * ((cubic k/3) * (2/(r^2-4)^2) +
        quadratic k * (2/(r^2-4)^2)) := by
      unfold fluxBound
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by unfold cubic; positivity)
        have h := recip_sq_antitone h4 hS0
        simp only [div_eq_mul_inv,one_mul] at h ⊢
        linarith
      · apply mul_le_mul_of_nonneg_left _ (by unfold quadratic; positivity)
        have h := recip_sq_antitone h4 hS1
        have h' := recip_sq_antitone h4 hR1
        simp only [div_eq_mul_inv,one_mul] at h h' ⊢
        linarith
    _ = _ := by unfold cubic quadratic; simp only [div_eq_mul_inv,mul_inv_rev]; ring

theorem fluxBound_lt_fourth {r s k : ℝ} (hr : 2<r) (hk : 0≤k) (hs : r+k≤s) :
    fluxBound r s k < Real.pi^3/45 * ((k+1)^3/(r-2)^4) := by
  have hden : 0<(r^2-4)^2 := sq_pos_of_pos (by nlinarith)
  have hsmall : 0<(r-2)^4 := by positivity
  have hcmp : (r-2)^4≤(r^2-4)^2 := by
    have h1 : 0≤r-2 := by linarith
    have h2 : (r-2)^2≤r^2-4 := by nlinarith
    nlinarith [mul_nonneg (show 0≤r by linarith) (sq_nonneg (r-2))]
  have hnum : k*(k+1)*(k+2)<(k+1)^3 := by nlinarith
  have hnonneg : 0≤k*(k+1)*(k+2) := by positivity
  calc
    fluxBound r s k ≤ Real.pi^3/45 * (k*(k+1)*(k+2)/(r^2-4)^2) := by
      convert fluxBound_le_cubic hr hk hs using 1 <;>
        simp only [div_eq_mul_inv,mul_inv_rev] <;> ring
    _ < Real.pi^3/45 * ((k+1)^3/(r^2-4)^2) :=
      mul_lt_mul_of_pos_left ((div_lt_div_iff_of_pos_right hden).mpr hnum) (by positivity)
    _ ≤ _ := by gcongr

private theorem monoOn_Icc_of_deriv_data {f : ℝ → ℝ} {a b : ℝ}
    (h : ∀ x ∈ Set.Icc a b, ∃ d, HasDerivAt f d x ∧ 0≤d) :
    MonotoneOn f (Set.Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
  · intro x hx
    obtain ⟨d,hd,_⟩ := h x hx
    exact hd.continuousAt.continuousWithinAt
  · intro x hx
    obtain ⟨d,hd,_⟩ := h x (interior_subset hx)
    exact hd.differentiableAt.differentiableWithinAt
  · intro x hx
    obtain ⟨d,hd,hp⟩ := h x (interior_subset hx)
    rwa [hd.deriv]

private theorem hasDerivAt_cubic (x : ℝ) : HasDerivAt cubic (6*x^2+6*x+1) x := by
  have h := ((hasDerivAt_id x).mul ((hasDerivAt_id x).add_const 1)).mul
    (((hasDerivAt_id x).const_mul 2).add_const 1)
  convert h using 1 <;> (try funext y) <;> dsimp [cubic,Pi.mul_apply,id_eq] <;> ring

private theorem hasDerivAt_quadratic (x : ℝ) : HasDerivAt quadratic (2*x+1) x := by
  have h := (hasDerivAt_id x).mul ((hasDerivAt_id x).add_const 1)
  convert h using 1 <;> (try funext y) <;> dsimp [quadratic,Pi.mul_apply,id_eq] <;> ring

private theorem hasDerivAt_div_square {f g : ℝ → ℝ} {u v x : ℝ}
    (hf : HasDerivAt f u x) (hg : HasDerivAt g v x) (hne : g x≠0) :
    HasDerivAt (fun y => f y/(g y)^2) ((u*g x-2*v*f x)/(g x)^3) x := by
  convert hf.div (hg.pow 2) (pow_ne_zero 2 hne) using 1 <;>
    (try funext y) <;> simp only [Pi.pow_apply,Pi.div_apply] <;> field_simp [hne] <;> ring

def shortCubic (a x : ℝ) : ℝ := cubic x/((a+x)^2-4)^2
def shortQuadratic (a x : ℝ) : ℝ := quadratic x/((a+x)^2-1)^2
def longCubic (b x : ℝ) : ℝ := cubic x/((b+x)^2-x^2)^2
def longQuadratic (b x : ℝ) : ℝ := quadratic x/((b+x)^2-(x+1)^2)^2

private theorem shortDenom_pos {a x : ℝ} (ha : 5≤a) (hx : 0≤x) :
    0<(a+x)^2-4 := by nlinarith [sq_nonneg (a+x-2)]

private theorem shortCubic_num_pos {a x : ℝ} (ha : 5≤a) (hx : 0≤x) (hxa : x≤a-1) :
    0<(6*x^2+6*x+1)*((a+x)^2-4)-4*(a+x)*cubic x := by
  have hD := shortDenom_pos ha hx
  have hlin : 0<3*(a+x-2)-4*(x+1) := by linarith
  have hrest : 0<3*((a+x)^2-4)-4*(a+x)*(x+1) := by
    rw [show 3*((a+x)^2-4)-4*(a+x)*(x+1) =
      (3*(a+x-2)-4*(x+1))*(a+x+2)+8*(x+1) by ring]
    positivity
  have hp : 0<(x+1)*((6*x^2+6*x+1)*((a+x)^2-4)-4*(a+x)*cubic x) := by
    rw [show (x+1)*((6*x^2+6*x+1)*((a+x)^2-4)-4*(a+x)*cubic x) =
      ((a+x)^2-4)*(3*x^2+4*x+1)+cubic x*(3*((a+x)^2-4)-4*(a+x)*(x+1)) by
        unfold cubic; ring]
    have hc : 0≤cubic x := by unfold cubic; positivity
    positivity
  exact (mul_pos_iff_of_pos_left (by linarith : 0<x+1)).mp hp

theorem shortCubic_monotone {a : ℝ} (ha : 5≤a) :
    MonotoneOn (shortCubic a) (Set.Icc 0 (a-1)) := by
  apply monoOn_Icc_of_deriv_data
  intro x hx
  have hD := shortDenom_pos ha hx.1
  have hg := (((hasDerivAt_id x).const_add a).pow 2).sub_const 4
  have hf : HasDerivAt (shortCubic a)
      (((6*x^2+6*x+1)*((a+x)^2-4)-4*(a+x)*cubic x)/((a+x)^2-4)^3) x := by
    convert hasDerivAt_div_square (hasDerivAt_cubic x) hg hD.ne' using 1 <;>
      (try funext y) <;> dsimp [shortCubic,Pi.pow_apply,Pi.sub_apply,id_eq] <;> ring
  exact ⟨_,hf,(div_pos (shortCubic_num_pos ha hx.1 hx.2) (pow_pos hD 3)).le⟩

theorem shortQuadratic_monotone {a : ℝ} (ha : 5≤a) :
    MonotoneOn (shortQuadratic a) (Set.Icc 0 (a-1)) := by
  apply monoOn_Icc_of_deriv_data
  intro x hx
  have hD : 0<(a+x)^2-1 := by linarith [shortDenom_pos ha hx.1]
  have hg := (((hasDerivAt_id x).const_add a).pow 2).sub_const 1
  have hf : HasDerivAt (shortQuadratic a)
      (((2*x+1)*((a+x)^2-1)-4*(a+x)*quadratic x)/((a+x)^2-1)^3) x := by
    convert hasDerivAt_div_square (hasDerivAt_quadratic x) hg hD.ne' using 1 <;>
      (try funext y) <;> dsimp [shortQuadratic,Pi.pow_apply,Pi.sub_apply,id_eq] <;> ring
  have hp : 0≤(2*x+1)*((a+x)^2-1)-4*(a+x)*quadratic x := by
    rw [show (2*x+1)*((a+x)^2-1)-4*(a+x)*quadratic x =
      (a-1-x)*(2*x^2+(2*a+1)*x+a+1) by unfold quadratic; ring]
    exact mul_nonneg (by linarith [hx.2]) (by have := hx.1; positivity)
  exact ⟨_,hf,div_nonneg hp (pow_pos hD 3).le⟩

theorem longCubic_monotone {b a : ℝ} (hb : 5≤b) :
    MonotoneOn (longCubic b) (Set.Icc 0 a) := by
  apply monoOn_Icc_of_deriv_data
  intro x hx
  have hD : 0<(b+x)^2-x^2 := by
    rw [show (b+x)^2-x^2=b*(b+2*x) by ring]
    have := hx.1
    positivity
  have hg := (((hasDerivAt_id x).const_add b).pow 2).sub ((hasDerivAt_id x).pow 2)
  have hf : HasDerivAt (longCubic b)
      (((6*x^2+6*x+1)*((b+x)^2-x^2)-4*b*cubic x)/((b+x)^2-x^2)^3) x := by
    convert hasDerivAt_div_square (hasDerivAt_cubic x) hg hD.ne' using 1 <;>
      (try funext y) <;> dsimp [longCubic,Pi.pow_apply,Pi.sub_apply,id_eq] <;> ring
  have hp : 0≤(6*x^2+6*x+1)*((b+x)^2-x^2)-4*b*cubic x := by
    rw [show (6*x^2+6*x+1)*((b+x)^2-x^2)-4*b*cubic x =
      b*(4*x^3+6*b*x^2+(6*b-2)*x+b) by unfold cubic; ring]
    have hb' : 0≤6*b-2 := by linarith
    have := hx.1
    positivity
  exact ⟨_,hf,div_nonneg hp (pow_pos hD 3).le⟩

theorem longQuadratic_monotone {b a : ℝ} (hb : 5≤b) :
    MonotoneOn (longQuadratic b) (Set.Icc 0 a) := by
  apply monoOn_Icc_of_deriv_data
  intro x hx
  have hD : 0<(b+x)^2-(x+1)^2 := by
    rw [show (b+x)^2-(x+1)^2=(b-1)*(b+1+2*x) by ring]
    have hb' : 0<b-1 := by linarith
    have := hx.1
    positivity
  have hg := (((hasDerivAt_id x).const_add b).pow 2).sub (((hasDerivAt_id x).add_const 1).pow 2)
  have hf : HasDerivAt (longQuadratic b)
      (((2*x+1)*((b+x)^2-(x+1)^2)-4*(b-1)*quadratic x)/((b+x)^2-(x+1)^2)^3) x := by
    convert hasDerivAt_div_square (hasDerivAt_quadratic x) hg hD.ne' using 1 <;>
      (try funext y) <;> dsimp [longQuadratic,Pi.pow_apply,Pi.sub_apply,id_eq] <;> ring
  have hp : 0≤(2*x+1)*((b+x)^2-(x+1)^2)-4*(b-1)*quadratic x := by
    rw [show (2*x+1)*((b+x)^2-(x+1)^2)-4*(b-1)*quadratic x =
      (b-1)*(2*b*x+b+1) by unfold quadratic; ring]
    have hb' : 0≤b-1 := by linarith
    have := hx.1
    positivity
  exact ⟨_,hf,div_nonneg hp (pow_pos hD 3).le⟩

theorem fluxBound_diagonal_eq (a b x : ℝ) :
    fluxBound (a+x) (b+x) x = Real.pi^3/60 *
      ((shortCubic a x+longCubic b x)/3+shortQuadratic a x+longQuadratic b x) := by
  unfold fluxBound shortCubic shortQuadratic longCubic longQuadratic
  ring

/-- Simultaneously increasing both sides and the strip length increases B
on the full interval used by the canonical comparison. -/
theorem fluxBound_diagonal_monotone {a b : ℝ} (ha : 5≤a) (hab : a≤b) :
    MonotoneOn (fun x => fluxBound (a+x) (b+x) x) (Set.Icc 0 (a-1)) := by
  intro x hx y hy hxy
  change fluxBound (a+x) (b+x) x ≤ fluxBound (a+y) (b+y) y
  rw [fluxBound_diagonal_eq,fluxBound_diagonal_eq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h1 := shortCubic_monotone ha hx hy hxy
  have h2 := longCubic_monotone (show 5≤b by linarith) hx hy hxy
  have h3 := shortQuadratic_monotone ha hx hy hxy
  have h4 := longQuadratic_monotone (show 5≤b by linarith) hx hy hxy
  linarith

end
end SpanningTreeIsoperimetry.FluxBounds
