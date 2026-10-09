import SpanningTreeIsoperimetry.FourthOrderRectangleError
import SpanningTreeIsoperimetry.SecondProfileComparison

/-! Actual refined and coarse coupled rectangle errors at equal perimeter. -/
namespace SpanningTreeIsoperimetry.CoupledRectangleBounds

open RectangularRemainder RectangularSecondProfile SharpRectangleExpansion
open FourthOrderRectangleError SecondProfileComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

private theorem area_gap_identity {R r s S : ℕ} (hRr : R≤r) (hrs : r≤s) (hsum : r+s=R+S) :
    R*S+(r-R)*(s-R)=r*s := by
  have hsubr := Nat.sub_add_cancel hRr
  have hsubs := Nat.sub_add_cancel (hRr.trans hrs)
  have hS : S=r-R+s := by omega
  have hrp := congrArg (fun x : ℕ => x*s) hsubr
  have hsp := congrArg (fun x : ℕ => (r-R)*x) hsubs
  rw [hS]
  nlinarith

private theorem area_gap_pos {R r s S : ℕ} (hRr : R<r) (hrs : r≤s) (hsum : r+s=R+S) :
    0<r*s-R*S := by
  have he := area_gap_identity hRr.le hrs hsum
  have hp := Nat.mul_pos (Nat.sub_pos_of_lt hRr) (Nat.sub_pos_of_lt (hRr.trans_le hrs))
  omega

private theorem area_gap_cast {R r s S : ℕ} (hRr : R≤r) (hrs : r≤s) (hsum : r+s=R+S) :
    ((r*s-R*S : ℕ) : ℝ)=(r : ℝ)*s-(R : ℝ)*S := by
  have he := area_gap_identity hRr hrs hsum
  have harea : R*S≤r*s := by omega
  rw [Nat.cast_sub harea,Nat.cast_mul,Nat.cast_mul]

/-- The full refined estimate, including the exceptional width-three constant. -/
theorem refined_rectangle_error_general {R r s S : ℕ} (hR : 3≤R) (hRr : R<r)
    (hrs : r≤s) (hsS : s≤S) (hsum : r+s=R+S) (haspect : S≤3*R) :
    error r s-error R S<
      ((r*s-R*S : ℕ) : ℝ)/(2*(R : ℝ)^2*(r : ℝ)^2)+1/(4*(r : ℝ)^4)+
        (if R=3 then 1/(3*(R : ℝ)^4) else 1/(4*(R : ℝ)^4)) := by
  have hR0 : 0<R := by omega
  have hr4 : 4≤r := by omega
  have hRS : R≤S := hRr.le.trans (hrs.trans hsS)
  have hsr : s≤3*r := hsS.trans (haspect.trans (Nat.mul_le_mul_left 3 hRr.le))
  have hrerr := sharpError_four hr4 hrs hsr
  have hRerr : |sharpError R S|<(if R=3 then 1/(3*(R : ℝ)^4) else 1/(4*(R : ℝ)^4)) := by
    by_cases he : R=3
    · rw [if_pos he]
      exact sharpError_three hR hRS haspect
    · rw [if_neg he]
      exact sharpError_four (by omega) hRS haspect
  have hL : (r : ℝ)+s=(R : ℝ)+S := by exact_mod_cast hsum
  have hp := coupled_profile_lt (R := (R : ℝ)) (r := (r : ℝ)) (s := (s : ℝ)) (S := (S : ℝ))
    (by exact_mod_cast hR0) (by exact_mod_cast hRr) (by exact_mod_cast hrs)
    (by exact_mod_cast hsS) hL (by exact_mod_cast haspect)
  rw [← area_gap_cast hRr.le hrs hsum,sub_div] at hp
  unfold sharpError at hrerr hRerr
  rw [← hL] at hRerr
  have hru := (abs_lt.mp hrerr).2
  have hRl := (abs_lt.mp hRerr).1
  linarith

/-- Stable main interface for canonical normalized error absorption. -/
theorem refined_rectangle_error {R r s S : ℕ} (hR : 4≤R) (hRr : R<r)
    (hrs : r≤s) (hsS : s≤S) (hsum : r+s=R+S) (haspect : S≤3*R) :
    error r s-error R S<
      ((r*s-R*S : ℕ) : ℝ)/(2*(R : ℝ)^2*(r : ℝ)^2)+1/(4*(r : ℝ)^4)+1/(4*(R : ℝ)^4) := by
  simpa only [if_neg (show R≠3 by omega)] using
    refined_rectangle_error_general (by omega : 3≤R) hRr hrs hsS hsum haspect

private theorem coarse_four_scalar {R r g : ℝ} (hR : 0<R) (hRr : R≤r) (hg : 1≤g) :
    g/(2*R^2*r^2)+1/(4*r^4)+1/(4*R^4)≤g/R^4 := by
  have hr : 0<r := hR.trans_le hRr
  have hg0 : 0≤g := by linarith
  have hp : R^2≤r^2 := pow_le_pow_left₀ hR.le hRr 2
  have hden : 2*R^4≤2*R^2*r^2 := by
    have h := mul_le_mul_of_nonneg_left hp (show 0≤2*R^2 by positivity)
    nlinarith
  have ha : g/(2*R^2*r^2)≤g/(2*R^4) :=
    div_le_div_of_nonneg_left hg0 (by positivity) hden
  have hb : (1 : ℝ)/(4*r^4)≤1/(4*R^4) := by
    apply one_div_le_one_div_of_le (by positivity : 0<4*R^4)
    gcongr
  calc
    _≤g/(2*R^4)+1/(4*R^4)+1/(4*R^4) := by linarith
    _=(g/2+1/2)/R^4 := by field_simp [hR.ne'] <;> ring
    _≤g/R^4 := div_le_div_of_nonneg_right (by linarith) (pow_nonneg hR.le 4)

private theorem coarse_three_scalar {r g : ℝ} (hr : 4≤r) (hg : 1≤g) :
    g/(2*3^2*r^2)+1/(4*r^4)+1/(3*3^4)<g/3^4 := by
  have hr0 : 0<r := by linarith
  have hg0 : 0≤g := by linarith
  have ha : g/(2*3^2*r^2)≤g/(2*3^4) := by
    apply div_le_div_of_nonneg_left hg0 (by norm_num)
    nlinarith [sq_nonneg (r-3)]
  have hb : (1 : ℝ)/(4*r^4)≤1/(4*4^4) := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<4*4^4)
    gcongr
  norm_num at ha hb ⊢
  nlinarith

/-- Distinct ordered integer hulls have a strict actual coupled error bound. -/
theorem coupled_rectangle_error_strict {R r s S : ℕ} (hR : 3≤R) (hRr : R<r)
    (hrs : r≤s) (hsS : s≤S) (hsum : r+s=R+S) (haspect : S≤3*R) :
    error r s-error R S<((r*s-R*S : ℕ) : ℝ)/(R : ℝ)^4 := by
  have hg : (1 : ℝ)≤((r*s-R*S : ℕ) : ℝ) := by
    exact_mod_cast (show 1≤r*s-R*S from area_gap_pos hRr hrs hsum)
  by_cases he : R=3
  · subst R
    have h := refined_rectangle_error_general (by omega : 3≤3) hRr hrs hsS hsum haspect
    simp only [if_pos rfl] at h
    exact h.trans (coarse_three_scalar (by exact_mod_cast (show 4≤r by omega)) hg)
  · have hR4 : 4≤R := by omega
    exact (refined_rectangle_error hR4 hRr hrs hsS hsum haspect).trans_le
      (coarse_four_scalar (by exact_mod_cast (show 0<R by omega)) (by exact_mod_cast hRr.le) hg)

/-- The actual coupled rectangle-error lemma, including identical hulls. -/
theorem coupled_rectangle_error {R r s S : ℕ} (hR : 3≤R) (hRr : R≤r)
    (hrs : r≤s) (hsS : s≤S) (hsum : r+s=R+S) (haspect : S≤3*R) :
    error r s-error R S≤((r*s-R*S : ℕ) : ℝ)/(R : ℝ)^4 := by
  by_cases he : R=r
  · subst r
    have hss : s=S := by omega
    subst S
    simp
  · exact (coupled_rectangle_error_strict hR (lt_of_le_of_ne hRr he) hrs hsS hsum haspect).le

end
end SpanningTreeIsoperimetry.CoupledRectangleBounds
