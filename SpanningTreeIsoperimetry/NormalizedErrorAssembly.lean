module

public import SpanningTreeIsoperimetry.CanonicalRectangleBounds
public import SpanningTreeIsoperimetry.FiniteSingletonSquareLower
public import SpanningTreeIsoperimetry.RectangularRemainder

@[expose] public section

/-! Algebraic conversion of the refined coupled remainder bound into actual
singleton absorption. The coupled estimate is an explicit input until the
quantitative fourth-order expansion is closed. -/
namespace SpanningTreeIsoperimetry.NormalizedErrorAssembly
open CanonicalRectangleBounds RectangularRemainder Ferrers CornerEnergy
open SquareMaximality.Boundary
noncomputable section

theorem coupled_bound_factorization {R r g : ℝ} (hR : R≠0) (hr : r≠0) (hg : g≠0) :
    g/(2*R^2*r^2)+1/(4*r^4)+1/(4*R^4)=
      (g/r^4)*((r/R)^2/2+(1+(r/R)^4)/(4*g)) := by
  field_simp
  <;> ring

theorem normalized_error_of_coupled {R S r s T t e : ℕ}
    (hR : 4≤R) (hsize : T^2-T+1≤R) (ht : t<T)
    (hr : r=R+T-t) (hrs : r≤s)
    (hbound : error r s-error R S ≤
      ((T*(T+e)-t*(t+e) : ℕ) : ℝ)/(2*(R : ℝ)^2*(r : ℝ)^2)+
        1/(4*(r : ℝ)^4)+1/(4*(R : ℝ)^4)) :
    error r s-error R S < ((T*(T+e)-t*(t+e) : ℕ) : ℝ)*
      correction (faceRectangle (r-1) (s-1)) {(0,0)} := by
  let g : ℝ := ((T*(T+e)-t*(t+e) : ℕ) : ℝ)
  have hg : 0<g := by
    have hp := imbalance_gap_pos (e := e) ht
    dsimp [g]
    exact_mod_cast (show 0<T*(T+e)-t*(t+e) by omega)
  have hrNat : 4≤r := by omega
  have hR0 : (R : ℝ)≠0 := by exact_mod_cast (show R≠0 by omega)
  have hr0 : (r : ℝ)≠0 := by exact_mod_cast (show r≠0 by omega)
  have hcoef := canonical_normalized_coefficient_lt (e := e) hR hsize ht
  change (((R+T-t : ℕ) : ℝ)/R)^2/2+
    (1+(((R+T-t : ℕ) : ℝ)/R)^4)/(4*g)<5/3 at hcoef
  rw [← hr] at hcoef
  have hsingle := (FiniteSingletonSquareLower.singleton_lower_primal
    (by omega : 2≤r) (by omega : 2≤s)).1
  rw [min_eq_left hrs] at hsingle
  have hf := coupled_bound_factorization hR0 hr0 hg.ne'
  change error r s-error R S≤g/(2*(R : ℝ)^2*(r : ℝ)^2)+
    1/(4*(r : ℝ)^4)+1/(4*(R : ℝ)^4) at hbound
  rw [hf] at hbound
  calc
    error r s-error R S ≤ (g/(r : ℝ)^4)*
        (((r : ℝ)/R)^2/2+(1+((r : ℝ)/R)^4)/(4*g)) := hbound
    _ < (g/(r : ℝ)^4)*(5/3) := mul_lt_mul_of_pos_left hcoef (by positivity)
    _ = g*(5/(3*(r : ℝ)^4)) := by ring
    _ < g*correction (faceRectangle (r-1) (s-1)) {(0,0)} :=
      mul_lt_mul_of_pos_left hsingle hg

end
end SpanningTreeIsoperimetry.NormalizedErrorAssembly
