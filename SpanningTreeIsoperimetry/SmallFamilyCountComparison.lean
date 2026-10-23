module

public import SpanningTreeIsoperimetry.SmallFamilyCostBounds
public import SpanningTreeIsoperimetry.CoupledRectangleBounds
public import SpanningTreeIsoperimetry.CrossHullCountComparison

@[expose] public section

/-! Actual finite count comparison from a certified weighted source profile.
The rectangle error and aspect conversion are proved here, rather than supplied
as analytic premises by the finite-family consumers. -/
namespace SpanningTreeIsoperimetry.SmallFamilyCountComparison
open Ferrers CornerEnergy CornerPrimalDomains CrossHullCountComparison
  SmallFamilyProfiles SmallFamilyMonotonicity SmallFamilyCosts
  SmallFamilyCostBounds MulticornerEndpointChecks RectangularRemainder
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem aspect_difference {R r s S a h : ℕ} (hR : 0<R)
    (hr : r=R+h) (hs : s=r+a) (hS : S=s+h) :
    AspectCost.D (aspectOffset R S)-AspectCost.D (aspectOffset r s)=
      aspectStep a h r := by
  have hR0 : (R : ℝ)≠0 := by exact_mod_cast hR.ne'
  have hr0 : (r : ℝ)≠0 := by exact_mod_cast (show 0<r by omega).ne'
  have hr' : (r : ℝ)=(R : ℝ)+h := by exact_mod_cast hr
  have hs' : (s : ℝ)=(r : ℝ)+a := by exact_mod_cast hs
  have hS' : (S : ℝ)=(s : ℝ)+h := by exact_mod_cast hS
  have hleft : aspectOffset R S=((a : ℝ)+2*h)/((r : ℝ)-h) := by
    unfold aspectOffset
    rw [hS',hs',hr']
    simp only [add_sub_cancel_right]
    field_simp
    <;> ring
  have hright : aspectOffset r s=(a : ℝ)/r := by
    unfold aspectOffset
    rw [hs']
    field_simp
    <;> ring
  rw [hleft,hright]
  rfl

theorem refined_profile_error {R r s S a h : ℕ} (hR : 3≤R) (hh : 0<h)
    (hr : r=R+h) (hs : s=r+a) (hS : S=s+h) (hshape : S≤3*R)
    {q : ℝ} (hq : (if R=3 then (1 : ℝ)/3 else 1/4)≤q) :
    error r s-error R S≤remainderBound q h 0 ((h : ℝ)*(a+h)) r := by
  have he := CoupledRectangleBounds.refined_rectangle_error_general hR
    (show R<r by omega) (show r≤s by omega) (show s≤S by omega)
    (show r+s=R+S by omega) hshape
  have hid : r*s=R*S+h*(a+h) := by rw [hS,hs,hr]; ring
  have hgap : r*s-R*S=h*(a+h) := by omega
  rw [hgap,Nat.cast_mul,Nat.cast_add] at he
  have hr' : (r : ℝ)-h=R := by
    have hcast : (r : ℝ)=(R : ℝ)+h := by exact_mod_cast hr
    linarith
  have hR0 : (0 : ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have hlast : (if R=3 then 1/(3*(R : ℝ)^4) else 1/(4*(R : ℝ)^4))≤q/(R : ℝ)^4 := by
    have hl := div_le_div_of_nonneg_right hq (pow_nonneg hR0.le 4)
    split_ifs at hl ⊢ with hh <;> convert hl using 1 <;>
      simp only [div_eq_mul_inv,mul_inv_rev] <;> ring
  unfold remainderBound
  rw [hr',sub_zero]
  linarith only [he,hlast]

theorem count_lt_of_profile {R r s S a h j : ℕ} (hR : 3≤R) (hh : 0<h)
    (hrEq : r=R+h) (hsEq : s=r+a) (hSEq : S=s+h) (hshape : S≤3*R)
    (M : Corner → Diagram) (hM : ∀ c,IsFerrers (M c))
    (hr : totalDefect M≤r-1) (hs : totalDefect M≤s-1) (hj : j≤S-1)
    (harea : r*s+j=R*S+totalDefect M) (i : Fin 26)
    (ha : gap i=a) (hh' : hullShift i=h) (hshift : sourceShift i=0)
    (hq : (if R=3 then (1 : ℝ)/3 else 1/4)≤errorCoeff i)
    (hcost : endpointCost i r<quadrantFloor i)
    (htarget : finiteTargetEnergy (by omega : 2≤R) hj≤targetCap (targetCapKind i))
    (hsource : quadrantFloor i+weightedLoss Finset.univ (coeff i) shifts r≤
      finiteSourceEnergy M hM hr hs) :
    treeCount (cornerPrimal (r-1) (s-1) M)<treeCount (cornerStrip R S j) := by
  have he := refined_profile_error hR hh hrEq hsEq hSEq hshape hq
  apply count_lt_of_refined_cost (by omega) (by omega) (by omega) (by omega)
    M hM hr hs hj harea (by omega) he
  have hdiff := aspect_difference (by omega : 0<R) hrEq hsEq hSEq
  unfold endpointCost upperCost at hcost
  rw [ha,hh',hshift] at hcost
  linarith only [hcost,htarget,hsource,hdiff]

end
end SpanningTreeIsoperimetry.SmallFamilyCountComparison
