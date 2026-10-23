module

public import SpanningTreeIsoperimetry.FourthOrderRectangleError
public import SpanningTreeIsoperimetry.FirstProfileModular

@[expose] public section

set_option backward.privateInPublic true

/-! The printed fixed-aspect fourth-order rectangle remainder for every
positive aspect. Only the quadrature coefficient grows with the aspect;
the existing retained-mode and tail bounds apply to every ordered hull. -/
namespace SpanningTreeIsoperimetry.FixedAspectRectangleError
open SquareMaximality SquareMaximality.Rectangle
open RectangularRemainder RectangularSecondProfile RectangleResidualBounds
open SharpRectangleExpansion RectangleTaylorRemainder RectangleTailRemainder
open TrapezoidalKernelError FourthOrderRectangleError RectangleProfileContinuity
open Filter Asymptotics
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def orderedConstant (u : ℝ) : ℝ := u*Real.pi^5/6048+|retainedConstant 396 37600|+1

theorem orderedConstant_pos {u : ℝ} (hu : 0<u) : 0<orderedConstant u := by
  unfold orderedConstant
  positivity

private theorem components {r s : ℕ} (hr : 0<r) (hrs : r≤s) :
    |sharpError r s|≤
      |-(s : ℝ)*(Concrete.epsilon squareLatticeEntropy r-Real.pi/(12*r)-Real.pi^3/(1440*(r : ℝ)^3))|+
      |retainedCorrection r s|+tailError r s := by
  have hs := hr.trans_le hrs
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hsR : (0 : ℝ)<s := by exact_mod_cast hs
  have hB := omittedBose_nonneg (div_pos hsR hrR) hr
  let a : ℝ := -(s : ℝ)*(Concrete.epsilon squareLatticeEntropy r-Real.pi/(12*r)-Real.pi^3/(1440*(r : ℝ)^3))
  let b := retainedCorrection r s
  let c := logTail (Real.exp (-2*Real.pi*((s : ℝ)/r))) r
  let d := (Real.pi^3*s/(6*(r : ℝ)^3))*omittedBose ((s : ℝ)/r) r
  let e := (1/2 : ℝ)*Real.log (1-Real.exp (-4*r*Concrete.alpha))
  have hd : 0≤d := by dsimp [d]; positivity
  rw [sharpError_exact hr hs]
  change |a+b-c+d-e|≤|a|+|b|+(|c|+d+|e|)
  have h1 := abs_add_le a b
  have h2 := abs_sub_le (a+b) (0 : ℝ) c
  have h3 := abs_add_le (a+b-c) d
  have h4 := abs_sub_le (a+b-c+d) (0 : ℝ) e
  simp only [sub_zero,zero_sub,abs_neg] at h2 h4
  rw [abs_of_nonneg hd] at h3
  linarith

/-- No upper restriction on s/r occurs in this ordered estimate. -/
theorem ordered_bound {r s : ℕ} (hr : 4≤r) (hrs : r≤s) :
    |sharpError r s|<orderedConstant ((s : ℝ)/r)/(r : ℝ)^4 := by
  have hr0 : 0<r := by omega
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr0
  have hε : |-(s : ℝ)*(Concrete.epsilon squareLatticeEntropy r-Real.pi/(12*r)-Real.pi^3/(1440*(r : ℝ)^3))|≤
      (((s : ℝ)/r)*Real.pi^5/6048)/(r : ℝ)^4 := by
    rw [abs_mul,abs_neg,abs_of_nonneg (Nat.cast_nonneg s)]
    calc
      _≤(s : ℝ)*(Real.pi^5/(6048*(r : ℝ)^5)) :=
        mul_le_mul_of_nonneg_left (epsilon_next_error hr0) (Nat.cast_nonneg s)
      _=_ := by field_simp [hrR.ne'] <;> ring
  have hret : |retainedCorrection r s|≤|retainedConstant 396 37600|/(r : ℝ)^4 :=
    (retainedCorrection_four hr hrs).trans (div_le_div_of_nonneg_right (le_abs_self _) (by positivity))
  have htail := tailError_four_lt hr hrs
  have hsum := add_lt_add_of_le_of_lt (add_le_add hε hret) htail
  calc
    _<(((s : ℝ)/r)*Real.pi^5/6048)/(r : ℝ)^4+
      |retainedConstant 396 37600|/(r : ℝ)^4+(1/1000)/(r : ℝ)^4 :=
        (components hr0 hrs).trans_lt hsum
    _<orderedConstant ((s : ℝ)/r)/(r : ℝ)^4 := by
      unfold orderedConstant
      have h := div_lt_div_of_pos_right (show (1/1000 : ℝ)<1 by norm_num) (pow_pos hrR 4)
      rw [add_div,add_div]
      linarith only [h]

/-- Exact reciprocal symmetry of the full fourth-order residual. -/
theorem sharpError_swap {r s : ℕ} (hr : 0<r) (hs : 0<s) : sharpError r s=sharpError s r := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hsR : (0 : ℝ)<s := by exact_mod_cast hs
  have hratio : ((s : ℝ)/r)⁻¹=(r : ℝ)/s := by simp only [inv_div]
  have hK := FirstProfileModular.K_inv (div_pos hsR hrR)
  have hK2 := SecondProfileModular.K2_inv (div_pos hsR hrR)
  rw [hratio] at hK hK2
  have hF : F r s=F s r := by
    unfold F
    rw [rectangle_treeCount_eq_foundation,rectangle_treeCount_eq_foundation,tauRect_comm r s]
    ring
  have h1 := F_eq_K hr hs
  have h2 := F_eq_K hs hr
  have herr : error r s=error s r := by
    rw [hF] at h1
    rw [add_comm (s : ℝ) (r : ℝ),hK] at h2
    linarith
  rw [sharpError,sharpError,herr,hK2,add_comm (r : ℝ) (s : ℝ)]

/-- Explicit fixed-aspect constant, valid on both orientations. -/
def aspectConstant (u : ℝ) : ℝ := orderedConstant u+orderedConstant u⁻¹/u^4

theorem aspectConstant_pos {u : ℝ} (hu : 0<u) : 0<aspectConstant u := by
  unfold aspectConstant
  exact add_pos (orderedConstant_pos hu) (div_pos (orderedConstant_pos (inv_pos.mpr hu)) (pow_pos hu 4))

/-- A uniform r^-4 estimate at every prescribed positive aspect u.
The threshold merely requires both lattice sides to be at least four. -/
theorem fixed_aspect_bound {u : ℝ} (hu : 0<u) {r s : ℕ} (hr : 4≤r) (hs : 4≤s)
    (haspect : (s : ℝ)/r=u) : |sharpError r s|<aspectConstant u/(r : ℝ)^4 := by
  have hr0 : 0<r := by omega
  have hs0 : 0<s := by omega
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr0
  have hsR : (0 : ℝ)<s := by exact_mod_cast hs0
  by_cases hrs : r≤s
  · have h := ordered_bound hr hrs
    rw [haspect] at h
    apply h.trans
    apply div_lt_div_of_pos_right _ (pow_pos hrR 4)
    unfold aspectConstant
    have hp := div_pos (orderedConstant_pos (inv_pos.mpr hu)) (pow_pos hu 4)
    linarith
  · have hsr : s≤r := by omega
    have h := ordered_bound hs hsr
    have hinv : (r : ℝ)/s=u⁻¹ := by rw [← haspect,inv_div]
    have hs_eq : (s : ℝ)=u*r := (div_eq_iff hrR.ne').mp haspect
    rw [← sharpError_swap hr0 hs0,hinv] at h
    have hden : orderedConstant u⁻¹/(s : ℝ)^4=(orderedConstant u⁻¹/u^4)/(r : ℝ)^4 := by
      rw [hs_eq]
      field_simp [hu.ne',hrR.ne'] <;> ring
    rw [hden] at h
    apply h.trans
    apply div_lt_div_of_pos_right _ (pow_pos hrR 4)
    unfold aspectConstant
    linarith [orderedConstant_pos hu]

/-- Standard asymptotic notation along any fixed-aspect integer family. -/
theorem fixed_aspect_isBigO {u : ℝ} (hu : 0<u) (r s : ℕ → ℕ)
    (hr : Tendsto r atTop atTop) (hs : Tendsto s atTop atTop)
    (haspect : ∀ n,(s n : ℝ)/(r n : ℝ)=u) :
    (fun n => sharpError (r n) (s n)) =O[atTop] (fun n => 1/(r n : ℝ)^4) := by
  apply isBigO_iff.mpr
  refine ⟨aspectConstant u,?_⟩
  filter_upwards [hr.eventually (eventually_ge_atTop 4),hs.eventually (eventually_ge_atTop 4)] with n hrn hsn
  have h := (fixed_aspect_bound hu hrn hsn (haspect n)).le
  simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : (0 : ℝ)≤1/(r n : ℝ)^4),div_eq_mul_inv,one_mul,abs_inv,abs_pow,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (r n))] using h


theorem aspectConstant_continuousAt {u : ℝ} (hu : 0<u) : ContinuousAt aspectConstant u := by
  unfold aspectConstant orderedConstant
  have hne : u≠0 := hu.ne'
  have hp : u^4≠0 := pow_ne_zero 4 hne
  have hc : (6048 : ℝ)≠0 := by norm_num
  fun_prop

/-- The fourth-order bound remains valid when the integer aspect ratios
merely converge to any u>0, including irrational limiting aspects. -/
theorem limiting_aspect_isBigO {u : ℝ} (hu : 0<u) (r s : ℕ → ℕ)
    (hr : Tendsto r atTop atTop) (hs : Tendsto s atTop atTop)
    (haspect : Tendsto (fun n => (s n : ℝ)/(r n : ℝ)) atTop (𝓝 u)) :
    (fun n => sharpError (r n) (s n)) =O[atTop] (fun n => 1/(r n : ℝ)^4) := by
  have hC := (aspectConstant_continuousAt hu).tendsto.comp haspect
  have hbound : ∀ᶠ n in atTop,aspectConstant ((s n : ℝ)/(r n : ℝ))<aspectConstant u+1 :=
    hC.eventually (gt_mem_nhds (by linarith : aspectConstant u<aspectConstant u+1))
  apply isBigO_iff.mpr
  refine ⟨aspectConstant u+1,?_⟩
  filter_upwards [hr.eventually (eventually_ge_atTop 4),hs.eventually (eventually_ge_atTop 4),hbound]
    with n hrn hsn hn
  have hrR : (0 : ℝ)<r n := by exact_mod_cast (show 0<r n by omega)
  have hsR : (0 : ℝ)<s n := by exact_mod_cast (show 0<s n by omega)
  have h := (fixed_aspect_bound (div_pos hsR hrR) hrn hsn rfl).le
  have h' := h.trans (div_le_div_of_nonneg_right hn.le (pow_nonneg hrR.le 4))
  simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : (0 : ℝ)≤1/(r n : ℝ)^4),div_eq_mul_inv,one_mul,abs_inv,abs_pow,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (r n))] using h'

end
end SpanningTreeIsoperimetry.FixedAspectRectangleError
