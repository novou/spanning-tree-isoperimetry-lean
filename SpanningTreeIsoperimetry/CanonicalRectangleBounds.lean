module

public import SpanningTreeIsoperimetry.Targets

@[expose] public section

/-! Exact selector arithmetic for normalized rectangular error and large
imbalance bounds. These are inequalities for the actual integer hull parameters. -/
namespace SpanningTreeIsoperimetry.CanonicalRectangleBounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every admissible ordered minimum-side-sum hull has aspect at most three. -/
theorem admissible_aspect_le_three {N L r s : ℕ} (hL : IsMinimumSideSum N L)
    (hr : 0<r) (hs : 0<s) (harea : N≤r*s) (hsum : r+s=L) : s≤3*r := by
  by_contra hn
  have hs2 : 2≤s := by omega
  have hsub : s-2+2=s := Nat.sub_add_cancel hs2
  have hp : 2*r≤s-2 := by omega
  have hprod := congrArg (fun z : ℕ => r*z) hsub
  have hnew : N≤(r+1)*(s-2) := by nlinarith
  have hmin := minimum_side_sum_le hL hnew
  omega

private theorem balanced_deficit_lt {N m e d : ℕ} (hN : 0<N)
    (hL : IsMinimumSideSum N (2*m+e)) (harea : N+d=m*(m+e)) : d<m := by
  have hm : 0<m := by
    by_contra hn
    have hm0 : m=0 := by omega
    simp [hm0] at harea
    omega
  have hh := deficit_lt_min_side hL hm (show 0<m+e by omega)
    (show N≤m*(m+e) by omega) (show m+(m+e)=2*m+e by omega)
  rw [min_eq_left (by omega : m≤m+e)] at hh
  omega

/-- The stronger size relation includes the canonical strip deficit. -/
theorem feasible_size_relation {N m e d T : ℕ} (hN : 0<N)
    (hL : IsMinimumSideSum N (2*m+e)) (harea : N+d=m*(m+e)) (hT : T*(T+e)≤d) :
    T^2-T+T*e+(d-T*(T+e))+1≤m-T := by
  have hd := balanced_deficit_lt hN hL harea
  have hTm := selector_index_lt_half_sum hN harea.symm hT
  have hr : m-T+T=m := Nat.sub_add_cancel hTm.le
  have hj : d-T*(T+e)+T*(T+e)=d := Nat.sub_add_cancel hT
  have hs : T≤T^2 := by simpa only [pow_two] using Nat.le_mul_self T
  have hsq : T^2-T+T=T^2 := Nat.sub_add_cancel hs
  nlinarith

/-- Actual canonical parameters supply the size estimate used by both the
rectangle and flux comparisons. -/
theorem canonical_size_relation {N : ℕ} (hN : 0<N) :
    let L := minimumSideSum N
    let m := L/2
    let e := L%2
    let d := m*(m+e)-N
    let T := selectorIndex d e
    T^2-T+T*e+(canonicalParameters N).2.2+1≤(canonicalParameters N).1 := by
  let L := minimumSideSum N
  let m := L/2
  let e := L%2
  let d := m*(m+e)-N
  let T := selectorIndex d e
  have hL : IsMinimumSideSum N L := ceil_sqrt_is_minimum_side_sum hN
  have hLm : L=2*m+e := by dsimp [m,e]; omega
  have he : e≤1 := by dsimp [e]; omega
  have harea := balanced_area_ge hL hLm he
  have hNd : N+d=m*(m+e) := by dsimp [d]; omega
  have hfeas := (selectorIndex_bounds d e).1
  have hh := feasible_size_relation hN (by simpa only [hLm] using hL) hNd hfeas
  exact hh

theorem two_mul_imbalance_le_short {R T : ℕ} (hR : 4≤R)
    (hsize : T^2-T+1≤R) (hT : 2≤T) : 2*T≤R := by
  by_cases hT2 : T=2
  · omega
  · have hT3 : 3≤T := by omega
    have hm := Nat.mul_le_mul_left T (show 2≤T-1 by omega)
    have he : T*(T-1)=T^2-T := by rw [Nat.mul_sub_left_distrib,pow_two]; simp
    rw [he] at hm
    nlinarith

theorem canonical_aspect_arithmetic {R T e : ℕ} (hR : 4≤R) (he : e≤1)
    (hsize : T^2-T+1≤R) : R+2*T+e≤3*R := by
  by_cases hT : 2≤T
  · have hh := two_mul_imbalance_le_short hR hsize hT
    omega
  · omega

theorem imbalance_gap_pos {T t e : ℕ} (ht : t<T) : 1≤T*(T+e)-t*(t+e) := by
  let δ := T-t
  have hδ : 1≤δ := by dsimp [δ]; omega
  have hT : T=δ+t := by dsimp [δ]; omega
  have hid : T*(T+e)=δ*(T+t+e)+t*(t+e) := by rw [hT]; ring
  have hm := Nat.mul_le_mul hδ (show 1≤T+t+e by omega)
  omega

theorem imbalance_gap_three {T t e : ℕ} (hT2 : 2≤T) (ht : t<T) :
    3≤T*(T+e)-t*(t+e) := by
  let δ := T-t
  have hδ : 1≤δ := by dsimp [δ]; omega
  have hT : T=δ+t := by dsimp [δ]; omega
  have hid : T*(T+e)=δ*(T+t+e)+t*(t+e) := by rw [hT]; ring
  by_cases ht0 : t=0
  · have hδ2 : 2≤δ := by omega
    have hm := Nat.mul_le_mul hδ2 (show 2≤T+t+e by omega)
    omega
  · have hm := Nat.mul_le_mul hδ (show 3≤T+t+e by omega)
    omega

theorem normalized_ratio_one {R T t : ℕ} (hR : 4≤R) (hT : T=1) (ht : t<T) :
    ((R+T-t : ℕ) : ℝ)/R≤5/4 := by
  apply (div_le_iff₀ (show (0 : ℝ)<R by exact_mod_cast (show 0<R by omega))).mpr
  have hr : R+T-t=R+1 := by omega
  rw [hr]
  push_cast
  have hR' : (4 : ℝ)≤R := by exact_mod_cast hR
  linarith

theorem normalized_ratio_many {R T t : ℕ} (hR : 4≤R) (hsize : T^2-T+1≤R)
    (hT : 2≤T) (ht : t<T) : ((R+T-t : ℕ) : ℝ)/R≤3/2 := by
  have hRT := two_mul_imbalance_le_short hR hsize hT
  apply (div_le_iff₀ (show (0 : ℝ)<R by exact_mod_cast (show 0<R by omega))).mpr
  have hr : 2*(R+T-t)≤3*R := by omega
  have hr' : 2*((R+T-t : ℕ) : ℝ)≤3*(R : ℝ) := by exact_mod_cast hr
  linarith

/-- The exact normalized coefficients are strictly below the singleton
comparison constant in both selector regimes. -/
theorem coefficient_one {a g : ℝ} (ha0 : 0≤a) (ha : a≤5/4) (hg : 1≤g) :
    a^2/2+(1+a^4)/(4*g)<5/3 := by
  have hg0 : 0<g := by linarith
  have h2 : a^2≤(5/4 : ℝ)^2 := by gcongr
  have h4 : a^4≤(5/4 : ℝ)^4 := by gcongr
  have hdiv : (1+a^4)/(4*g)≤(1+(5/4 : ℝ)^4)/4 := by
    apply (div_le_div_iff₀ (by positivity : 0<4*g) (by norm_num : (0 : ℝ)<4)).mpr
    nlinarith
  norm_num at h2 h4 hdiv
  linarith

theorem coefficient_many {a g : ℝ} (ha0 : 0≤a) (ha : a≤3/2) (hg : 3≤g) :
    a^2/2+(1+a^4)/(4*g)<5/3 := by
  have hg0 : 0<g := by linarith
  have h2 : a^2≤(3/2 : ℝ)^2 := by gcongr
  have h4 : a^4≤(3/2 : ℝ)^4 := by gcongr
  have hdiv : (1+a^4)/(4*g)≤(1+(3/2 : ℝ)^4)/12 := by
    apply (div_le_div_iff₀ (by positivity : 0<4*g) (by norm_num : (0 : ℝ)<12)).mpr
    nlinarith
  norm_num at h2 h4 hdiv
  linarith

theorem canonical_normalized_coefficient_lt {R T t e : ℕ} (hR : 4≤R)
    (hsize : T^2-T+1≤R) (ht : t<T) :
    let a := ((R+T-t : ℕ) : ℝ)/R
    let g := ((T*(T+e)-t*(t+e) : ℕ) : ℝ)
    a^2/2+(1+a^4)/(4*g)<5/3 := by
  by_cases hT : T=1
  · exact coefficient_one (by positivity) (normalized_ratio_one hR hT ht)
      (by exact_mod_cast imbalance_gap_pos (e := e) ht)
  · exact coefficient_many (by positivity) (normalized_ratio_many hR hsize (by omega) ht)
      (by exact_mod_cast imbalance_gap_three (e := e) (by omega) ht)

/-- Exact canonical arithmetic needed to instantiate the real flux bound. -/
theorem canonical_flux_hypotheses {N : ℕ} (hN : 0<N) :
    let L := minimumSideSum N
    let m := L/2
    let e := L%2
    let d := m*(m+e)-N
    let T := selectorIndex d e
    let R := (canonicalParameters N).1
    let S := (canonicalParameters N).2.1
    let k := (canonicalParameters N).2.2
    0<R ∧ R≤S ∧ k≤2*T+1 ∧ T^2-T+k+1≤R ∧ R+k≤S := by
  let L := minimumSideSum N
  let m := L/2
  let e := L%2
  let d := m*(m+e)-N
  let T := selectorIndex d e
  let R := (canonicalParameters N).1
  let S := (canonicalParameters N).2.1
  let k := (canonicalParameters N).2.2
  change 0<R ∧ R≤S ∧ k≤2*T+1 ∧ T^2-T+k+1≤R ∧ R+k≤S
  have hp := selected_hull_properties_of_ceil hN
  change 0<R ∧ R≤S ∧ R+S=minimumSideSum N ∧ R*S=N+k ∧ k<R at hp
  have he : e≤1 := by dsimp [e]; omega
  have hL : IsMinimumSideSum N L := ceil_sqrt_is_minimum_side_sum hN
  have hLm : L=2*m+e := by dsimp [m,e]; omega
  have harea := balanced_area_ge hL hLm he
  have hNd : N+d=m*(m+e) := by dsimp [d]; omega
  have hTm := selector_index_lt_half_sum hN hNd.symm (selectorIndex_bounds d e).1
  have hR : R=m-T := rfl
  have hS : S=m+e+T := rfl
  have hstep := selector_remainder_lt_step (selectorIndex_bounds d e).1 (selectorIndex_bounds d e).2
  change k<2*T+e+1 at hstep
  have hsize := canonical_size_relation hN
  change T^2-T+T*e+k+1≤R at hsize
  refine ⟨hp.1,hp.2.1,?_,?_,?_⟩ <;> omega

end SpanningTreeIsoperimetry.CanonicalRectangleBounds
