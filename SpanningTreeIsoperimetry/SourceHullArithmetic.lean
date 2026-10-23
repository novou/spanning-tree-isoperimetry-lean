module

public import SpanningTreeIsoperimetry.CanonicalRectangleBounds

@[expose] public section

/-! Actual feasible minimum-side-sum hulls indexed before the canonical
selector. This supplies common arithmetic for every imbalance family. -/
namespace SpanningTreeIsoperimetry.SourceHullArithmetic
noncomputable section

def canonicalIndex (N : ℕ) : ℕ :=
  let L := minimumSideSum N
  let m := L/2
  let e := L%2
  selectorIndex (m*(m+e)-N) e

def sourceParameters (N t : ℕ) : ℕ × ℕ × ℕ :=
  let L := minimumSideSum N
  let m := L/2
  let e := L%2
  let d := m*(m+e)-N
  (m-t,m+e+t,d-t*(t+e))

theorem source_at_canonical (N : ℕ) :
    sourceParameters N (canonicalIndex N)=canonicalParameters N := rfl

structure SourceHullFacts (N t : ℕ) : Prop where
  short_pos : 0<(sourceParameters N t).1
  ordered : (sourceParameters N t).1≤(sourceParameters N t).2.1
  side_sum : (sourceParameters N t).1+(sourceParameters N t).2.1=minimumSideSum N
  area : (sourceParameters N t).1*(sourceParameters N t).2.1=N+(sourceParameters N t).2.2
  deficit_lt_short : (sourceParameters N t).2.2<(sourceParameters N t).1
  canonical_short_le : (canonicalParameters N).1≤(sourceParameters N t).1
  long_le_canonical : (sourceParameters N t).2.1≤(canonicalParameters N).2.1
  side_difference : (sourceParameters N t).2.1=
    (sourceParameters N t).1+2*t+minimumSideSum N%2

theorem source_hull_facts {N t : ℕ} (hN : 0<N) (ht : t≤canonicalIndex N) : SourceHullFacts N t := by
  let L := minimumSideSum N
  let m := L/2
  let e := L%2
  let d := m*(m+e)-N
  let T := selectorIndex d e
  let r := m-t
  let s := m+e+t
  let k := d-t*(t+e)
  change t≤T at ht
  have hp := selected_hull_properties_of_ceil hN
  change 0<m-T ∧ m-T≤m+e+T ∧ m-T+(m+e+T)=L ∧
    (m-T)*(m+e+T)=N+(d-T*(T+e)) ∧ d-T*(T+e)<m-T at hp
  have hTm : T<m := by omega
  have htm : t<m := lt_of_le_of_lt ht hTm
  have hr : 0<r := by dsimp [r]; omega
  have hrs : r≤s := by dsimp [r,s]; omega
  have hs : 0<s := hr.trans_le hrs
  have hL : IsMinimumSideSum N L := ceil_sqrt_is_minimum_side_sum hN
  have hLm : L=2*m+e := by dsimp [m,e]; omega
  have he : e≤1 := by dsimp [e]; omega
  have hbalanced := balanced_area_ge hL hLm he
  have hNd : N+d=m*(m+e) := by dsimp [d]; omega
  have htfeas := selector_index_feasible (selectorIndex_bounds d e).1 ht
  have hkd : k+t*(t+e)=d := Nat.sub_add_cancel htfeas
  have hmt : m=r+t := by dsimp [r]; omega
  have hsdef : s=m+e+t := rfl
  have hid : r*s+t*(t+e)=m*(m+e) := by rw [hsdef,hmt]; ring
  have harea : r*s=N+k := by omega
  have hsum : r+s=L := by dsimp [r,s]; omega
  have hk := deficit_lt_min_side hL hr hs (show N≤r*s by omega) hsum
  rw [min_eq_left hrs] at hk
  have hdeficit : r*s-N=k := by omega
  rw [hdeficit] at hk
  refine ⟨hr,hrs,hsum,harea,hk,?_,?_,?_⟩
  · change m-T≤r
    dsimp [r]
    omega
  · change s≤m+e+T
    dsimp [s]
    omega
  · change s=r+2*t+e
    dsimp [r,s]
    omega

/-- Every ordered admissible minimum-side-sum hull is one of the actual
pre-selector parameter triples. -/
theorem source_parameters_of_hull {N r s k : ℕ} (hN : 0<N) (hr : 0<r) (hrs : r≤s)
    (harea : r*s=N+k) (hsum : r+s=minimumSideSum N) :
    minimumSideSum N/2-r≤canonicalIndex N ∧
      sourceParameters N (minimumSideSum N/2-r)=(r,s,k) := by
  let L := minimumSideSum N
  let m := L/2
  let e := L%2
  let d := m*(m+e)-N
  let t := m-r
  change t≤selectorIndex d e ∧ sourceParameters N t=(r,s,k)
  have hL : IsMinimumSideSum N L := ceil_sqrt_is_minimum_side_sum hN
  have hLm : L=2*m+e := by dsimp [m,e]; omega
  have he : e≤1 := by dsimp [e]; omega
  change r+s=L at hsum
  have hrm : r≤m := by omega
  have hmt : m=r+t := by dsimp [t]; omega
  have hst : s=m+e+t := by omega
  have hbalanced := balanced_area_ge hL hLm he
  have hNd : N+d=m*(m+e) := by dsimp [d]; omega
  have hid : m*(m+e)=r*s+t*(t+e) := by rw [hst,hmt]; ring
  have hd : d=k+t*(t+e) := by omega
  refine ⟨(selectorIndex_feasible_iff d e t).mp (by omega),?_⟩
  change (m-t,m+e+t,d-t*(t+e))=(r,s,k)
  simp only [Prod.mk.injEq]
  omega

theorem source_index_lt_of_noncanonical {N r s k : ℕ} (hN : 0<N) (hr : 0<r) (hrs : r≤s)
    (harea : r*s=N+k) (hsum : r+s=minimumSideSum N) (hne : (r,s,k)≠canonicalParameters N) :
    minimumSideSum N/2-r<canonicalIndex N := by
  have hh := source_parameters_of_hull hN hr hrs harea hsum
  have hneq : minimumSideSum N/2-r≠canonicalIndex N := by
    intro he
    have hp := hh.2
    rw [he,source_at_canonical] at hp
    exact hne hp.symm
  omega

end
end SpanningTreeIsoperimetry.SourceHullArithmetic
