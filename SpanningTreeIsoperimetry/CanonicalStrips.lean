import SpanningTreeIsoperimetry.StripTreeComparisons
import SpanningTreeIsoperimetry.Targets

/-! The explicit selector is optimal among all single strips on minimum
side-sum hulls. Excluding nonstrip maximizers is a separate energy argument. -/
namespace SpanningTreeIsoperimetry.CanonicalStrips

open StripTreeComparisons StripPolarization

theorem terminal_parameters {N r s k : ℕ} (hN : 0<N) (hr : 1≤r)
    (hrs : r≤s) (harea : r*s=N+k) (hsum : r+s=minimumSideSum N)
    (hstop : k<s-r+1) : canonicalParameters N=(r,s,k) := by
  let L := minimumSideSum N
  let m := L/2
  let e := L%2
  let d := m*(m+e)-N
  let t := m-r
  let T := selectorIndex d e
  have hL : IsMinimumSideSum N L := ceil_sqrt_is_minimum_side_sum hN
  have hLm : L=2*m+e := by dsimp [m,e]; omega
  have he : e≤1 := by dsimp [e]; omega
  have hrm : r≤m := by change r+s=L at hsum; omega
  have hmt : m=r+t := by dsimp [t]; omega
  have hst : s=m+e+t := by change r+s=L at hsum; omega
  have hbal := balanced_area_ge hL hLm he
  have hNd : N+d=m*(m+e) := by dsimp [d]; omega
  have hid : m*(m+e)=r*s+t*(t+e) := by rw [hst,hmt]; ring
  have hd : d=k+t*(t+e) := by omega
  have hstep : s-r+1=2*t+e+1 := by omega
  have hnext : d<(t+1)*(t+1+e) := by rw [hd]; rw [hstep] at hstop; nlinarith
  have htT : t≤T := (selectorIndex_feasible_iff d e t).mp (by omega)
  have hTt : T≤t := selector_index_maximal hnext (selectorIndex_bounds d e).1
  have hT : T=t := by omega
  change (m-T,m+e+T,d-T*(T+e))=(r,s,k)
  rw [hT]
  simp only [Prod.mk.injEq]
  omega

theorem next_hull_area {N r s k : ℕ} (hr : 1≤r) (hrs : r≤s)
    (harea : r*s=N+k) (hgap : s-r+1≤k) :
    (r-1)*(s+1)=N+(k-(s-r+1)) := by
  have hrsub : r-1+1=r := by omega
  have hssub : s-r+r=s := Nat.sub_add_cancel hrs
  have hksub : k-(s-r+1)+(s-r+1)=k := Nat.sub_add_cancel hgap
  nlinarith

theorem strip_le_canonical {N r s k : ℕ} (hN : 0<N) (hr : 1≤r)
    (hrs : r≤s) (hk : k<r) (harea : r*s=N+k) (hsum : r+s=minimumSideSum N) :
    treeCount (cornerStrip r s k)≤treeCount (canonicalDomain N) := by
  induction r using Nat.strong_induction_on generalizing s k with
  | h r ih =>
    by_cases hstop : k<s-r+1
    · have hp := terminal_parameters hN hr hrs harea hsum hstop
      unfold canonicalDomain
      rw [hp]
    · have hgap : s-r+1≤k := by omega
      have hchain := adjacent_hull_treeCount hr hrs hk hgap
      have hnext := ih (r-1) (by omega) (s := s+1) (k := k-(s-r+1))
        (by omega) (by omega) (by omega) (next_hull_area hr hrs harea hgap) (by omega)
      exact (hchain.1.trans hchain.2).trans hnext

theorem adjacent_hull_strict_of_large {r s k : ℕ} (hr : 1≤r) (hrs : r≤s) (hk : k<r)
    (hgap : s-r+1≤k) (hN : 18≤r*s-k) :
    treeCount (cornerStrip r s k)<treeCount (cornerStrip (r-1) (s+1) (k-(s-r+1))) := by
  have hchain := adjacent_hull_treeCount hr hrs hk hgap
  apply lt_of_le_of_ne (hchain.1.trans hchain.2)
  intro heq
  have hc := (adjacent_hull_treeCount_eq_iff hr hrs hk hgap).mp heq
  have ht := (adjacent_equality_triples hr hrs hk hgap).mp hc
  simp only [Prod.mk.injEq] at ht
  rcases ht with h | h | h | h | h | h <;>
    rcases h with ⟨rfl,rfl,rfl⟩ <;> norm_num at hN

/-- At cardinality at least18 the selector is the unique ordered hull/strip
parameter triple attaining the best single-strip count. -/
theorem strip_eq_canonical_iff {N r s k : ℕ} (hN : 18≤N) (hr : 1≤r)
    (hrs : r≤s) (hk : k<r) (harea : r*s=N+k) (hsum : r+s=minimumSideSum N) :
    treeCount (cornerStrip r s k)=treeCount (canonicalDomain N) ↔
      canonicalParameters N=(r,s,k) := by
  constructor
  · intro heq
    by_cases hstop : k<s-r+1
    · exact terminal_parameters (by omega) hr hrs harea hsum hstop
    · have hgap : s-r+1≤k := by omega
      have hstrict := adjacent_hull_strict_of_large hr hrs hk hgap (by omega)
      have hnext := strip_le_canonical (by omega : 0<N)
        (by omega : 1≤r-1) (by omega : r-1≤s+1)
        (by omega : k-(s-r+1)<r-1) (next_hull_area hr hrs harea hgap) (by omega)
      omega
  · intro hp
    unfold canonicalDomain
    rw [hp]

theorem cornerStrip_connected_of_short_deficit {r s k : ℕ}
    (hr : 1≤r) (hrs : r≤s) (hk : k<r) : (domainGraph (cornerStrip r s k)).Connected := by
  by_cases hr1 : r=1
  · subst r
    have hk0 : k=0 := by omega
    rw [hk0,cornerStrip_zero,domainGraph_eq_foundation,rectangle_eq_foundation]
    exact SquareMaximality.standardRectangle_connected (by omega) (by omega)
  obtain ⟨R,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
  obtain ⟨S,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s≠0)
  exact CornerStripBridge.cornerStrip_connected (by omega) (by omega)

theorem canonicalDomain_connected {N : ℕ} (hN : 0<N) : (domainGraph (canonicalDomain N)).Connected := by
  have hp := selected_hull_properties_of_ceil hN
  change 0<(canonicalParameters N).1 ∧
    (canonicalParameters N).1≤(canonicalParameters N).2.1 ∧
    (canonicalParameters N).1+(canonicalParameters N).2.1=minimumSideSum N ∧
    (canonicalParameters N).1*(canonicalParameters N).2.1=N+(canonicalParameters N).2.2 ∧
    (canonicalParameters N).2.2<(canonicalParameters N).1 at hp
  exact cornerStrip_connected_of_short_deficit (by omega) hp.2.1 hp.2.2.2.2

/-- The canonical construction attains the best count in the entire ordered
minimum-hull strip family, allowing either strip orientation. -/
theorem canonical_strip_optimal {N : ℕ} (hN : 0<N) :
    (canonicalDomain N).card=N ∧ (domainGraph (canonicalDomain N)).Connected ∧
    ∀ r s k : ℕ, 1≤r → r≤s → k<r → r*s=N+k → r+s=minimumSideSum N →
      treeCount (cornerStrip r s k)≤treeCount (canonicalDomain N) ∧
      treeCount (horizontalCornerStrip r s k)≤treeCount (canonicalDomain N) := by
  refine ⟨canonicalDomain_card hN,canonicalDomain_connected hN,?_⟩
  intro r s k hr hrs hk harea hsum
  have h := strip_le_canonical hN hr hrs hk harea hsum
  exact ⟨h,(orientation_treeCount hr hrs hk).trans h⟩

theorem congruent_transpose (A : Domain) : Congruent (transposeDomain A) A := by
  refine ⟨(0,0),true,1,1,Or.inl rfl,Or.inl rfl,?_⟩
  have hf : rigidMotion (0,0) true 1 1=Prod.swap := by funext ⟨x,y⟩; simp [rigidMotion]
  rw [hf]
  ext p
  change p ∈ transposeDomain (transposeDomain A) ↔ p ∈ A
  simp

/-- Among the two orientations on all minimum-side-sum hulls, equality at
N≥18 forces a lattice-isometric copy of the canonical construction. -/
theorem strip_family_equality_congruent {N r s k : ℕ} {A : Domain}
    (hN : 18≤N) (hr : 1≤r) (hrs : r≤s) (hk : k<r)
    (harea : r*s=N+k) (hsum : r+s=minimumSideSum N)
    (hshape : A=cornerStrip r s k ∨ A=horizontalCornerStrip r s k)
    (hcount : treeCount A=treeCount (canonicalDomain N)) : Congruent A (canonicalDomain N) := by
  have hY := strip_le_canonical (by omega : 0<N) hr hrs hk harea hsum
  have hXY := orientation_treeCount hr hrs hk
  rcases hshape with rfl | rfl
  · have hp := (strip_eq_canonical_iff hN hr hrs hk harea hsum).mp hcount
    unfold canonicalDomain
    rw [hp]
    exact congruent_refl _
  · have hEqY : treeCount (cornerStrip r s k)=treeCount (canonicalDomain N) := by omega
    have hp := (strip_eq_canonical_iff hN hr hrs hk harea hsum).mp hEqY
    have hEqXY : treeCount (horizontalCornerStrip r s k)=treeCount (cornerStrip r s k) := by omega
    have hc := (orientation_treeCount_eq_iff hr hrs hk).mp hEqXY
    have hcanonical : canonicalDomain N=cornerStrip r s k := by unfold canonicalDomain; rw [hp]
    rw [hcanonical]
    rcases hc with hrsEq | hkSmall
    · subst s
      rw [horizontal_eq_transpose]
      exact congruent_transpose _
    · have hsets : horizontalCornerStrip r s k=cornerStrip r s k := by
        interval_cases k <;> ext p <;>
          simp only [horizontalCornerStrip,cornerStrip,Finset.mem_sdiff,mem_rectangle] <;> omega
      rw [hsets]
      exact congruent_refl _

end SpanningTreeIsoperimetry.CanonicalStrips
