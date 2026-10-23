module

public import SpanningTreeIsoperimetry.ThreeImbalanceTest
public import SpanningTreeIsoperimetry.MulticornerEndpointChecks

@[expose] public section

/-! Actual multicorner scalar comparison in the odd selector-two regime. -/
namespace SpanningTreeIsoperimetry.OddTwoImbalanceTest
open Ferrers CornerEnergy FluxBounds AspectCost SourceHullArithmetic
  CanonicalRectangleBounds CrossHullCountComparison MulticornerEndpointChecks
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem parameter_test {R S j k : ℕ} (hj : j≤5) (hR : j+5≤R)
    (hS : S=R+5) (hk : j+4≤k) :
    realEnergy (horizontalStrip j)+D (5/(R : ℝ))-D (1/((R : ℝ)+2))+
      fluxBound R S j<realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip (k-1)) := by
  let jf : Fin 6 := ⟨j,by omega⟩
  have hend := odd_two_normalized_endpoint jf
  have hR' : (j : ℝ)+5≤R := by exact_mod_cast hR
  have hA := shifted_difference_antitone (A := 5) (B := 1) (a := -2) (b := 0)
    (by norm_num) (by norm_num) (by norm_num)
    (show (j : ℝ)+7∈Set.Ioi (-(-2 : ℝ)) by
      change -(-2 : ℝ)<(j : ℝ)+7
      have hj0 := Nat.cast_nonneg (α := ℝ) j
      linarith)
    (show (R : ℝ)+2∈Set.Ioi (-(-2 : ℝ)) by
      change -(-2 : ℝ)<(R : ℝ)+2
      have hj0 := Nat.cast_nonneg (α := ℝ) j
      linarith)
    (show (j : ℝ)+7≤(R : ℝ)+2 by linarith)
  have hB := ThreeImbalanceTest.flux_base_le (by decide : 3≤5) (by decide : 2≤10)
    hR (show j+10≤S by omega)
  have hidx : (if jf=0 then 3 else 4)≤k-1 := by
    by_cases hz : jf=0
    · simp only [if_pos hz]; omega
    · have hj0 : 0<j := by
        by_contra hn
        have he : j=0 := by omega
        exact hz (Fin.ext he)
      simp only [if_neg hz]; omega
  have hE := realEnergy_strip_monotone hidx
  have haeq : ((R : ℝ)+2)+(-2)=R := by ring
  have hjeq : ((j : ℝ)+7)+(-2)=(j : ℝ)+5 := by ring
  simp only [haeq,hjeq,add_zero] at hA
  change realEnergy (horizontalStrip j)+
    SmallFamilyMonotonicity.aspectStep 1 2 ((j : ℝ)+7)+
    fluxBound ((j : ℝ)+5) ((j : ℝ)+10) j<_ at hend
  simp only [SmallFamilyMonotonicity.aspectStep] at hend
  norm_num only [show (1 : ℝ)+2*2=5 by norm_num] at hend
  have hden : (j : ℝ)+7-2=(j : ℝ)+5 := by ring
  rw [hden] at hend
  norm_num only [Nat.cast_ofNat] at hB
  dsimp only at hE
  linarith only [hend,hA,hB,hE]

theorem actual_selector_multicorner_test {N t : ℕ} (hN : 0<N)
    (hT : canonicalIndex N=2) (he : minimumSideSum N%2=1) (ht : t<canonicalIndex N)
    (M : CornerPrimalDomains.Corner → Diagram) (hM : ∀ c,IsFerrers (M c))
    (hk : CornerPrimalDomains.totalDefect M=(sourceParameters N t).2.2)
    {c d : CornerPrimalDomains.Corner} (hdc : d≠c) (hc : (M c).Nonempty) (hd : (M d).Nonempty) :
    realEnergy (horizontalStrip (canonicalParameters N).2.2)+
      D (aspectOffset (canonicalParameters N).1 (canonicalParameters N).2.1)-
      D (aspectOffset (sourceParameters N t).1 (sourceParameters N t).2.1)+
      fluxBound (canonicalParameters N).1 (canonicalParameters N).2.1 (canonicalParameters N).2.2<
        ∑ c,realEnergy (M c) := by
  let R := (canonicalParameters N).1
  let S := (canonicalParameters N).2.1
  let j := (canonicalParameters N).2.2
  let r := (sourceParameters N t).1
  let s := (sourceParameters N t).2.1
  let k := (sourceParameters N t).2.2
  let m := minimumSideSum N/2
  let Δ := m*(m+minimumSideSum N%2)-N
  have hf := source_hull_facts hN ht.le
  have hsize := canonical_size_relation hN
  change (canonicalIndex N)^2-canonicalIndex N+canonicalIndex N*(minimumSideSum N%2)+j+1≤R at hsize
  rw [hT,he] at hsize
  have hR : j+5≤R := by omega
  have hside := (source_hull_facts hN (le_refl (canonicalIndex N))).side_difference
  rw [source_at_canonical,hT,he] at hside
  change S=R+2*2+1 at hside
  have hS : S=R+5 := by omega
  have hj := selector_remainder_lt_step (selectorIndex_bounds Δ (minimumSideSum N%2)).1
    (selectorIndex_bounds Δ (minimumSideSum N%2)).2
  change j<2*canonicalIndex N+minimumSideSum N%2+1 at hj
  rw [hT,he] at hj
  have hkl := LargeImbalanceGeometry.source_deficit_lower
    (selectorIndex_bounds Δ (minimumSideSum N%2)).1 ht
  change 2*canonicalIndex N+minimumSideSum N%2-1+j≤k at hkl
  rw [hT,he] at hkl
  have htest := parameter_test (show j≤5 by omega) hR hS (show j+4≤k by omega)
  have hR0 : (0 : ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have hr0 : (0 : ℝ)<r := by exact_mod_cast hf.short_pos
  have hRm : R=m-2 := by
    change (sourceParameters N (canonicalIndex N)).1=m-2
    rw [hT]
    rfl
  have hrm : r≤R+2 := by
    change m-t≤R+2
    omega
  have hsrcSide := hf.side_difference
  rw [he] at hsrcSide
  change s=r+2*t+1 at hsrcSide
  have hratio : aspectOffset R S=5/(R : ℝ) := by
    have hS' : (S : ℝ)=(R : ℝ)+5 := by exact_mod_cast hS
    unfold aspectOffset
    rw [hS']
    field_simp
    <;> ring
  have hsrcRatio : 1/((R : ℝ)+2)≤aspectOffset r s := by
    have hm' : (r : ℝ)≤(R : ℝ)+2 := by exact_mod_cast hrm
    have hs' : (r : ℝ)+1≤s := by exact_mod_cast (show r+1≤s by omega)
    have h1 := one_div_le_one_div_of_le hr0 hm'
    have h2 : 1/(r : ℝ)≤aspectOffset r s := by
      unfold aspectOffset
      have hh := div_le_div_of_nonneg_right hs' hr0.le
      have heq : ((r : ℝ)+1)/r=1+1/(r : ℝ) := by
        field_simp
        <;> ring
      rw [heq] at hh
      linarith only [hh]
    exact h1.trans h2
  have hD := D_strictMonoOn.monotoneOn (show (0 : ℝ)≤1/((R : ℝ)+2) by positivity)
    (le_trans (by positivity) hsrcRatio) hsrcRatio
  have hfamily := MulticornerEnergyMinimum.two_nonempty_minimum Finset.univ M
    (fun c _ => hM c) (Finset.mem_univ c) (Finset.mem_univ d) hdc hc hd
  change realEnergy (horizontalStrip 1)+
    realEnergy (horizontalStrip (CornerPrimalDomains.totalDefect M-1))≤_ at hfamily
  rw [hk] at hfamily
  change realEnergy (horizontalStrip j)+D (aspectOffset R S)-D (aspectOffset r s)+fluxBound R S j<_
  rw [hratio]
  linarith only [htest,hD,hfamily]

end
end SpanningTreeIsoperimetry.OddTwoImbalanceTest
