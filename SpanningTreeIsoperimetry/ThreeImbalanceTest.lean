import SpanningTreeIsoperimetry.ThreeImbalanceScalarChecks
import SpanningTreeIsoperimetry.LargeImbalanceGeometry
import SpanningTreeIsoperimetry.SourceHullArithmetic
import SpanningTreeIsoperimetry.CrossHullCountComparison

/-! Parameter-level multicorner comparison for every canonical imbalance
T=3, with exact actual strip energies and flux envelopes. -/
namespace SpanningTreeIsoperimetry.ThreeImbalanceTest
open Ferrers CornerEnergy FluxBounds AspectCost LargeImbalanceGeometry ThreeImbalanceScalarChecks
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem flux_base_le {R S j a b : ℕ} (ha : 3≤a) (hb : 2≤b)
    (hR : j+a≤R) (hS : j+b≤S) :
    fluxBound R S j≤fluxBound ((j : ℝ)+a) ((j : ℝ)+b) j := by
  have hj := Nat.cast_nonneg (α := ℝ) j
  have haR : (3 : ℝ)≤a := by exact_mod_cast ha
  have hbR : (2 : ℝ)≤b := by exact_mod_cast hb
  have hR' : (j : ℝ)+a≤R := by exact_mod_cast hR
  have hS' : (j : ℝ)+b≤S := by exact_mod_cast hS
  exact (fluxBound_antitone_left (by linarith : (2 : ℝ)<(j : ℝ)+a) hR' hj).trans
    (fluxBound_antitone_right hj (by linarith : (j : ℝ)+1<(j : ℝ)+b) hS')

theorem flux_even_le {R S j l : ℕ} (hR : j+7≤R) (hS : j+13≤S)
    (hjl : j≤l) (hl : l≤6) : fluxBound R S j≤fluxBound ((l : ℝ)+7) ((l : ℝ)+13) l := by
  have hb := flux_base_le (by decide : 3≤7) (by decide : 2≤13) hR hS
  have hm := fluxBound_diagonal_monotone (a := (7 : ℝ)) (b := 13) (by norm_num) (by norm_num)
    (show (j : ℝ)∈Set.Icc 0 (7-1) from ⟨Nat.cast_nonneg _,by norm_num; exact_mod_cast (show j≤6 by omega)⟩)
    (show (l : ℝ)∈Set.Icc 0 (7-1) from ⟨Nat.cast_nonneg _,by norm_num; exact_mod_cast hl⟩)
    (by exact_mod_cast hjl)
  have hm' : fluxBound ((j : ℝ)+7) ((j : ℝ)+13) j≤fluxBound ((l : ℝ)+7) ((l : ℝ)+13) l := by
    simpa only [add_comm] using hm
  exact hb.trans hm'

theorem flux_odd_le {R S j : ℕ} (hR : j+10≤R) (hS : j+17≤S) (hj : j≤7) :
    fluxBound R S j≤fluxBound 17 24 7 := by
  have hb := flux_base_le (by decide : 3≤10) (by decide : 2≤17) hR hS
  have hm := fluxBound_diagonal_monotone (a := (10 : ℝ)) (b := 17) (by norm_num) (by norm_num)
    (show (j : ℝ)∈Set.Icc 0 (10-1) from ⟨Nat.cast_nonneg _,by norm_num; exact_mod_cast (show j≤9 by omega)⟩)
    (show (7 : ℝ)∈Set.Icc 0 (10-1) by norm_num) (by exact_mod_cast hj)
  have hm' : fluxBound ((j : ℝ)+10) ((j : ℝ)+17) j≤fluxBound 17 24 7 := by
    norm_num at hm ⊢
    simpa only [add_comm] using hm
  exact hb.trans hm'

theorem low_aspect_le {R j e : ℕ} (he : e≤1) (hj : j≤3) (hR : j+7+3*e≤R) :
    (6+(e : ℝ))/(R : ℝ)≤6/((j : ℝ)+7) := by
  have hR0 : (0 : ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have hj0 := Nat.cast_nonneg (α := ℝ) j
  have hR' : (j : ℝ)+7+3*e≤R := by exact_mod_cast hR
  have hj' : (j : ℝ)≤3 := by exact_mod_cast hj
  rw [div_le_div_iff₀ hR0 (by positivity : (0 : ℝ)<(j : ℝ)+7)]
  interval_cases e <;> norm_num at hR' ⊢ <;> nlinarith

theorem high_aspect_le {R j e : ℕ} (he : e≤1) (hj : 4≤j) (hR : j+7+3*e≤R) :
    (6+(e : ℝ))/(R : ℝ)≤6/11 := by
  have hR0 : (0 : ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have hR' : (j : ℝ)+7+3*e≤R := by exact_mod_cast hR
  have hj' : (4 : ℝ)≤j := by exact_mod_cast hj
  rw [div_le_div_iff₀ hR0 (by norm_num : (0 : ℝ)<11)]
  interval_cases e <;> norm_num at hR' ⊢ <;> nlinarith

/-- No envelope or analytic estimate is assumed: every scalar comparison
comes from the four checked endpoint inequalities and actual monotonicity. -/
theorem parameter_test {R S j k e : ℕ} (he : e≤1) (hj : j≤6+e)
    (hR : j+7+3*e≤R) (hS : S=R+6+e) (hk : j+5+e≤k) :
    realEnergy (horizontalStrip j)+D ((6+(e : ℝ))/R)+fluxBound R S j<
      realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip (k-1)) := by
  have hR0 : (0 : ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have ha0 : 0≤(6+(e : ℝ))/(R : ℝ) := by positivity
  by_cases hj3 : j≤3
  · have ha := low_aspect_le he hj3 hR
    have hD := D_mono_nonneg ha0 ha
    have hr : j+7≤R := by omega
    have hs : j+13≤S := by omega
    by_cases hj0 : j=0
    · subst j
      have hzero : horizontalStrip 0=(∅ : Diagram) := by decide +kernel
      simp only [hzero,realEnergy_empty,Nat.cast_zero,fluxBound_zero,zero_add]
      have htarget := realEnergy_strip_monotone (show 4≤k-1 by omega)
      norm_num at hD
      linarith [zero_cost]
    · by_cases hj1 : j=1
      · subst j
        have hB := flux_even_le hr hs (le_refl 1) (by decide : 1≤6)
        have htarget := realEnergy_strip_monotone (show 5≤k-1 by omega)
        norm_num at hD hB
        linarith [one_cost]
      · have hj2 : 2≤j := by omega
        have hratio : (6 : ℝ)/((j : ℝ)+7)≤2/3 := by
          rw [div_le_iff₀ (show (0 : ℝ)<(j : ℝ)+7 by positivity)]
          have h : (2 : ℝ)≤j := by exact_mod_cast hj2
          linarith
        have hD' := D_mono_nonneg (show 0≤(6 : ℝ)/((j : ℝ)+7) by positivity) hratio
        have hB := flux_even_le hr hs hj3 (by decide : 3≤6)
        have hE := realEnergy_strip_monotone hj3
        have htarget := realEnergy_strip_monotone (show 6≤k-1 by omega)
        norm_num at hB
        linarith [two_three_cost]
  · have hj4 : 4≤j := by omega
    have hD := D_mono_nonneg ha0 (high_aspect_le he hj4 hR)
    have hB : fluxBound R S j≤fluxBound 13 19 6 := by
      interval_cases e
      · have h := flux_even_le (show j+7≤R by omega) (show j+13≤S by omega)
          (show j≤6 by omega) (le_refl 6)
        norm_num at h
        exact h
      · exact (flux_odd_le (by omega) (by omega) (by omega)).trans odd_flux_below_even.le
    have htarget := realEnergy_strip_monotone (show j≤k-1 by omega)
    linarith [long_cost]

theorem actual_selector_multicorner_test {N t : ℕ} (hN : 0<N)
    (hT : SourceHullArithmetic.canonicalIndex N=3) (ht : t<SourceHullArithmetic.canonicalIndex N)
    (M : CornerPrimalDomains.Corner → Diagram) (hM : ∀ c, IsFerrers (M c))
    (hk : CornerPrimalDomains.totalDefect M=(SourceHullArithmetic.sourceParameters N t).2.2)
    {c d : CornerPrimalDomains.Corner} (hdc : d≠c) (hc : (M c).Nonempty) (hd : (M d).Nonempty) :
    realEnergy (horizontalStrip (canonicalParameters N).2.2)+
      D (CrossHullCountComparison.aspectOffset (canonicalParameters N).1 (canonicalParameters N).2.1)-
      D (CrossHullCountComparison.aspectOffset (SourceHullArithmetic.sourceParameters N t).1
        (SourceHullArithmetic.sourceParameters N t).2.1)+
      fluxBound (canonicalParameters N).1 (canonicalParameters N).2.1 (canonicalParameters N).2.2 <
        ∑ c,realEnergy (M c) := by
  let e := minimumSideSum N%2
  let m := minimumSideSum N/2
  let Δ := m*(m+e)-N
  let R := (canonicalParameters N).1
  let S := (canonicalParameters N).2.1
  let j := (canonicalParameters N).2.2
  let r := (SourceHullArithmetic.sourceParameters N t).1
  let s := (SourceHullArithmetic.sourceParameters N t).2.1
  let k := (SourceHullArithmetic.sourceParameters N t).2.2
  have he : e≤1 := by dsimp [e]; omega
  have htarget := SourceHullArithmetic.source_hull_facts hN (le_refl (SourceHullArithmetic.canonicalIndex N))
  have htargetPos := htarget.short_pos
  rw [SourceHullArithmetic.source_at_canonical] at htargetPos
  have hsource := SourceHullArithmetic.source_hull_facts hN ht.le
  have hsize := CanonicalRectangleBounds.canonical_size_relation hN
  change (SourceHullArithmetic.canonicalIndex N)^2-SourceHullArithmetic.canonicalIndex N+
    SourceHullArithmetic.canonicalIndex N*e+j+1≤R at hsize
  rw [hT] at hsize
  have hR : j+7+3*e≤R := by omega
  have hside := htarget.side_difference
  rw [SourceHullArithmetic.source_at_canonical] at hside
  change S=R+2*SourceHullArithmetic.canonicalIndex N+e at hside
  rw [hT] at hside
  have hS : S=R+6+e := by omega
  have hj0 := selector_remainder_lt_step (selectorIndex_bounds Δ e).1 (selectorIndex_bounds Δ e).2
  change j<2*SourceHullArithmetic.canonicalIndex N+e+1 at hj0
  rw [hT] at hj0
  have hj : j≤6+e := by omega
  have hlower := LargeImbalanceGeometry.source_deficit_lower (selectorIndex_bounds Δ e).1 ht
  change 2*SourceHullArithmetic.canonicalIndex N+e-1+j≤k at hlower
  rw [hT] at hlower
  have hkl : j+5+e≤k := by omega
  have htest := parameter_test he hj hR hS hkl
  have hR0 : (0 : ℝ)<R := by exact_mod_cast htargetPos
  have hratio : CrossHullCountComparison.aspectOffset R S=(6+(e : ℝ))/R := by
    have hh : (S : ℝ)=(R : ℝ)+6+e := by exact_mod_cast hS
    unfold CrossHullCountComparison.aspectOffset
    rw [hh]
    field_simp
    <;> ring
  have hr0 : (0 : ℝ)<r := by exact_mod_cast hsource.short_pos
  have hratio0 : 0≤CrossHullCountComparison.aspectOffset r s := by
    unfold CrossHullCountComparison.aspectOffset
    have hrs : (r : ℝ)≤s := by exact_mod_cast hsource.ordered
    have hle : (1 : ℝ)≤(s : ℝ)/r := (le_div_iff₀ hr0).mpr (by simpa only [one_mul] using hrs)
    linarith
  have hD0 := D_nonneg hratio0
  have hfamily := MulticornerEnergyMinimum.two_nonempty_minimum Finset.univ M
    (fun i _ => hM i) (Finset.mem_univ c) (Finset.mem_univ d) hdc hc hd
  change realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip (CornerPrimalDomains.totalDefect M-1))≤_ at hfamily
  rw [hk] at hfamily
  change realEnergy (horizontalStrip j)+D (CrossHullCountComparison.aspectOffset R S)-
    D (CrossHullCountComparison.aspectOffset r s)+fluxBound R S j<_
  rw [hratio]
  linarith only [htest,hfamily,hD0]

end
end SpanningTreeIsoperimetry.ThreeImbalanceTest
