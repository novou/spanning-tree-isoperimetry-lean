import SpanningTreeIsoperimetry.EvenTwoLastRow
import SpanningTreeIsoperimetry.SourceHullArithmetic

/-! Actual selector-two even multicorner exclusions for target deficits3/4. -/
namespace SpanningTreeIsoperimetry.EvenTwoImbalanceExclusion
open Ferrers CornerEnergy CornerPrimalDomains SourceHullArithmetic CanonicalRectangleBounds
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem count_lt_canonical {N t : ℕ} (hN : 0<N) (hT : canonicalIndex N=2)
    (he : minimumSideSum N%2=0) (ht : t<canonicalIndex N)
    (hj : (canonicalParameters N).2.2=3 ∨ (canonicalParameters N).2.2=4)
    (M : Corner → Diagram) (hM : ∀ c,IsFerrers (M c))
    (hcard : totalDefect M=(sourceParameters N t).2.2)
    {c d : Corner} (hdc : d≠c) (hc : (M c).Nonempty) (hd : (M d).Nonempty) :
    treeCount (cornerPrimal ((sourceParameters N t).1-1) ((sourceParameters N t).2.1-1) M)<
      treeCount (canonicalDomain N) := by
  let m := minimumSideSum N/2
  let Δ := m*m-N
  let j := (canonicalParameters N).2.2
  have ht1 : t≤1 := by omega
  have hsrc (t : ℕ) : sourceParameters N t=(m-t,m+t,Δ-t^2) := by
    simp [sourceParameters,m,Δ,he,pow_two]
  have hparam := (source_at_canonical N).symm
  rw [hsrc,hT] at hparam
  have hfeas := (selectorIndex_bounds Δ 0).1
  have hidx : selectorIndex Δ 0=canonicalIndex N := by simp [canonicalIndex,m,Δ,he]
  rw [hidx,hT] at hfeas
  have hjEq : j=Δ-4 := by
    have hh := congrArg (fun p : ℕ×ℕ×ℕ => p.2.2) hparam
    simpa only [j,Prod.snd,show (2 : ℕ)^2=4 by norm_num] using hh
  have hΔ : Δ=j+4 := by omega
  have hsize := canonical_size_relation hN
  change (canonicalIndex N)^2-canonicalIndex N+canonicalIndex N*(minimumSideSum N%2)+j+1≤
    (canonicalParameters N).1 at hsize
  rw [hT,he,hparam] at hsize
  have hm : j+5≤m := by norm_num at hsize; omega
  rw [hsrc] at hcard ⊢
  change totalDefect M=Δ-t^2 at hcard
  change treeCount (cornerPrimal (m-t-1) (m+t-1) M)<treeCount (canonicalDomain N)
  unfold canonicalDomain
  rw [hparam]
  change treeCount (cornerPrimal (m-t-1) (m+t-1) M)<treeCount (cornerStrip (m-2) (m+2) (Δ-4))
  rw [← hjEq]
  change j=3 ∨ j=4 at hj
  rcases hj with hj|hj
  · rw [hj] at hΔ hm ⊢
    rw [hΔ] at hcard
    interval_cases t
    · simpa using EvenTwoFamilyRows.square_seven (by omega : 8≤m) M hM
        (by simpa using hcard) hdc hc hd
    · have hh := EvenTwoFamilyRows.gap_two_six (r := m-1) (by omega : 7≤m-1) M hM
        (by simpa using hcard) hdc hc hd
      have he1 : m-1-1=m-2 := by omega
      have he2 : m-1+2=m+1 := by omega
      have he3 : m-1+3=m+2 := by omega
      simpa only [he1,he2,he3] using hh
  · rw [hj] at hΔ hm ⊢
    rw [hΔ] at hcard
    exact EvenTwoLastRow.count_lt (by omega) ht1 M hM hcard hdc hc hd

end
end SpanningTreeIsoperimetry.EvenTwoImbalanceExclusion
