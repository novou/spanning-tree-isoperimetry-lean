import SpanningTreeIsoperimetry.MulticornerExclusion
import SpanningTreeIsoperimetry.SingleCornerZeroReduction

/-! The square-hook weak fold cannot preserve global maximality: its target
has two nonempty corner strips, already excluded on every minimum hull. -/
namespace SpanningTreeIsoperimetry.SquareSingleCornerExclusion
open Ferrers CornerEnergy CornerPrimalDomains CornerProfileNormalization StripRigidity
open SingleCornerSmallOrientation SingleCornerSmallReduction
open scoped Classical
noncomputable section

theorem not_isMaximizer {N u : ℕ} {M : Diagram} (hN : 18≤N) (hM : IsFerrers M)
    (hk : M.card≤u) (hn : ¬IsStraightStrip M)
    (harea : (u+1)*(u+1)=N+M.card) (hsum : (u+1)+(u+1)=minimumSideSum N) (c : Corner) :
    ¬IsMaximizer (cornerPrimal u u (singleFamily c M)) := by
  intro hm
  have hsrc : (cornerPrimal u u (singleFamily c M)).card=N := by
    rw [single_card c hM hk hk,harea]
    omega
  obtain ⟨a,b,ha,hb,hab,hmT,hcard⟩ :=
    SingleCornerZeroReduction.square_maximizer_transfer hM hk hn c hm
  have htarget : (cornerPrimal (u-1) (u+1)
      (twoCornerFamily (false,true) (true,false) (horizontalStrip a) (horizontalStrip b))).card=N :=
    hcard.trans hsrc
  have hcd : (false,true)≠(true,false) := by decide
  have hF := twoCornerFamily_ferrers (false,true) (true,false)
    (horizontalStrip_isFerrers a) (horizontalStrip_isFerrers b)
  have htotal : totalDefect (twoCornerFamily (false,true) (true,false)
      (horizontalStrip a) (horizontalStrip b))=a+b := by
    rw [totalDefect_twoCornerFamily hcd,card_horizontalStrip,card_horizontalStrip]
  have hR : totalDefect (twoCornerFamily (false,true) (true,false)
      (horizontalStrip a) (horizontalStrip b))≤u-1 := by omega
  have hS : totalDefect (twoCornerFamily (false,true) (true,false)
      (horizontalStrip a) (horizontalStrip b))≤u+1 := by omega
  rw [cornerPrimal_card hF hR hS,htotal,Nat.sub_add_cancel (by omega : 1≤u)] at htarget
  change u*(u+2)-(a+b)=N at htarget
  have hprod : a+b≤u*(u+2) := by nlinarith
  have hareaT : u*(u+2)=N+(a+b) := by omega
  have hna : (horizontalStrip a).Nonempty := by
    apply Finset.card_pos.mp
    rwa [card_horizontalStrip]
  have hnb : (horizontalStrip b).Nonempty := by
    apply Finset.card_pos.mp
    rwa [card_horizontalStrip]
  have hnT := MulticornerExclusion.not_isMaximizer hN (by omega : u≤u+2)
    (by omega : a+b<u) hareaT (by omega : u+(u+2)=minimumSideSum N)
    (twoCornerFamily (false,true) (true,false) (horizontalStrip a) (horizontalStrip b)) hF htotal hcd
    (by simpa [twoCornerFamily] using hna) (by simpa [twoCornerFamily] using hnb)
  have he : u+2-1=u+1 := by omega
  rw [he] at hnT
  exact hnT hmT

end
end SpanningTreeIsoperimetry.SquareSingleCornerExclusion
