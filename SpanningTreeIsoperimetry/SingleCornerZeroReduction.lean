module

public import SpanningTreeIsoperimetry.SingleCornerSmallReduction
public import SpanningTreeIsoperimetry.SourceHullArithmetic

@[expose] public section

/-! The zero source index: odd side sum is strictly improvable; square
hooks transfer maximality to a literal pair of nonempty opposite strips. -/
namespace SpanningTreeIsoperimetry.SingleCornerZeroReduction
open Ferrers CornerFolds CornerPrimalDomains CornerProfileNormalization StripRigidity
open SingleCornerSmallReduction SourceHullArithmetic
noncomputable section

theorem square_maximizer_transfer {u : ℕ} {M : Diagram} (hM : IsFerrers M)
    (hk : M.card≤u) (hn : ¬IsStraightStrip M) (c : Corner)
    (hmax : IsMaximizer (cornerPrimal u u (singleFamily c M))) :
    ∃ a b : ℕ, 0<a ∧ 0<b ∧ a+b≤u-1 ∧
      IsMaximizer (cornerPrimal (u-1) (u+1)
        (twoCornerFamily (false,true) (true,false) (horizontalStrip a) (horizontalStrip b))) ∧
      (cornerPrimal (u-1) (u+1)
        (twoCornerFamily (false,true) (true,false) (horizontalStrip a) (horizontalStrip b))).card=
        (cornerPrimal u u (singleFamily c M)).card := by
  have hh := height_gt_gap_of_le_one hM hn (u := u) (v := u) (by omega)
  obtain ⟨t,ht0,htu,hcard,hconn,hhull,hcount,halt⟩ := tall_fold_alternative hM le_rfl hk hn hh c
  rcases halt with ⟨_,_,_,a,b,ha,hb,hab,heq⟩|hstrict
  · have hm := maximality_transfer hmax hcard.symm hconn hcount
    rw [heq] at hm hcard
    exact ⟨a,b,ha,hb,hab,hm,hcard.symm⟩
  · exact False.elim ((not_lt_of_ge (hmax.2 _ hcard.symm hconn)) hstrict)

theorem zero_odd_not_maximal {N : ℕ} (hN : 0<N) (he : minimumSideSum N%2=1)
    {M : Diagram} (hM : IsFerrers M) (hn : ¬IsStraightStrip M)
    (hk : M.card=(sourceParameters N 0).2.2) (c : Corner) :
    ¬IsMaximizer (cornerPrimal ((sourceParameters N 0).1-1) ((sourceParameters N 0).2.1-1)
      (singleFamily c M)) := by
  have hf := source_hull_facts hN (Nat.zero_le _)
  have hs := hf.side_difference
  rw [he] at hs
  norm_num at hs
  have hshort : M.card≤(sourceParameters N 0).1-1 := by
    rw [hk]
    have hh := hf.deficit_lt_short
    omega
  have hp := hf.short_pos
  apply tall_nonsquare_not_maximal hM (by omega) hshort hn
  exact height_gt_gap_of_le_one hM hn (by omega)

end
end SpanningTreeIsoperimetry.SingleCornerZeroReduction
