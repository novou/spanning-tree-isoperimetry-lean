import SpanningTreeIsoperimetry.SingleCornerSmallOrientation
import SpanningTreeIsoperimetry.SmallShapeCatalogue
import SpanningTreeIsoperimetry.LatticeCongruenceExtra

/-! Actual strict single-corner improvements and the sole square-hook
alternative, including shallow two-row transposition followed by a fold. -/
namespace SpanningTreeIsoperimetry.SingleCornerSmallReduction

open Ferrers CornerEnergy CornerFolds CornerPrimalDomains CornerProfileNormalization
open SingleCornerSmallOrientation StripRigidity
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem single_congruent_fold_source {u v : ℕ} {M : Diagram} (hM : IsFerrers M)
    (hu : M.card≤u) (hv : M.card≤v) (c : Corner) :
    Congruent (cornerPrimal u v (singleFamily c M)) (ferrersSourcePrimal u v M) := by
  have h := (single_normalization c hM hu hv).trans
    (single_normalization (false,true) hM hu hv).symm
  simpa [ferrersSourcePrimal,singleFamily,opposite,reflectCorner] using h

private theorem hook_tail_bounds {u : ℕ} {M : Diagram} (hM : IsFerrers M)
    (hk : M.card≤u) (hn : ¬IsStraightStrip M) :
    0<ferrersWidth M-1 ∧ 0<ferrersHeight M-1 ∧
      (ferrersWidth M-1)+(ferrersHeight M-1)≤u-1 := by
  have he := ferrers_nonstrip_extents hM (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h))
  have hne := nonempty_of_not_straight hn
  have hw := ferrers_width_corner hM hne
  have hh := ferrers_height_corner hM hne
  have hz : (0,0)∈M := hM _ hw (0,0) (Nat.zero_le _) le_rfl
  have hb := ferrers_axes_block_card (p := ferrersWidth M) (q := ferrersHeight M) (t := 1) (c := 1)
    hM (by omega) (by omega) (by omega) (by omega) hw hh (by simpa using hz)
  norm_num at hb
  omega

/-- All corner placements inherit the constructed maximal-block fold.
The weak alternative is a literal pair of nonempty opposite strips. -/
theorem tall_fold_alternative {u v : ℕ} {M : Diagram} (hM : IsFerrers M)
    (huv : u≤v) (hk : M.card≤u) (hn : ¬IsStraightStrip M)
    (hh : v-u<ferrersHeight M) (c : Corner) :
    ∃ t : ℕ, 0<t ∧ t<u ∧
      (cornerPrimal u v (singleFamily c M)).card=(ferrersTargetPrimal u v t M).card ∧
      (domainGraph (ferrersTargetPrimal u v t M)).Connected ∧
      SquareMaximality.IsRectHull (ferrersTargetPrimal u v t M) 0 0 (u-t+1) (v+t+1) ∧
      treeCount (cornerPrimal u v (singleFamily c M))≤treeCount (ferrersTargetPrimal u v t M) ∧
      ((u=v ∧ IsFerrersHook M ∧ t=1 ∧
        ∃ a b : ℕ, 0<a ∧ 0<b ∧ a+b≤u-1 ∧
          ferrersTargetPrimal u v t M=cornerPrimal (u-1) (v+1)
            (twoCornerFamily (false,true) (true,false) (horizontalStrip a) (horizontalStrip b))) ∨
       treeCount (cornerPrimal u v (singleFamily c M))<treeCount (ferrersTargetPrimal u v t M)) := by
  have hnorm := single_congruent_fold_source hM hk (hk.trans huv) c
  obtain ⟨t,ht0,htu,hcard,hconn,hhull,hcount,halt⟩ := exists_ferrers_primal_fold hM huv hk hh
    (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h))
  refine ⟨t,ht0,htu,hnorm.card_eq.trans hcard,hconn,hhull,?_,?_⟩
  · rw [hnorm.treeCount_eq]
    exact hcount
  · rcases halt with ⟨he,hHook,ht,heq⟩ | hs
    · have hb := hook_tail_bounds hM hk hn
      exact Or.inl ⟨he,hHook,ht,ferrersWidth M-1,ferrersHeight M-1,hb.1,hb.2.1,hb.2.2,heq⟩
    · right
      rw [hnorm.treeCount_eq]
      exact hs

theorem exists_strict_tall_improvement {u v : ℕ} {M : Diagram} (hM : IsFerrers M)
    (huv : u<v) (hk : M.card≤u) (hn : ¬IsStraightStrip M)
    (hh : v-u<ferrersHeight M) (c : Corner) :
    ∃ B : Domain, B.card=(cornerPrimal u v (singleFamily c M)).card ∧
      (domainGraph B).Connected ∧ treeCount (cornerPrimal u v (singleFamily c M))<treeCount B := by
  obtain ⟨t,ht0,htu,hcard,hconn,hhull,hcount,halt⟩ := tall_fold_alternative hM huv.le hk hn hh c
  refine ⟨ferrersTargetPrimal u v t M,hcard.symm,hconn,?_⟩
  rcases halt with h|h
  · omega
  · exact h

theorem tall_nonsquare_not_maximal {u v : ℕ} {M : Diagram} (hM : IsFerrers M)
    (huv : u<v) (hk : M.card≤u) (hn : ¬IsStraightStrip M)
    (hh : v-u<ferrersHeight M) (c : Corner) :
    ¬IsMaximizer (cornerPrimal u v (singleFamily c M)) := by
  obtain ⟨B,hcard,hconn,hstrict⟩ := exists_strict_tall_improvement hM huv hk hn hh c
  intro hm
  have h := hm.2 B hcard hconn
  omega

/-- A shallow two-row corner whose width crosses the hull gap first
transposes without loss, then has a strict actual fold. -/
theorem two_row_wide_not_maximal {u v : ℕ} {M : Diagram} (hM : IsFerrers M)
    (huv : u<v) (hk : M.card≤u) (hn : ¬IsStraightStrip M)
    (hh : ferrersHeight M≤2) (hw : v-u<ferrersWidth M) (c : Corner) :
    ¬IsMaximizer (cornerPrimal u v (singleFamily c M)) := by
  have hne := nonempty_of_not_straight hn
  have hc := Finset.card_pos.mpr hne
  have hu : 1≤u := by omega
  have hor := two_row_transpose_treeCount hu huv.le hM hk hn hh c
  have hMt := transpose_isFerrers hM
  have hkt : (transpose M).card≤u := by simpa only [card_transpose] using hk
  have hht : v-u<ferrersHeight (transpose M) := by rw [transpose_height]; exact hw
  obtain ⟨B,hcard,hconn,hstrict⟩ := exists_strict_tall_improvement hMt huv hkt (transpose_nonstrip hn) hht c
  have hsame : (cornerPrimal u v (singleFamily c (transpose M))).card=
      (cornerPrimal u v (singleFamily c M)).card := by
    rw [single_card c hMt hkt (hkt.trans huv.le),single_card c hM hk (hk.trans huv.le),card_transpose]
  intro hm
  have h := hm.2 B (hcard.trans hsame) hconn
  exact (not_lt_of_ge h) (hor.trans_lt hstrict)

theorem two_row_large_not_maximal {u v : ℕ} {M : Diagram} (hM : IsFerrers M)
    (huv : u<v) (hk : M.card≤u) (hn : ¬IsStraightStrip M)
    (hh : ferrersHeight M≤2) (hsize : 2*(v-u)<M.card) (c : Corner) :
    ¬IsMaximizer (cornerPrimal u v (singleFamily c M)) :=
  two_row_wide_not_maximal hM huv hk hn hh (width_gt_of_two_rows hh hsize) c

/-- The only nonstrips inside the two-by-two box are L and the full square. -/
theorem two_by_two_catalogue {M : Diagram} (hM : IsFerrers M) (hn : ¬IsStraightStrip M)
    (hh : ferrersHeight M≤2) (hw : ferrersWidth M≤2) :
    M=threeCell ∨ M=faceRectangle 2 2 := by
  have hsub : M⊆faceRectangle 2 2 := by
    intro p hp
    have h := ferrers_extent_bounds hp
    exact mem_faceRectangle.mpr ⟨by omega,by omega⟩
  by_cases hk : M.card≤3
  · rcases SmallShapeCatalogue.ferrers_three_cell_catalogue hM hk with hs|he
    · exact False.elim (hn hs)
    · exact Or.inl he
  · right
    apply Finset.eq_of_subset_of_card_le hsub
    have h := Finset.card_le_card hsub
    norm_num [faceRectangle] at h ⊢
    omega

/-- Exhaustive shallow gap-two reduction: every other two-row nonstrip has
an actual strict improvement. -/
theorem gap_two_cases {u v : ℕ} {M : Diagram} (hM : IsFerrers M) (hk : M.card≤u)
    (hn : ¬IsStraightStrip M) (hh : ferrersHeight M≤2) (hgap : v-u=2) (c : Corner) :
    ¬IsMaximizer (cornerPrimal u v (singleFamily c M)) ∨ M=threeCell ∨ M=faceRectangle 2 2 := by
  by_cases hw : 2<ferrersWidth M
  · left
    exact two_row_wide_not_maximal hM (by omega) hk hn hh (by omega) c
  · right
    exact two_by_two_catalogue hM hn hh (by omega)

theorem height_gt_gap_of_le_one {u v : ℕ} {M : Diagram} (hM : IsFerrers M)
    (hn : ¬IsStraightStrip M) (hgap : v-u≤1) : v-u<ferrersHeight M := by
  have h := ferrers_nonstrip_extents hM (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h))
  omega

/-- A weak same-cardinality improvement of a maximizer is itself a maximizer. -/
theorem maximality_transfer {A B : Domain} (hA : IsMaximizer A) (hcard : B.card=A.card)
    (hconn : (domainGraph B).Connected) (hcount : treeCount A≤treeCount B) : IsMaximizer B := by
  refine ⟨hconn,?_⟩
  intro T hT hconnT
  exact (hA.2 T (hT.trans hcard) hconnT).trans hcount

end
end SpanningTreeIsoperimetry.SingleCornerSmallReduction
