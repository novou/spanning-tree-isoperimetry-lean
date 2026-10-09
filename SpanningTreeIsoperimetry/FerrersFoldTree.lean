import SpanningTreeIsoperimetry.CornerSeparationTree
import SpanningTreeIsoperimetry.FerrersFoldHook

/-! Maximal-block Ferrers folds as actual primal spanning-tree comparisons. -/
namespace SpanningTreeIsoperimetry.CornerPrimalDomains

open Ferrers CornerEnergy CornerFolds StripPolarization Polarization
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def ferrersSourcePrimal (u v : ℕ) (M : Diagram) : Domain :=
  cornerPrimal u v (twoCornerFamily (false,true) (true,false) M ∅)

def ferrersTargetPrimal (u v t : ℕ) (M : Diagram) : Domain :=
  cornerPrimal (u-t) (v+t) (twoCornerFamily (false,true) (true,false)
    (ferrersTailX M t) (transpose (ferrersTailY M (v-u+t))))

theorem empty_ferrers : IsFerrers (∅ : Diagram) := by
  intro p hp
  exact False.elim (Finset.notMem_empty p hp)

theorem ferrersSource_count {u v : ℕ} {M : Diagram} (hu : 1≤u) (huv : u≤v)
    (hM : IsFerrers M) (hk : M.card≤u) :
    (treeCount (ferrersSourcePrimal u v M) : ℝ)=
      faceDeterminant (rectangle u v \ bottomRightDefect u M) 4 := by
  have ht := totalDefect_twoCornerFamily (by decide : (false,true)≠(true,false)) M ∅
  simp only [Finset.card_empty,Nat.add_zero] at ht
  have h := cornerPrimal_treeCount_eq_faceDeterminant (R := u) (S := v) hu (by omega)
    (twoCornerFamily_ferrers (false,true) (true,false) hM empty_ferrers) (by omega) (by omega)
  rw [cornerFaceDomain_BR_TL (R := u) (S := v) hu (by omega) M ∅ (ferrers_fit_of_card (R := u) (S := v) hM hk (by omega))
    (Finset.empty_subset _)] at h
  have he : topLeftDefect v ∅=∅ := by simp [topLeftDefect,DomainIsometries.integerFaces]
  simpa only [he,Finset.union_empty,ferrersSourcePrimal] using h

/-- Maximal-block membership supplies both the exact remaining deficit and
its strict-short-side bound; no geometric decomposition is assumed. -/
theorem ferrers_fold_tail_bounds {u v t : ℕ} {M : Diagram} (hM : IsFerrers M)
    (hk : M.card≤u) (ht0 : 0<t) (hcorner : (t-1,v-u+t-1)∈M)
    (hsplit : ∀ p∈M, p.1<t ∨ p.2<v-u+t) :
    (ferrersTailX M t).card+(transpose (ferrersTailY M (v-u+t))).card=M.card-t*(v-u+t) ∧
    M.card-t*(v-u+t)≤u-t ∧ t*(v-u+t)≤M.card := by
  have hc : 0<v-u+t := by omega
  have hblock : (Finset.range t ×ˢ Finset.range (v-u+t))⊆M := by
    intro p hp
    have hb := Finset.mem_product.mp hp
    simp only [Finset.mem_range] at hb
    exact hM _ hcorner p (by omega) (by omega)
  have hbcard := Finset.card_le_card hblock
  simp only [Finset.card_product,Finset.card_range] at hbcard
  have htc : t≤t*(v-u+t) := by nlinarith
  refine ⟨?_,by omega,hbcard⟩
  rw [card_transpose]
  exact ferrers_tails_card hblock hsplit

theorem ferrersTarget_count {u v t : ℕ} {M : Diagram} (huv : u≤v) (ht0 : 0<t) (ht : t<u)
    (hM : IsFerrers M) (hk : M.card≤u) (hcorner : (t-1,v-u+t-1)∈M)
    (hsplit : ∀ p∈M, p.1<t ∨ p.2<v-u+t) :
    (treeCount (ferrersTargetPrimal u v t M) : ℝ)=faceDeterminant (ferrersFoldCandidate u v t M) 4 := by
  have hb := ferrers_fold_tail_bounds hM hk ht0 hcorner hsplit
  have hA := ferrersTailX_isFerrers hM t
  have hB := transpose_isFerrers (ferrersTailY_isFerrers hM (v-u+t))
  have hsum := totalDefect_twoCornerFamily (by decide : (false,true)≠(true,false))
    (ferrersTailX M t) (transpose (ferrersTailY M (v-u+t)))
  have h := cornerPrimal_treeCount_eq_faceDeterminant (show 1≤u-t by omega) (show 1≤v+t by omega)
    (twoCornerFamily_ferrers (false,true) (true,false) hA hB) (by omega) (by omega)
  rw [cornerFaceDomain_BR_TL (R := u-t) (S := v+t) (by omega) (by omega) _ _
    (ferrers_fit_of_card hA (by omega) (by omega))
    (ferrers_fit_of_card hB (by omega) (by omega))] at h
  rw [← ferrersFoldCandidate_eq_two_corners M huv (by omega)] at h
  exact h

theorem ferrers_fold_cardinality {u v t : ℕ} {M : Diagram} (huv : u≤v) (ht0 : 0<t) (ht : t<u)
    (hM : IsFerrers M) (hk : M.card≤u) (hcorner : (t-1,v-u+t-1)∈M)
    (hsplit : ∀ p∈M, p.1<t ∨ p.2<v-u+t) :
    (ferrersSourcePrimal u v M).card=(ferrersTargetPrimal u v t M).card := by
  have hb := ferrers_fold_tail_bounds hM hk ht0 hcorner hsplit
  have hA := ferrersTailX_isFerrers hM t
  have hB := transpose_isFerrers (ferrersTailY_isFerrers hM (v-u+t))
  have hsumSource := totalDefect_twoCornerFamily (by decide : (false,true)≠(true,false)) M ∅
  simp only [Finset.card_empty,Nat.add_zero] at hsumSource
  have hsumTarget := totalDefect_twoCornerFamily (by decide : (false,true)≠(true,false))
    (ferrersTailX M t) (transpose (ferrersTailY M (v-u+t)))
  rw [ferrersSourcePrimal,ferrersTargetPrimal,
    cornerPrimal_card (twoCornerFamily_ferrers _ _ hM empty_ferrers) (by omega) (by omega),
    cornerPrimal_card (twoCornerFamily_ferrers _ _ hA hB) (by omega) (by omega),
    hsumSource,hsumTarget,hb.1]
  have hut : u-t+t=u := Nat.sub_add_cancel (by omega)
  have hvu : v-u+u=v := Nat.sub_add_cancel huv
  have harea : ((u-t)+1)*((v+t)+1)+t*(v-u+t)=(u+1)*(v+1) := by nlinarith
  omega

/-- Actual comparison for the geometrically selected maximal block. -/
theorem ferrers_fold_treeCount {u v t : ℕ} {M : Diagram} (huv : u≤v) (ht0 : 0<t) (ht : t<u)
    (hM : IsFerrers M) (hk : M.card≤u) (hcorner : (t-1,v-u+t-1)∈M)
    (hsplit : ∀ p∈M, p.1<t ∨ p.2<v-u+t) :
    treeCount (ferrersSourcePrimal u v M)≤treeCount (ferrersTargetPrimal u v t M) := by
  have hs := ferrersSource_count (by omega) huv hM hk
  have ht' := ferrersTarget_count huv ht0 ht hM hk hcorner hsplit
  have h := shiftedDiagonal_lower_determinant (ferrersFoldCandidate u v t M) (v-u+t : ℕ) 4 le_rfl
  rw [polarize_ferrersFoldCandidate hM huv ht0 ht.le hcorner hsplit,← hs,← ht'] at h
  exact_mod_cast h

/-- The manuscript Ferrers fold, with the maximal block constructed and all
actual primal connectivity, cardinality and hull conclusions discharged. -/
theorem exists_ferrers_primal_fold {u v : ℕ} {M : Diagram} (hM : IsFerrers M)
    (huv : u≤v) (hk : M.card≤u) (hheight : v-u<ferrersHeight M)
    (hnotX : M≠horizontalStrip M.card) (hnotY : M≠transpose (horizontalStrip M.card)) :
    ∃ t : ℕ, 0<t ∧ t<u ∧
      (ferrersSourcePrimal u v M).card=(ferrersTargetPrimal u v t M).card ∧
      (domainGraph (ferrersTargetPrimal u v t M)).Connected ∧
      SquareMaximality.IsRectHull (ferrersTargetPrimal u v t M) 0 0 (u-t+1) (v+t+1) ∧
      treeCount (ferrersSourcePrimal u v M)≤treeCount (ferrersTargetPrimal u v t M) ∧
      ((u=v ∧ IsFerrersHook M ∧ t=1 ∧
        ferrersTargetPrimal u v t M=cornerPrimal (u-1) (v+1)
          (twoCornerFamily (false,true) (true,false)
            (horizontalStrip (ferrersWidth M-1)) (horizontalStrip (ferrersHeight M-1)))) ∨
        treeCount (ferrersSourcePrimal u v M)<treeCount (ferrersTargetPrimal u v t M)) := by
  have hext := ferrers_nonstrip_extents hM hnotX hnotY
  obtain ⟨t,ht0,ht,hcorner,hsplit,halt⟩ := exists_ferrers_fold_strict_alternative hM huv hk
    ((ferrers_height_cell_iff hM (v-u)).mpr hheight) hext.1 hext.2
  have hb := ferrers_fold_tail_bounds hM hk ht0 hcorner hsplit
  have hA := ferrersTailX_isFerrers hM t
  have hB := transpose_isFerrers (ferrersTailY_isFerrers hM (v-u+t))
  have hsum := totalDefect_twoCornerFamily (by decide : (false,true)≠(true,false))
    (ferrersTailX M t) (transpose (ferrersTailY M (v-u+t)))
  refine ⟨t,ht0,ht,ferrers_fold_cardinality huv ht0 ht hM hk hcorner hsplit,
    cornerPrimal_connected (twoCornerFamily_ferrers _ _ hA hB) (by omega),
    cornerPrimal_hull (by omega) (by omega),ferrers_fold_treeCount huv ht0 ht hM hk hcorner hsplit,?_⟩
  rcases halt with ⟨heq,hHook,ht1,hX,hY⟩ | hstrict
  · left
    refine ⟨heq,hHook,ht1,?_⟩
    unfold ferrersTargetPrimal
    rw [hX,hY,ht1]
  · right
    have h := hstrict 4 le_rfl
    rw [← ferrersSource_count (by omega) huv hM hk,
      ← ferrersTarget_count huv ht0 ht hM hk hcorner hsplit] at h
    exact_mod_cast h

end
end SpanningTreeIsoperimetry.CornerPrimalDomains
