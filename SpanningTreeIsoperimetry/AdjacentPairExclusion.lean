module

public import SpanningTreeIsoperimetry.CornerSeparationTree
public import SpanningTreeIsoperimetry.CornerPrimalSymmetry

@[expose] public section

/-! Two nonempty Ferrers corners of a maximizer must be opposite. Reflections
and coordinate exchange discharge all placements of the adjacent pair. -/
namespace SpanningTreeIsoperimetry.CornerPrimalDomains
open Ferrers CornerEnergy
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem adjacentPrimal_not_isMaximizer {R S : ℕ} {A B : Diagram}
    (hA : IsFerrers A) (hB : IsFerrers B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hR : A.card+B.card≤R) (hS : A.card+B.card≤S) :
    ¬IsMaximizer (adjacentPrimal R S A B) := by
  intro hmax
  have hg := separate_corners_geometry A B hA hB hR hS
  have hstrict := separate_corners_treeCount A B hA hB hneA hneB hR hS
  have hle := hmax.2 (oppositePrimal R S A B) hg.1.symm hg.2.2.1
  omega

theorem pair_family_fit {R S : ℕ} {A B : Diagram} {c d : Corner} (hcd : c≠d)
    (hA : IsFerrers A) (hB : IsFerrers B) (hR : A.card+B.card≤R) (hS : A.card+B.card≤S) :
    ∀ e, twoCornerFamily c d A B e⊆faceRectangle (R+1) (S+1) := by
  intro e
  have htotal := totalDefect_twoCornerFamily hcd A B
  have he : (twoCornerFamily c d A B e).card≤A.card+B.card := by
    rw [← htotal]
    exact Finset.single_le_sum (fun f _ => Nat.zero_le (twoCornerFamily c d A B f).card)
      (Finset.mem_univ e)
  exact ferrers_fit_of_card (twoCornerFamily_ferrers c d hA hB e) (by omega) (by omega)

theorem reflectCorner_self (c : Corner) : reflectCorner c c=(true,true) := by
  rcases c with ⟨x,y⟩
  cases x <;> cases y <;> rfl

theorem adjacent_normal_forms : ∀ c d : Corner,
    c≠d → d≠reflectCorner (false,false) c →
      reflectCorner c d=(false,true) ∨ reflectCorner c d=(true,false) := by
  decide +kernel

theorem pair_maximizer_opposite {R S : ℕ} {A B : Diagram} {c d : Corner}
    (hcd : c≠d) (hA : IsFerrers A) (hB : IsFerrers B)
    (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hR : A.card+B.card≤R) (hS : A.card+B.card≤S)
    (hmax : IsMaximizer (cornerPrimal R S (twoCornerFamily c d A B))) :
    d=reflectCorner (false,false) c := by
  by_contra hnot
  have hcongr := cornerPrimal_reflect_congruent c (pair_family_fit hcd hA hB hR hS)
  have hnormal : IsMaximizer (cornerPrimal R S
      (twoCornerFamily (true,true) (reflectCorner c d) A B)) := by
    simpa only [reflectedFamily_twoCornerFamily,reflectCorner_self] using
      hcongr.isMaximizer_iff.mp hmax
  rcases adjacent_normal_forms c d hcd hnot with hd|hd
  · rw [hd] at hnormal
    exact adjacentPrimal_not_isMaximizer hA hB hneA hneB hR hS hnormal
  · rw [hd] at hnormal
    have hfit := pair_family_fit (by decide : (true,true)≠(true,false)) hA hB hR hS
    have htranspose := (cornerPrimal_transpose_congruent hfit).isMaximizer_iff.mp hnormal
    rw [transposedFamily_twoCornerFamily] at htranspose
    have hna : (transpose A).Nonempty := by simpa only [transpose] using hneA.image Prod.swap
    have hnb : (transpose B).Nonempty := by simpa only [transpose] using hneB.image Prod.swap
    exact adjacentPrimal_not_isMaximizer (transpose_isFerrers hA) (transpose_isFerrers hB)
      hna hnb (by simpa only [card_transpose] using hS)
      (by simpa only [card_transpose] using hR) htranspose

end
end SpanningTreeIsoperimetry.CornerPrimalDomains
