module

public import SpanningTreeIsoperimetry.AdjacentPairExclusion
public import SpanningTreeIsoperimetry.CanonicalStrips
public import SpanningTreeIsoperimetry.TwoCornerStripTree
public import SpanningTreeIsoperimetry.FiniteGreenMonotonicity

@[expose] public section

/-! Concrete corner-profile normalization and the single-strip count bound. -/
namespace SpanningTreeIsoperimetry.CornerProfileNormalization
open Ferrers CornerEnergy CornerPrimalDomains CornerStripBridge
open DomainIsometries FerrersPrimalBridge StripTreeComparisons
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def opposite (c : Corner) : Corner := reflectCorner (false,false) c
def singleFamily (c : Corner) (A : Diagram) : Corner → Diagram := twoCornerFamily c (opposite c) A ∅

theorem opposite_distinct : ∀ c : Corner, c≠opposite c := by decide +kernel
theorem reflect_opposite (c : Corner) : reflectCorner c (opposite c)=(false,false) := by
  rcases c with ⟨x,y⟩
  cases x <;> cases y <;> rfl

theorem pair_normalization {R S : ℕ} (c : Corner) {A B : Diagram}
    (hA : IsFerrers A) (hB : IsFerrers B) (hR : A.card+B.card≤R) (hS : A.card+B.card≤S) :
    Congruent (cornerPrimal R S (twoCornerFamily c (opposite c) A B))
      (cornerPrimal R S (twoCornerFamily (true,true) (false,false) A B)) := by
  have h := cornerPrimal_reflect_congruent c (pair_family_fit (opposite_distinct c) hA hB hR hS)
  simpa only [reflectedFamily_twoCornerFamily,reflectCorner_self,reflect_opposite] using h

theorem single_normalization {R S : ℕ} (c : Corner) {A : Diagram}
    (hA : IsFerrers A) (hR : A.card≤R) (hS : A.card≤S) :
    Congruent (cornerPrimal R S (singleFamily c A))
      (cornerPrimal R S (singleFamily (true,true) A)) := by
  exact pair_normalization c hA (by intro p hp; exact False.elim (Finset.notMem_empty p hp))
    (by simpa only [Finset.card_empty,add_zero] using hR)
    (by simpa only [Finset.card_empty,add_zero] using hS)

theorem twoCornerFamily_comm (c d : Corner) (hcd : c≠d) (A B : Diagram) :
    twoCornerFamily c d A B=twoCornerFamily d c B A := by
  funext e
  by_cases hc : e=c
  · subst e
    simp [twoCornerFamily,hcd]
  · by_cases hd : e=d
    · subst e
      simp [twoCornerFamily,hcd.symm]
    · simp [twoCornerFamily,hc,hd]

theorem pair_swap {R S : ℕ} {A B : Diagram}
    (hA : IsFerrers A) (hB : IsFerrers B) (hR : A.card+B.card≤R) (hS : A.card+B.card≤S) :
    Congruent (cornerPrimal R S (twoCornerFamily (true,true) (false,false) A B))
      (cornerPrimal R S (twoCornerFamily (true,true) (false,false) B A)) := by
  have h := cornerPrimal_reflect_congruent (false,false)
    (pair_family_fit (by decide : (true,true)≠(false,false)) hA hB hR hS)
  rw [reflectedFamily_twoCornerFamily] at h
  change Congruent (cornerPrimal R S (twoCornerFamily (true,true) (false,false) A B))
    (cornerPrimal R S (twoCornerFamily (false,false) (true,true) A B)) at h
  rw [twoCornerFamily_comm (false,false) (true,true) (by decide) A B] at h
  exact h

theorem vacancies_single (R S : ℕ) (A : Diagram) :
    fourCornerVacancies R S (singleFamily (true,true) A)=A := by
  ext p
  rw [mem_fourCornerVacancies]
  constructor
  · rintro ⟨c,hc⟩
    by_cases he : c=(true,true)
    · subst c
      simpa [placedCorner,singleFamily,twoCornerFamily,cornerMap] using hc
    · simp [singleFamily,twoCornerFamily,he,placedCorner] at hc
  · intro hp
    refine ⟨(true,true),?_⟩
    simpa [placedCorner,singleFamily,twoCornerFamily,cornerMap] using hp

theorem single_primal_eq (R S : ℕ) (A : Diagram) :
    cornerPrimal R S (singleFamily (true,true) A)=primalDomain R S A := by
  rw [cornerPrimal,vacancies_single]

theorem integerFaces_horizontalStrip (k : ℕ) : integerFaces (horizontalStrip k)=rectangle k 1 := by
  have he : horizontalStrip k=faceRectangle k 1 := by
    ext p
    rw [mem_horizontalStrip,mem_faceRectangle]
    omega
  rw [he,integerFaces_faceRectangle]

theorem single_strip_primal (R S k : ℕ) (v : Bool) :
    cornerPrimal R S (singleFamily (true,true) (stripDiagram k v))=
      if v then cornerStrip (R+1) (S+1) k else horizontalCornerStrip (R+1) (S+1) k := by
  rw [single_primal_eq,primalDomain_eq]
  cases v
  · simp only [stripDiagram,Bool.false_eq_true,ite_false,integerFaces_horizontalStrip]
    rfl
  · simp only [stripDiagram,ite_true,integerFaces_verticalDiagram]
    rfl

theorem single_strip_le_canonical {N R S k : ℕ} (hN : 0<N) (hRS : R≤S)
    (hk : k≤R) (harea : (R+1)*(S+1)=N+k)
    (hsum : (R+1)+(S+1)=minimumSideSum N) (c : Corner) (v : Bool) :
    treeCount (cornerPrimal R S (singleFamily c (stripDiagram k v)))≤treeCount (canonicalDomain N) := by
  have hn := single_normalization (R := R) (S := S) c (stripDiagram_ferrers k v)
    (by simpa only [stripDiagram_card] using hk)
    (by simp only [stripDiagram_card]; omega)
  rw [hn.treeCount_eq,single_strip_primal]
  have ho := (CanonicalStrips.canonical_strip_optimal hN).2.2 (R+1) (S+1) k
    (by omega) (by omega) (by omega) harea hsum
  cases v
  · exact ho.2
  · exact ho.1

theorem stripDiagram_one : ∀ v : Bool, stripDiagram 1 v=horizontalStrip 1 := by decide +kernel

def missingFamily (d : Corner) : Corner → Diagram := fun c => if c=d then ∅ else horizontalStrip 1

theorem missingFamily_ferrers (d : Corner) : ∀ c, IsFerrers (missingFamily d c) := by
  intro c
  unfold missingFamily
  split_ifs
  · intro p hp; exact False.elim (Finset.notMem_empty p hp)
  · exact horizontalStrip_isFerrers 1

theorem missingFamily_total : ∀ d : Corner, totalDefect (missingFamily d)=3 := by decide +kernel

theorem reflected_missingFamily : ∀ d : Corner,
    reflectedFamily (opposite d) (missingFamily d)=missingFamily (false,false) := by decide +kernel

theorem triple_normalization {R S : ℕ} (d : Corner) (hR : 3≤R) (hS : 3≤S) :
    Congruent (cornerPrimal R S (missingFamily d))
      (cornerPrimal R S (missingFamily (false,false))) := by
  have hfit : ∀ c, missingFamily d c⊆faceRectangle (R+1) (S+1) := by
    intro c
    exact (ferrers_family_fit (R := R) (S := S) (missingFamily_ferrers d)
      (by simpa only [missingFamily_total] using hR)
      (by simpa only [missingFamily_total] using hS) c).trans
      (FiniteGreenMonotonicity.rectangle_subset (by omega : R≤R+1) (by omega))
  simpa only [reflected_missingFamily] using cornerPrimal_reflect_congruent (opposite d) hfit

end
end SpanningTreeIsoperimetry.CornerProfileNormalization
