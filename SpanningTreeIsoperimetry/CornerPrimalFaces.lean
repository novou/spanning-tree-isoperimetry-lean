import SpanningTreeIsoperimetry.CornerPrimalDomains
import SpanningTreeIsoperimetry.FerrersFold

/-! The marked faces of actual four-corner primal vacancies are exactly the
same Ferrers diagrams placed in the smaller face rectangle. -/
namespace SpanningTreeIsoperimetry.CornerPrimalDomains

open Ferrers CornerEnergy DomainIsometries SquareMaximality.Boundary
open FerrersPrimalBridge RowConvexPrimal CornerFolds StripPolarization
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem markedFaces_placedCorner {R S : ℕ} (c : Corner) {M : Diagram}
    (hM : IsFerrers M) (hfit : M⊆faceRectangle R S) :
    markedFaces R S (placedCorner R S c M)=placedCorner (R-1) (S-1) c M := by
  ext z
  constructor
  · intro hz
    obtain ⟨hx,hy,w,hw,hxw,hwx,hyw,hwy⟩ := mem_markedFaces.mp hz
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hw
    have hp' := mem_faceRectangle.mp (hfit hp)
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    have hless : (cornerMap (R-1) (S-1) c z).1≤p.1 ∧
        (cornerMap (R-1) (S-1) c z).2≤p.2 := by
      rcases c with ⟨cx,cy⟩
      cases cx <;> cases cy <;>
        simp only [cornerMap, Bool.false_eq_true, ↓reduceIte] at he1 he2 ⊢ <;> omega
    apply Finset.mem_image.mpr
    exact ⟨cornerMap (R-1) (S-1) c z,hM p hp _ hless.1 hless.2,
      cornerMap_involutive c (by omega) (by omega)⟩
  · intro hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    have hp' := mem_faceRectangle.mp (hfit hp)
    apply mem_markedFaces.mpr
    refine ⟨?_,?_,cornerMap R S c p,Finset.mem_image.mpr ⟨p,hp,rfl⟩,?_,?_,?_,?_⟩ <;>
      rcases c with ⟨cx,cy⟩ <;> cases cx <;> cases cy <;>
      simp only [cornerMap, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem markedFaces_fourCorners {R S : ℕ} {M : Corner → Diagram}
    (hM : ∀ c, IsFerrers (M c)) (hfit : ∀ c, M c⊆faceRectangle R S) :
    markedFaces R S (fourCornerVacancies R S M)=fourCornerVacancies (R-1) (S-1) M := by
  ext z
  constructor
  · intro hz
    obtain ⟨hx,hy,w,hw,hxw,hwx,hyw,hwy⟩ := mem_markedFaces.mp hz
    obtain ⟨c,hc⟩ := mem_fourCornerVacancies.mp hw
    have hm : z∈markedFaces R S (placedCorner R S c (M c)) :=
      mem_markedFaces.mpr ⟨hx,hy,w,hc,hxw,hwx,hyw,hwy⟩
    rw [markedFaces_placedCorner c (hM c) (hfit c)] at hm
    exact mem_fourCornerVacancies.mpr ⟨c,hm⟩
  · intro hz
    obtain ⟨c,hc⟩ := mem_fourCornerVacancies.mp hz
    rw [← markedFaces_placedCorner c (hM c) (hfit c)] at hc
    obtain ⟨hx,hy,w,hw,hxw,hwx,hyw,hwy⟩ := mem_markedFaces.mp hc
    exact mem_markedFaces.mpr ⟨hx,hy,w,mem_fourCornerVacancies.mpr ⟨c,hw⟩,hxw,hwx,hyw,hwy⟩

def cornerFaceDomain (R S : ℕ) (M : Corner → Diagram) : Domain :=
  integerFaces (faceRectangle R S \ fourCornerVacancies (R-1) (S-1) M)

theorem cornerPrimal_connected {R S : ℕ} {M : Corner → Diagram}
    (hM : ∀ c, IsFerrers (M c)) (hR : totalDefect M≤R) :
    (domainGraph (cornerPrimal R S M)).Connected :=
  RowConvexPrimal.primal_connected (fourCorner_rowConvex R S hM) ((fourCorner_card_le R S M).trans hR)

theorem cornerPrimal_hull {R S : ℕ} {M : Corner → Diagram}
    (hR : totalDefect M≤R) (hS : totalDefect M≤S) :
    SquareMaximality.IsRectHull (cornerPrimal R S M) 0 0 (R+1) (S+1) :=
  RowConvexPrimal.primal_hull ((fourCorner_card_le R S M).trans hR) ((fourCorner_card_le R S M).trans hS)

theorem cornerPrimal_card {R S : ℕ} {M : Corner → Diagram}
    (hM : ∀ c, IsFerrers (M c)) (hR : totalDefect M≤R) (hS : totalDefect M≤S) :
    (cornerPrimal R S M).card=(R+1)*(S+1)-totalDefect M := by
  have hfit : fourCornerVacancies R S M⊆faceRectangle (R+1) (S+1) := by
    apply fourCorner_subset
    intro c p hp
    have h := mem_faceRectangle.mp (ferrers_family_fit hM hR hS c hp)
    exact mem_faceRectangle.mpr ⟨by omega,by omega⟩
  rw [cornerPrimal,RowConvexPrimal.primal_card hfit,fourCorner_card hM hR hS]

/-- Actual primal count, literal integer face set, all geometry discharged. -/
theorem cornerPrimal_treeCount_eq_faceDeterminant {R S : ℕ} {M : Corner → Diagram}
    (hR0 : 1≤R) (hS0 : 1≤S) (hM : ∀ c, IsFerrers (M c))
    (hR : totalDefect M≤R) (hS : totalDefect M≤S) :
    (treeCount (cornerPrimal R S M) : ℝ)=faceDeterminant (cornerFaceDomain R S M) 4 := by
  rw [cornerPrimal_treeCount_eq_dirichlet hR0 hS0 hM hR hS]
  have heq : unmarkedFaces R S (fourCornerVacancies R S M)=
      faceRectangle R S \ fourCornerVacancies (R-1) (S-1) M := by
    rw [unmarkedFaces, markedFaces_fourCorners hM (ferrers_family_fit hM hR hS), foundation_faceIndices]
  rw [heq]
  exact face_dirichlet_det_eq_integer _

/-- Embed natural corner placements as the integer-coordinate placements used
by the already checked polarization modules. -/
theorem integerFaces_placedCorner {R S : ℕ} (c : Corner) {M : Diagram}
    (hfit : M⊆faceRectangle (R+1) (S+1)) :
    integerFaces (placedCorner R S c M)=
      M.image (fun p => ((if c.1 then (p.1 : ℤ) else (R : ℤ)-p.1),
        (if c.2 then (p.2 : ℤ) else (S : ℤ)-p.2))) := by
  unfold integerFaces placedCorner
  rw [Finset.image_image]
  apply Finset.image_congr
  intro p hp
  have hb := mem_faceRectangle.mp (hfit hp)
  rcases c with ⟨cx,cy⟩
  cases cx <;> cases cy <;> apply Prod.ext <;>
    simp only [Function.comp_apply, cornerMap, ofNatPoint, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- A two-corner family with all other diagrams empty. -/
def twoCornerFamily (c d : Corner) (A B : Diagram) : Corner → Diagram :=
  fun e => if e=c then A else if e=d then B else ∅

theorem twoCornerFamily_ferrers (c d : Corner) {A B : Diagram} (hA : IsFerrers A) (hB : IsFerrers B) :
    ∀ e, IsFerrers (twoCornerFamily c d A B e) := by
  intro e
  unfold twoCornerFamily
  split_ifs
  · exact hA
  · exact hB
  · intro p hp
    exact False.elim (Finset.notMem_empty p hp)

theorem totalDefect_twoCornerFamily {c d : Corner} (hcd : c≠d) (A B : Diagram) :
    totalDefect (twoCornerFamily c d A B)=A.card+B.card := by
  have he : (fun e => (twoCornerFamily c d A B e).card)=
      (fun e => (if e=c then A.card else 0)+(if e=d then B.card else 0)) := by
    funext e
    by_cases hec : e=c <;> by_cases hed : e=d <;> simp_all [twoCornerFamily]
  rw [totalDefect,he,Finset.sum_add_distrib]
  simp

theorem fourCornerVacancies_twoCornerFamily {R S : ℕ} {c d : Corner} (hcd : c≠d) (A B : Diagram) :
    fourCornerVacancies R S (twoCornerFamily c d A B)=placedCorner R S c A ∪ placedCorner R S d B := by
  ext p
  rw [mem_fourCornerVacancies,Finset.mem_union]
  constructor
  · rintro ⟨e,he⟩
    by_cases hec : e=c
    · subst e
      exact Or.inl (by simpa [twoCornerFamily] using he)
    · by_cases hed : e=d
      · subst e
        exact Or.inr (by simpa [twoCornerFamily,hec] using he)
      · simp [twoCornerFamily,hec,hed,placedCorner] at he
  · rintro (hc | hd)
    · exact ⟨c,by simpa [twoCornerFamily] using hc⟩
    · exact ⟨d,by simpa [twoCornerFamily,Ne.symm hcd] using hd⟩

theorem integerFaces_placedCorner_BL (R S : ℕ) (M : Diagram) :
    integerFaces (placedCorner R S (true,true) M)=integerFaces M := by
  unfold integerFaces placedCorner
  rw [Finset.image_image]
  rfl

theorem integerFaces_placedCorner_BR {R S : ℕ} {M : Diagram}
    (hfit : M⊆faceRectangle (R+1) (S+1)) :
    integerFaces (placedCorner R S (false,true) M)=bottomRightDefect (R+1) M := by
  rw [integerFaces_placedCorner _ hfit]
  unfold bottomRightDefect integerFaces
  rw [Finset.image_image]
  apply Finset.image_congr
  intro p _
  apply Prod.ext <;> simp [Function.comp_def, Polarization.verticalReflection, ofNatPoint]

theorem integerFaces_placedCorner_TL {R S : ℕ} {M : Diagram}
    (hfit : M⊆faceRectangle (R+1) (S+1)) :
    integerFaces (placedCorner R S (true,false) M)=topLeftDefect (S+1) M := by
  rw [integerFaces_placedCorner _ hfit]
  unfold topLeftDefect integerFaces
  rw [Finset.image_image]
  apply Finset.image_congr
  intro p _
  apply Prod.ext <;> simp [Function.comp_def, Polarization.axialReflection, ofNatPoint]

theorem integerFaces_placedCorner_TR {R S : ℕ} {M : Diagram}
    (hfit : M⊆faceRectangle (R+1) (S+1)) :
    integerFaces (placedCorner R S (false,false) M)=
      (bottomRightDefect (R+1) M).image (Polarization.axialReflection S) := by
  rw [integerFaces_placedCorner _ hfit]
  unfold bottomRightDefect integerFaces
  rw [Finset.image_image,Finset.image_image]
  apply Finset.image_congr
  intro p _
  apply Prod.ext <;> simp [Function.comp_def, Polarization.axialReflection,
    Polarization.verticalReflection,ofNatPoint]

/-- Opposite bottom-right / top-left faces in exactly the fold coordinates. -/
theorem cornerFaceDomain_BR_TL {R S : ℕ} (hR : 1≤R) (hS : 1≤S) (A B : Diagram)
    (hA : A⊆faceRectangle R S) (hB : B⊆faceRectangle R S) :
    cornerFaceDomain R S (twoCornerFamily (false,true) (true,false) A B)=
      rectangle R S \ (bottomRightDefect R A ∪ topLeftDefect S B) := by
  unfold cornerFaceDomain
  rw [fourCornerVacancies_twoCornerFamily (by decide : (false,true)≠(true,false))]
  unfold integerFaces
  rw [Finset.image_sdiff _ _ ofNatPoint_injective,Finset.image_union]
  change integerFaces (faceRectangle R S) \
    (integerFaces (placedCorner (R-1) (S-1) (false,true) A) ∪
      integerFaces (placedCorner (R-1) (S-1) (true,false) B))=_
  rw [CornerStripBridge.integerFaces_faceRectangle,
    integerFaces_placedCorner_BR (by simpa only [Nat.sub_add_cancel hR,Nat.sub_add_cancel hS] using hA),
    integerFaces_placedCorner_TL (by simpa only [Nat.sub_add_cancel hR,Nat.sub_add_cancel hS] using hB),
    Nat.sub_add_cancel hR,Nat.sub_add_cancel hS]

/-- Opposite bottom-left / top-right faces in the corner-separation coordinates. -/
theorem cornerFaceDomain_BL_TR {R S : ℕ} (hR : 1≤R) (hS : 1≤S) (A B : Diagram)
    (hA : A⊆faceRectangle R S) (hB : B⊆faceRectangle R S) :
    cornerFaceDomain R S (twoCornerFamily (true,true) (false,false) A B)=
      oppositeCornerFaces R S A B := by
  unfold cornerFaceDomain
  rw [fourCornerVacancies_twoCornerFamily (by decide : (true,true)≠(false,false))]
  unfold integerFaces
  rw [Finset.image_sdiff _ _ ofNatPoint_injective,Finset.image_union]
  change integerFaces (faceRectangle R S) \
    (integerFaces (placedCorner (R-1) (S-1) (true,true) A) ∪
      integerFaces (placedCorner (R-1) (S-1) (false,false) B))=_
  rw [CornerStripBridge.integerFaces_faceRectangle,integerFaces_placedCorner_BL,
    integerFaces_placedCorner_TR (by simpa only [Nat.sub_add_cancel hR,Nat.sub_add_cancel hS] using hB),
    Nat.sub_add_cancel hR]
  unfold oppositeCornerFaces oppositeColumnFaces
  have hs : ((S-1 : ℕ) : ℤ)=(S : ℤ)-1 := by omega
  rw [hs]

theorem cornerFaceDomain_BL_BR {R S : ℕ} (hR : 1≤R) (hS : 1≤S) (A B : Diagram)
    (hA : A⊆faceRectangle R S) (hB : B⊆faceRectangle R S) :
    cornerFaceDomain R S (twoCornerFamily (true,true) (false,true) A B)=
      adjacentCornerFaces R S A B := by
  unfold cornerFaceDomain
  rw [fourCornerVacancies_twoCornerFamily (by decide : (true,true)≠(false,true))]
  unfold integerFaces
  rw [Finset.image_sdiff _ _ ofNatPoint_injective,Finset.image_union]
  change integerFaces (faceRectangle R S) \
    (integerFaces (placedCorner (R-1) (S-1) (true,true) A) ∪
      integerFaces (placedCorner (R-1) (S-1) (false,true) B))=_
  rw [CornerStripBridge.integerFaces_faceRectangle,integerFaces_placedCorner_BL,
    integerFaces_placedCorner_BR (by simpa only [Nat.sub_add_cancel hR,Nat.sub_add_cancel hS] using hB),
    Nat.sub_add_cancel hR]
  rfl

end
end SpanningTreeIsoperimetry.CornerPrimalDomains
