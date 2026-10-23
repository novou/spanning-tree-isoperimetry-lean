module

public import SpanningTreeIsoperimetry.RowConvexPrimal
public import SpanningTreeIsoperimetry.CornerFolds

@[expose] public section

/-! Actual primal rectangles with four prescribed Ferrers corner defects. -/
namespace SpanningTreeIsoperimetry.CornerPrimalDomains

open Ferrers CornerEnergy DomainIsometries SquareMaximality.Boundary
open FerrersPrimalBridge RowConvexPrimal CornerFolds
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

abbrev Corner := Bool × Bool

/-- `true` selects the lower coordinate side, consistently with FourCorners. -/
def cornerMap (R S : ℕ) (c : Corner) (p : Ferrers.Point) : Ferrers.Point :=
  (if c.1 then p.1 else R-p.1, if c.2 then p.2 else S-p.2)

def placedCorner (R S : ℕ) (c : Corner) (M : Diagram) : Diagram := M.image (cornerMap R S c)

def totalDefect (M : Corner → Diagram) : ℕ := ∑ c, (M c).card

def fourCornerVacancies (R S : ℕ) (M : Corner → Diagram) : Diagram :=
  Finset.univ.biUnion fun c => placedCorner R S c (M c)

def cornerPrimal (R S : ℕ) (M : Corner → Diagram) : Domain :=
  primalDomain R S (fourCornerVacancies R S M)

@[simp] theorem mem_fourCornerVacancies {R S : ℕ} {M : Corner → Diagram} {p : Ferrers.Point} :
    p∈fourCornerVacancies R S M ↔ ∃ c, p∈placedCorner R S c (M c) := by
  simp only [fourCornerVacancies, Finset.mem_biUnion, Finset.mem_univ, true_and]

theorem cornerMap_bounds {R S : ℕ} (c : Corner) {p : Ferrers.Point} (hx : p.1≤R) (hy : p.2≤S) :
    (cornerMap R S c p).1≤R ∧ (cornerMap R S c p).2≤S := by
  rcases c with ⟨cx,cy⟩
  cases cx <;> cases cy <;> simp only [cornerMap, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem cornerMap_involutive {R S : ℕ} (c : Corner) {p : Ferrers.Point} (hx : p.1≤R) (hy : p.2≤S) :
    cornerMap R S c (cornerMap R S c p)=p := by
  rcases c with ⟨cx,cy⟩
  cases cx <;> cases cy <;> apply Prod.ext <;>
    simp only [cornerMap, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem placedCorner_card {R S : ℕ} (c : Corner) {M : Diagram}
    (hfit : M⊆faceRectangle (R+1) (S+1)) : (placedCorner R S c M).card=M.card := by
  apply Finset.card_image_iff.mpr
  intro p hp q hq heq
  have hp' := mem_faceRectangle.mp (hfit hp)
  have hq' := mem_faceRectangle.mp (hfit hq)
  have h := congrArg (cornerMap R S c) heq
  simpa only [cornerMap_involutive c (by omega : p.1≤R) (by omega : p.2≤S),
    cornerMap_involutive c (by omega : q.1≤R) (by omega : q.2≤S)] using h

theorem placedCorner_subset {R S : ℕ} (c : Corner) {M : Diagram}
    (hfit : M⊆faceRectangle (R+1) (S+1)) : placedCorner R S c M⊆faceRectangle (R+1) (S+1) := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  have hq' := mem_faceRectangle.mp (hfit hq)
  have hb := cornerMap_bounds c (by omega : q.1≤R) (by omega : q.2≤S)
  exact mem_faceRectangle.mpr ⟨by omega,by omega⟩

theorem corner_card_le_total (M : Corner → Diagram) (c : Corner) : (M c).card≤totalDefect M :=
  Finset.single_le_sum (f := fun d => (M d).card) (fun d _ => Nat.zero_le _) (Finset.mem_univ c)

theorem pair_card_le_total (M : Corner → Diagram) {c d : Corner} (hcd : c≠d) :
    (M c).card+(M d).card≤totalDefect M := by
  have h := Finset.sum_le_sum_of_subset (s := {c,d}) (t := Finset.univ)
    (f := fun e => (M e).card) (Finset.subset_univ _)
  simpa [hcd, totalDefect] using h

theorem ferrers_family_fit {R S : ℕ} {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c))
    (hR : totalDefect M≤R) (hS : totalDefect M≤S) (c : Corner) : M c⊆faceRectangle R S := by
  intro p hp
  have hb := ferrers_coordinate_lt_card (hM c) hp
  have hc := corner_card_le_total M c
  exact mem_faceRectangle.mpr ⟨by omega,by omega⟩

theorem fourCorner_subset {R S : ℕ} {M : Corner → Diagram}
    (hfit : ∀ c, M c⊆faceRectangle (R+1) (S+1)) :
    fourCornerVacancies R S M⊆faceRectangle (R+1) (S+1) := by
  intro p hp
  obtain ⟨c,hc⟩ := mem_fourCornerVacancies.mp hp
  exact placedCorner_subset c (hfit c) hc

theorem fourCorner_card_le (R S : ℕ) (M : Corner → Diagram) :
    (fourCornerVacancies R S M).card≤totalDefect M := by
  apply (Finset.card_biUnion_le).trans
  apply Finset.sum_le_sum
  intro c _
  exact Finset.card_image_le

theorem placedCorner_left_closed {R S x y x' : ℕ} {M : Diagram} (hM : IsFerrers M) (cy : Bool)
    (hp : (x,y)∈placedCorner R S (true,cy) M) (hx : x'≤x) :
    (x',y)∈placedCorner R S (true,cy) M := by
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hp
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  simp only [cornerMap, ↓reduceIte] at he1 he2
  refine Finset.mem_image.mpr ⟨(x',p.2),hM p hp _ (by omega) le_rfl,?_⟩
  apply Prod.ext
  · rfl
  · exact he2

theorem placedCorner_right_closed {R S x y x' : ℕ} {M : Diagram} (hM : IsFerrers M) (cy : Bool)
    (hp : (x,y)∈placedCorner R S (false,cy) M) (hx : x≤x') (hxR : x'≤R) :
    (x',y)∈placedCorner R S (false,cy) M := by
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hp
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  simp only [cornerMap, Bool.false_eq_true, ↓reduceIte] at he1 he2
  refine Finset.mem_image.mpr ⟨(R-x',p.2),hM p hp _ (by omega) le_rfl,?_⟩
  apply Prod.ext
  · simp only [cornerMap, Bool.false_eq_true, ↓reduceIte]
    omega
  · exact he2

theorem fourCorner_rowConvex (R S : ℕ) {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c)) :
    RowConvex (faceRectangle (R+1) (S+1) \ fourCornerVacancies R S M) := by
  intro x₁ x x₂ y h₁ h₂ h₁x hx₂
  have hb₁ := mem_faceRectangle.mp (Finset.mem_sdiff.mp h₁).1
  have hb₂ := mem_faceRectangle.mp (Finset.mem_sdiff.mp h₂).1
  refine Finset.mem_sdiff.mpr ⟨mem_faceRectangle.mpr ⟨by omega,hb₁.2⟩,?_⟩
  intro hx
  obtain ⟨⟨cx,cy⟩,hc⟩ := mem_fourCornerVacancies.mp hx
  cases cx
  · have h := placedCorner_right_closed (hM (false,cy)) cy hc hx₂ (by omega)
    exact (Finset.mem_sdiff.mp h₂).2 (mem_fourCornerVacancies.mpr ⟨(false,cy),h⟩)
  · have h := placedCorner_left_closed (hM (true,cy)) cy hc h₁x
    exact (Finset.mem_sdiff.mp h₁).2 (mem_fourCornerVacancies.mpr ⟨(true,cy),h⟩)

theorem placedCorner_disjoint {R S : ℕ} {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c))
    (hR : totalDefect M≤R+1) (hS : totalDefect M≤S+1) {c d : Corner} (hcd : c≠d) :
    Disjoint (placedCorner R S c (M c)) (placedCorner R S d (M d)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨a,ha,hea⟩ := Finset.mem_image.mp hp
  obtain ⟨b,hb,heb⟩ := Finset.mem_image.mp hq
  have hsum := pair_card_le_total M hcd
  have hab := ferrers_coordinate_lt_card (hM c) ha
  have hbb := ferrers_coordinate_lt_card (hM d) hb
  have he1 := congrArg Prod.fst (hea.trans heb.symm)
  have he2 := congrArg Prod.snd (hea.trans heb.symm)
  rcases c with ⟨cx,cy⟩
  rcases d with ⟨dx,dy⟩
  cases cx <;> cases cy <;> cases dx <;> cases dy <;>
    simp only [cornerMap, Bool.false_eq_true, ↓reduceIte] at he1 he2 <;>
    simp only [ne_eq, Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false,
      and_true, and_false, not_true_eq_false, not_false_eq_true] at hcd <;> omega

theorem fourCorner_card {R S : ℕ} {M : Corner → Diagram} (hM : ∀ c, IsFerrers (M c))
    (hR : totalDefect M≤R) (hS : totalDefect M≤S) :
    (fourCornerVacancies R S M).card=totalDefect M := by
  rw [fourCornerVacancies,Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro c _
    apply placedCorner_card c
    intro p hp
    have h := mem_faceRectangle.mp (ferrers_family_fit hM hR hS c hp)
    exact mem_faceRectangle.mpr ⟨by omega,by omega⟩
  · intro c _ d _ hcd
    exact placedCorner_disjoint hM (by omega) (by omega) hcd

/-- Full geometric and determinant bridge for four actual Ferrers deletions. -/
theorem cornerPrimal_treeCount_eq_dirichlet {R S : ℕ} {M : Corner → Diagram}
    (hR0 : 1≤R) (hS0 : 1≤S) (hM : ∀ c, IsFerrers (M c))
    (hR : totalDefect M≤R) (hS : totalDefect M≤S) :
    (treeCount (cornerPrimal R S M) : ℝ)=
      Matrix.det (fourIminusAdjacency (unmarkedFaces R S (fourCornerVacancies R S M))) := by
  apply RowConvexPrimal.primal_treeCount_eq_dirichlet hR0 hS0
  · apply fourCorner_subset
    intro c p hp
    have h := mem_faceRectangle.mp (ferrers_family_fit hM hR hS c hp)
    exact mem_faceRectangle.mpr ⟨by omega,by omega⟩
  · exact fourCorner_rowConvex R S hM
  · exact (fourCorner_card_le R S M).trans hR
  · exact (fourCorner_card_le R S M).trans hS

end
end SpanningTreeIsoperimetry.CornerPrimalDomains
