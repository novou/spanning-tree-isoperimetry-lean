module

public import SpanningTreeIsoperimetry.CornerPrimalFaces
public import SpanningTreeIsoperimetry.LatticeCongruence
public import SpanningTreeIsoperimetry.FourCorners

@[expose] public section

/-! Reflections and coordinate exchange of the actual four-corner primal
models, expressed in the classification's concrete congruence relation. -/
namespace SpanningTreeIsoperimetry.CornerPrimalDomains

open Ferrers CornerEnergy DomainIsometries SquareMaximality.Boundary FerrersPrimalBridge
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def integerCornerVacancies (R S : ℕ) (M : Corner → Diagram) : Domain :=
  Finset.univ.biUnion fun c => (M c).image (cornerEmbedding (R+1) (S+1) c.1 c.2)

theorem integerFaces_fourCornerVacancies {R S : ℕ} {M : Corner → Diagram}
    (hfit : ∀ c, M c⊆faceRectangle (R+1) (S+1)) :
    integerFaces (fourCornerVacancies R S M)=integerCornerVacancies R S M := by
  unfold integerFaces fourCornerVacancies integerCornerVacancies
  rw [Finset.biUnion_image]
  apply Finset.biUnion_congr rfl
  intro c _
  change integerFaces (placedCorner R S c (M c))=_
  rw [integerFaces_placedCorner c (hfit c)]
  apply Finset.image_congr
  intro p _
  rcases c with ⟨cx,cy⟩
  cases cx <;> cases cy <;> simp [cornerEmbedding]

theorem cornerPrimal_integer_eq {R S : ℕ} {M : Corner → Diagram}
    (hfit : ∀ c, M c⊆faceRectangle (R+1) (S+1)) :
    cornerPrimal R S M=rectangle (R+1) (S+1) \ integerCornerVacancies R S M := by
  rw [cornerPrimal,primalDomain_eq,integerFaces_fourCornerVacancies hfit]

def reflectCorner (c d : Corner) : Corner :=
  (if c.1 then d.1 else !d.1, if c.2 then d.2 else !d.2)

def reflectedFamily (c : Corner) (M : Corner → Diagram) : Corner → Diagram :=
  fun d => M (reflectCorner c d)

def reflectPoint (R S : ℕ) (c : Corner) (p : Vertex) : Vertex :=
  (if c.1 then p.1 else (R : ℤ)-p.1, if c.2 then p.2 else (S : ℤ)-p.2)

@[simp] theorem reflectCorner_involutive (c d : Corner) : reflectCorner c (reflectCorner c d)=d := by
  rcases c with ⟨cx,cy⟩
  cases cx <;> cases cy <;> simp [reflectCorner]

@[simp] theorem reflectPoint_involutive (R S : ℕ) (c : Corner) (p : Vertex) :
    reflectPoint R S c (reflectPoint R S c p)=p := by
  rcases c with ⟨cx,cy⟩
  cases cx <;> cases cy <;> ext <;> simp [reflectPoint]

theorem reflectPoint_cornerEmbedding (R S : ℕ) (c d : Corner) (p : Ferrers.Point) :
    reflectPoint R S c (cornerEmbedding (R+1) (S+1) d.1 d.2 p)=
      cornerEmbedding (R+1) (S+1) (reflectCorner c d).1 (reflectCorner c d).2 p := by
  rcases c with ⟨cx,cy⟩
  rcases d with ⟨dx,dy⟩
  cases cx <;> cases cy <;> cases dx <;> cases dy <;>
    ext <;> simp [reflectPoint,reflectCorner,cornerEmbedding]

theorem reflectPoint_rectangle (R S : ℕ) (c : Corner) :
    (rectangle (R+1) (S+1)).image (reflectPoint R S c)=rectangle (R+1) (S+1) := by
  ext p
  rw [CornerFolds.mem_image_involution (reflectPoint_involutive R S c)]
  rcases c with ⟨cx,cy⟩
  cases cx <;> cases cy <;> simp only [mem_rectangle,reflectPoint,Bool.false_eq_true,↓reduceIte] <;> omega

theorem reflectPoint_vacancies (R S : ℕ) (c : Corner) (M : Corner → Diagram) :
    (integerCornerVacancies R S M).image (reflectPoint R S c)=
      integerCornerVacancies R S (reflectedFamily c M) := by
  ext p
  constructor
  · intro hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨d,_,hd⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hd
    apply Finset.mem_biUnion.mpr
    refine ⟨reflectCorner c d,Finset.mem_univ _,Finset.mem_image.mpr ⟨q,?_,?_⟩⟩
    · simpa only [reflectedFamily,reflectCorner_involutive] using hq
    · exact (reflectPoint_cornerEmbedding R S c d q).symm
  · intro hp
    obtain ⟨d,_,hd⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hd
    apply Finset.mem_image.mpr
    refine ⟨cornerEmbedding (R+1) (S+1) (reflectCorner c d).1 (reflectCorner c d).2 q,?_,?_⟩
    · exact Finset.mem_biUnion.mpr ⟨reflectCorner c d,Finset.mem_univ _,Finset.mem_image.mpr ⟨q,hq,rfl⟩⟩
    · rw [reflectPoint_cornerEmbedding,reflectCorner_involutive]

theorem cornerPrimal_reflect_image {R S : ℕ} (c : Corner) {M : Corner → Diagram}
    (hfit : ∀ d, M d⊆faceRectangle (R+1) (S+1)) :
    (cornerPrimal R S M).image (reflectPoint R S c)=cornerPrimal R S (reflectedFamily c M) := by
  rw [cornerPrimal_integer_eq hfit,
    Finset.image_sdiff _ _ (Function.Involutive.injective (reflectPoint_involutive R S c)),
    reflectPoint_rectangle,reflectPoint_vacancies,
    cornerPrimal_integer_eq (M := reflectedFamily c M) (fun d => hfit (reflectCorner c d))]

theorem cornerPrimal_reflect_congruent {R S : ℕ} (c : Corner) {M : Corner → Diagram}
    (hfit : ∀ d, M d⊆faceRectangle (R+1) (S+1)) :
    Congruent (cornerPrimal R S M) (cornerPrimal R S (reflectedFamily c M)) := by
  refine ⟨((if c.1 then 0 else (R : ℤ)),(if c.2 then 0 else (S : ℤ))),false,
    (if c.1 then (1 : ℤ) else -1),(if c.2 then (1 : ℤ) else -1),?_,?_,?_⟩
  · cases c.1 <;> simp
  · cases c.2 <;> simp
  · have he : rigidMotion ((if c.1 then 0 else (R : ℤ)),(if c.2 then 0 else (S : ℤ))) false
        (if c.1 then 1 else -1) (if c.2 then 1 else -1)=reflectPoint R S c := by
      funext p
      rcases c with ⟨cx,cy⟩
      cases cx <;> cases cy <;> ext <;> simp [rigidMotion,reflectPoint,sub_eq_add_neg]
    rw [he]
    exact cornerPrimal_reflect_image c hfit

def transposedFamily (M : Corner → Diagram) : Corner → Diagram :=
  fun c => transpose (M c.swap)

theorem swap_cornerEmbedding (R S : ℕ) (c : Corner) (p : Ferrers.Point) :
    (cornerEmbedding (R+1) (S+1) c.1 c.2 p).swap=
      cornerEmbedding (S+1) (R+1) c.2 c.1 p.swap := by
  rcases c with ⟨cx,cy⟩
  cases cx <;> cases cy <;> rfl

theorem transpose_integerVacancies (R S : ℕ) (M : Corner → Diagram) :
    (integerCornerVacancies R S M).image Prod.swap=integerCornerVacancies S R (transposedFamily M) := by
  ext p
  constructor
  · intro hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨c,_,hc⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
    apply Finset.mem_biUnion.mpr
    refine ⟨c.swap,Finset.mem_univ _,Finset.mem_image.mpr ⟨q.swap,?_,?_⟩⟩
    · change q.swap∈transpose (M c.swap.swap)
      simpa only [mem_transpose,Prod.swap_swap] using hq
    · exact (swap_cornerEmbedding R S c q).symm
  · intro hp
    obtain ⟨c,_,hc⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
    have hq' : q.swap∈M c.swap := mem_transpose.mp hq
    apply Finset.mem_image.mpr
    refine ⟨cornerEmbedding (R+1) (S+1) c.2 c.1 q.swap,?_,?_⟩
    · exact Finset.mem_biUnion.mpr ⟨c.swap,Finset.mem_univ _,Finset.mem_image.mpr ⟨q.swap,hq',rfl⟩⟩
    · simpa only [Prod.fst_swap,Prod.snd_swap,Prod.swap_swap] using swap_cornerEmbedding R S c.swap q.swap

theorem transposedFamily_fit {R S : ℕ} {M : Corner → Diagram}
    (hfit : ∀ c, M c⊆faceRectangle (R+1) (S+1)) :
    ∀ c, transposedFamily M c⊆faceRectangle (S+1) (R+1) := by
  intro c p hp
  have hb := mem_faceRectangle.mp (hfit c.swap (mem_transpose.mp hp))
  exact mem_faceRectangle.mpr ⟨hb.2,hb.1⟩

theorem cornerPrimal_transpose_image {R S : ℕ} {M : Corner → Diagram}
    (hfit : ∀ c, M c⊆faceRectangle (R+1) (S+1)) :
    (cornerPrimal R S M).image Prod.swap=cornerPrimal S R (transposedFamily M) := by
  have hrect : (rectangle (R+1) (S+1)).image Prod.swap=rectangle (S+1) (R+1) := by
    ext p
    rw [CornerFolds.mem_image_involution Prod.swap_swap]
    simp only [mem_rectangle,Prod.fst_swap,Prod.snd_swap]
    tauto
  rw [cornerPrimal_integer_eq hfit,Finset.image_sdiff _ _ Prod.swap_injective,hrect,
    transpose_integerVacancies,cornerPrimal_integer_eq (transposedFamily_fit hfit)]

theorem cornerPrimal_transpose_congruent {R S : ℕ} {M : Corner → Diagram}
    (hfit : ∀ c, M c⊆faceRectangle (R+1) (S+1)) :
    Congruent (cornerPrimal R S M) (cornerPrimal S R (transposedFamily M)) := by
  refine ⟨(0,0),true,1,1,Or.inl rfl,Or.inl rfl,?_⟩
  have he : rigidMotion (0,0) true 1 1=Prod.swap := by funext ⟨x,y⟩; simp [rigidMotion]
  rw [he]
  exact cornerPrimal_transpose_image hfit

theorem reflectedFamily_ferrers (c : Corner) {M : Corner → Diagram} (hM : ∀ d, IsFerrers (M d)) :
    ∀ d, IsFerrers (reflectedFamily c M d) := fun d => hM (reflectCorner c d)

theorem transposedFamily_ferrers {M : Corner → Diagram} (hM : ∀ d, IsFerrers (M d)) :
    ∀ d, IsFerrers (transposedFamily M d) := fun d => transpose_isFerrers (hM d.swap)

theorem totalDefect_reflectedFamily (c : Corner) (M : Corner → Diagram) :
    totalDefect (reflectedFamily c M)=totalDefect M := by
  exact Equiv.sum_comp (Function.Involutive.toPerm (reflectCorner c) (reflectCorner_involutive c))
    (fun d => (M d).card)

theorem totalDefect_transposedFamily (M : Corner → Diagram) :
    totalDefect (transposedFamily M)=totalDefect M := by
  simp only [totalDefect,transposedFamily,card_transpose]
  exact (Equiv.prodComm Bool Bool).sum_comp (fun d => (M d).card)

theorem reflectedFamily_twoCornerFamily (c a b : Corner) (A B : Diagram) :
    reflectedFamily c (twoCornerFamily a b A B)=
      twoCornerFamily (reflectCorner c a) (reflectCorner c b) A B := by
  funext d
  have he (e : Corner) : reflectCorner c d=e ↔ d=reflectCorner c e := by
    constructor
    · intro h
      simpa only [reflectCorner_involutive] using congrArg (reflectCorner c) h
    · intro h
      rw [h,reflectCorner_involutive]
  simp only [reflectedFamily,twoCornerFamily,he]

theorem transposedFamily_twoCornerFamily (a b : Corner) (A B : Diagram) :
    transposedFamily (twoCornerFamily a b A B)=twoCornerFamily a.swap b.swap (transpose A) (transpose B) := by
  funext d
  have he (e : Corner) : d.swap=e ↔ d=e.swap := by
    constructor
    · intro h
      simpa only [Prod.swap_swap] using congrArg Prod.swap h
    · intro h
      rw [h,Prod.swap_swap]
  simp only [transposedFamily,twoCornerFamily,he]
  split_ifs <;> simp [transpose]

end
end SpanningTreeIsoperimetry.CornerPrimalDomains
