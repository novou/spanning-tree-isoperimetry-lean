module

public import SpanningTreeIsoperimetry.Targets
public import SpanningTreeIsoperimetry.DomainIsometries

@[expose] public section

/-! The concrete lattice isometries in the classification target preserve
counts and maximality, and their congruence relation composes. -/
namespace SpanningTreeIsoperimetry

def rigidEquiv (a : Vertex) (swap : Bool) (sx sy : ℤ)
    (hx : sx=1 ∨ sx= -1) (hy : sy=1 ∨ sy= -1) : Vertex ≃ Vertex where
  toFun := rigidMotion a swap sx sy
  invFun p :=
    let q := (sx*(p.1-a.1),sy*(p.2-a.2))
    if swap then q.swap else q
  left_inv p := by
    rcases p with ⟨x,y⟩
    cases swap <;> rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      ext <;> simp [rigidMotion] <;> ring
  right_inv p := by
    rcases p with ⟨x,y⟩
    cases swap <;> rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      ext <;> simp [rigidMotion] <;> ring

theorem rigidMotion_adj (a : Vertex) (swap : Bool) (sx sy : ℤ)
    (hx : sx=1 ∨ sx= -1) (hy : sy=1 ∨ sy= -1) (p q : Vertex) :
    lattice.Adj (rigidMotion a swap sx sy p) (rigidMotion a swap sx sy q) ↔ lattice.Adj p q := by
  rcases p with ⟨x,y⟩
  rcases q with ⟨u,v⟩
  cases swap <;> rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp [rigidMotion,lattice,abs_eq (by norm_num : (0 : ℤ)≤1)] <;> omega

noncomputable def rigidGraphIso (A : Domain) (a : Vertex) (swap : Bool) (sx sy : ℤ)
    (hx : sx=1 ∨ sx= -1) (hy : sy=1 ∨ sy= -1) :
    domainGraph A ≃g domainGraph (A.image (rigidMotion a swap sx sy)) :=
  DomainIsometries.inducedImageIso lattice lattice (rigidEquiv a swap sx sy hx hy).toEmbedding
    (rigidMotion_adj a swap sx sy hx hy) A

theorem Congruent.card_eq {A B : Domain} (h : Congruent A B) : A.card=B.card := by
  obtain ⟨a,swap,sx,sy,hx,hy,rfl⟩ := h
  exact (Finset.card_image_of_injective _ (rigidEquiv a swap sx sy hx hy).injective).symm

theorem Congruent.treeCount_eq {A B : Domain} (h : Congruent A B) : treeCount A=treeCount B := by
  obtain ⟨a,swap,sx,sy,hx,hy,rfl⟩ := h
  change SquareMaximality.treeCount (domainGraph A)=
    SquareMaximality.treeCount (domainGraph (A.image (rigidMotion a swap sx sy)))
  exact SquareMaximality.treeCount_congr (rigidGraphIso A a swap sx sy hx hy)

theorem Congruent.connected_iff {A B : Domain} (h : Congruent A B) :
    (domainGraph A).Connected ↔ (domainGraph B).Connected := by
  rw [← treeCount_pos_iff_connected,← treeCount_pos_iff_connected,h.treeCount_eq]

theorem Congruent.isMaximizer_iff {A B : Domain} (h : Congruent A B) :
    IsMaximizer A ↔ IsMaximizer B := by
  constructor
  · intro hA
    refine ⟨h.connected_iff.mp hA.1,?_⟩
    intro T hcard hconn
    have ht := hA.2 T (hcard.trans h.card_eq.symm) hconn
    rwa [h.treeCount_eq] at ht
  · intro hB
    refine ⟨h.connected_iff.mpr hB.1,?_⟩
    intro T hcard hconn
    have ht := hB.2 T (hcard.trans h.card_eq) hconn
    rwa [← h.treeCount_eq] at ht

theorem rigidMotion_comp (a b : Vertex) (u v : Bool) (sx sy tx ty : ℤ) (p : Vertex) :
    rigidMotion b v tx ty (rigidMotion a u sx sy p)=
      rigidMotion (rigidMotion b v tx ty a) (Bool.xor u v)
        (tx*(if v then sy else sx)) (ty*(if v then sx else sy)) p := by
  cases u <;> cases v <;> ext <;> simp [rigidMotion] <;> ring

private theorem sign_mul {a b : ℤ} (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1) :
    a*b=1 ∨ a*b= -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

theorem Congruent.trans {A B C : Domain} (hAB : Congruent A B) (hBC : Congruent B C) :
    Congruent A C := by
  obtain ⟨a,u,sx,sy,hx,hy,hAB⟩ := hAB
  obtain ⟨b,v,tx,ty,htx,hty,hBC⟩ := hBC
  refine ⟨rigidMotion b v tx ty a,Bool.xor u v,
    tx*(if v then sy else sx),ty*(if v then sx else sy),
    sign_mul htx (by cases v <;> assumption),sign_mul hty (by cases v <;> assumption),?_⟩
  have hf : rigidMotion (rigidMotion b v tx ty a) (Bool.xor u v)
      (tx*(if v then sy else sx)) (ty*(if v then sx else sy))=
      rigidMotion b v tx ty ∘ rigidMotion a u sx sy := by
    funext p
    exact (rigidMotion_comp a b u v sx sy tx ty p).symm
  rw [hf,← Finset.image_image,hAB,hBC]

end SpanningTreeIsoperimetry
