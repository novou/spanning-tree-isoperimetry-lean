import SpanningTreeIsoperimetry.LatticeCongruence

/-! Symmetry of concrete lattice congruence and maximality transport by count. -/
namespace SpanningTreeIsoperimetry
open scoped Classical

theorem Congruent.symm {A B : Domain} (h : Congruent A B) : Congruent B A := by
  obtain ⟨a,sw,sx,sy,hx,hy,he⟩ := h
  let tx := if sw then sy else sx
  let ty := if sw then sx else sy
  let b : Vertex := if sw then (-sy*a.2,-sx*a.1) else (-sx*a.1,-sy*a.2)
  have htx : tx=1 ∨ tx= -1 := by cases sw <;> assumption
  have hty : ty=1 ∨ ty= -1 := by cases sw <;> assumption
  refine ⟨b,sw,tx,ty,htx,hty,?_⟩
  rw [← he,Finset.image_image]
  have hi : rigidMotion b sw tx ty ∘ rigidMotion a sw sx sy=id := by
    funext p
    cases sw <;> rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;>
      ext <;> simp [Function.comp_def,rigidMotion,b,tx,ty]
  rw [hi,Finset.image_id]

theorem isMaximizer_of_same_count {A B : Domain} (hA : IsMaximizer A)
    (hcard : B.card=A.card) (hconn : (domainGraph B).Connected)
    (hcount : treeCount B=treeCount A) : IsMaximizer B := by
  refine ⟨hconn,?_⟩
  intro T ht hc
  have h := hA.2 T (ht.trans hcard) hc
  rwa [← hcount] at h

end SpanningTreeIsoperimetry
