import SpanningTreeIsoperimetry.GreenMinorProducts
import SpanningTreeIsoperimetry.CornerPrimalDomains

/-! Reflection of actual rectangular Green minors between the four corners. -/
namespace SpanningTreeIsoperimetry.GreenCornerReflection
open Ferrers CornerEnergy CornerPrimalDomains SquareMaximality.Boundary
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def cornerEquiv (R S : ℕ) (c : Corner) :
    {p // p∈faceRectangle (R+1) (S+1)} ≃ {p // p∈faceRectangle (R+1) (S+1)} where
  toFun p := ⟨cornerMap R S c p.val,by
    have hp := mem_faceRectangle.mp p.property
    have hb := cornerMap_bounds c (by omega : p.val.1≤R) (by omega : p.val.2≤S)
    exact mem_faceRectangle.mpr ⟨by omega,by omega⟩⟩
  invFun p := ⟨cornerMap R S c p.val,by
    have hp := mem_faceRectangle.mp p.property
    have hb := cornerMap_bounds c (by omega : p.val.1≤R) (by omega : p.val.2≤S)
    exact mem_faceRectangle.mpr ⟨by omega,by omega⟩⟩
  left_inv p := by
    apply Subtype.ext
    have hp := mem_faceRectangle.mp p.property
    exact cornerMap_involutive c (by omega) (by omega)
  right_inv p := by
    apply Subtype.ext
    have hp := mem_faceRectangle.mp p.property
    exact cornerMap_involutive c (by omega) (by omega)

theorem corner_distance (R S : ℕ) (c : Corner)
    (p q : {p // p∈faceRectangle (R+1) (S+1)}) :
    natManhattanDist (cornerEquiv R S c p).val (cornerEquiv R S c q).val=
      natManhattanDist p.val q.val := by
  have hp := mem_faceRectangle.mp p.property
  have hq := mem_faceRectangle.mp q.property
  rcases c with ⟨x,y⟩
  cases x <;> cases y <;>
    simp only [cornerEquiv,Equiv.coe_fn_mk,cornerMap,Bool.false_eq_true,ite_false,ite_true,
      natManhattanDist,Nat.dist] <;> omega

theorem dirichlet_reflection (R S : ℕ) (c : Corner) :
    (fourIminusAdjacency (faceRectangle (R+1) (S+1))).submatrix (cornerEquiv R S c) (cornerEquiv R S c)=
      fourIminusAdjacency (faceRectangle (R+1) (S+1)) := by
  ext p q
  simp only [Matrix.submatrix_apply,fourIminusAdjacency_apply,(cornerEquiv R S c).injective.eq_iff,
    corner_distance]

def placedEquiv {R S : ℕ} (c : Corner) {M : Diagram} (hM : M⊆faceRectangle (R+1) (S+1)) :
    {p // p∈M} ≃ {p // p∈placedCorner R S c M} :=
  Equiv.ofBijective (fun p => ⟨cornerMap R S c p.val,Finset.mem_image_of_mem _ p.property⟩) (by
    constructor
    · intro p q he
      have hp := mem_faceRectangle.mp (hM p.property)
      have hq := mem_faceRectangle.mp (hM q.property)
      have hh := congrArg (fun p : {p // p∈placedCorner R S c M} => cornerMap R S c p.val) he
      simp only [cornerMap_involutive c (by omega : p.val.1≤R) (by omega : p.val.2≤S),
        cornerMap_involutive c (by omega : q.val.1≤R) (by omega : q.val.2≤S)] at hh
      exact Subtype.ext hh
    · intro q
      obtain ⟨p,hp,he⟩ := Finset.mem_image.mp q.property
      exact ⟨⟨p,hp⟩,Subtype.ext he⟩)

theorem greenMinor_reflected_det {R S : ℕ} (c : Corner) {M : Diagram}
    (hM : M⊆faceRectangle (R+1) (S+1)) :
    (greenMinor (placedCorner_subset c hM)).det=(greenMinor hM).det := by
  have hi := congrArg (fun A => A⁻¹) (dirichlet_reflection R S c)
  rw [Matrix.inv_submatrix_equiv] at hi
  rw [← Matrix.det_submatrix_equiv_self (placedEquiv c hM)]
  apply congrArg Matrix.det
  ext p q
  exact congrArg (fun A => A ⟨p.val,hM p.property⟩ ⟨q.val,hM q.property⟩) hi

theorem dirichletEnergy_reflected {R S : ℕ} (c : Corner) {M : Diagram}
    (hM : M⊆faceRectangle (R+1) (S+1)) :
    dirichletEnergy (placedCorner_subset c hM)=dirichletEnergy hM := by
  unfold dirichletEnergy
  rw [greenMinor_reflected_det,placedCorner_card c hM]

end
end SpanningTreeIsoperimetry.GreenCornerReflection
