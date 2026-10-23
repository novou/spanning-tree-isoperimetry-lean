module

public import SpanningTreeIsoperimetry.MatrixGreenSeries
public import SpanningTreeIsoperimetry.FaceWalkWords
public import SpanningTreeIsoperimetry.CornerDeterminant
public import SpanningTreeIsoperimetry.FiniteGreenMonotonicity

@[expose] public section

/-! Actual finite Green entries, extended by zero, and their boundary equations.
The loss considered here is the difference of two actual finite inverses. -/
namespace SpanningTreeIsoperimetry.BoundaryGreenLoss

open Ferrers CornerEnergy SquareMaximality.Boundary
open scoped BigOperators Classical Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

/-- Zero extension of a function on a finite face set. -/
def extend (U : Diagram) (f : {p // p∈U} → ℝ) (p : Point) : ℝ :=
  if hp : p∈U then f ⟨p,hp⟩ else 0

@[simp] theorem extend_mem {U : Diagram} (f : {p // p∈U} → ℝ)
    {p : Point} (hp : p∈U) : extend U f p=f ⟨p,hp⟩ := by simp [extend,hp]

@[simp] theorem extend_not_mem {U : Diagram} (f : {p // p∈U} → ℝ)
    {p : Point} (hp : p∉U) : extend U f p=0 := by simp [extend,hp]

theorem sum_delta_extend (U : Diagram) (f : {p // p∈U} → ℝ) (t : Point) :
    (∑ p : {p // p∈U}, (if p.val=t then (1 : ℝ) else 0)*f p)=extend U f t := by
  by_cases ht : t∈U
  · have he (p : {p // p∈U}) : p.val=t ↔ p=⟨t,ht⟩ := by
      constructor
      · intro h
        apply Subtype.ext
        exact h
      · intro h
        exact congrArg Subtype.val h
    simp only [he,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,
      ite_true,extend_mem f ht]
  · have he (p : {p // p∈U}) : p.val≠t := by intro h; exact ht (h ▸ p.property)
    simp [he,extend,ht]

/-- Dirichlet lattice Laplacian on the natural-coordinate quadrant. -/
def laplacian (f : Point → ℝ) (p : Point) : ℝ :=
  4*f p-f (p.1+1,p.2)-(if p.1=0 then 0 else f (p.1-1,p.2))-
    f (p.1,p.2+1)-(if p.2=0 then 0 else f (p.1,p.2-1))

theorem laplacian_sub (f g : Point → ℝ) (p : Point) :
    laplacian (fun t => f t-g t) p=laplacian f p-laplacian g p := by
  unfold laplacian
  split_ifs <;> ring

set_option maxHeartbeats 800000 in
theorem dirichlet_row (U : Diagram) (p q : {p // p∈U}) :
    fourIminusAdjacency U p q=
      (if p=q then 4 else 0)-
      (if q.val=(p.val.1+1,p.val.2) then 1 else 0)-
      (if p.val.1=0 then 0 else if q.val=(p.val.1-1,p.val.2) then 1 else 0)-
      (if q.val=(p.val.1,p.val.2+1) then 1 else 0)-
      (if p.val.2=0 then 0 else if q.val=(p.val.1,p.val.2-1) then 1 else 0) := by
  rw [fourIminusAdjacency_apply]
  simp only [Subtype.ext_iff,Prod.ext_iff,natManhattanDist,Nat.dist]
  split_ifs <;> norm_num <;> omega

/-- Matrix multiplication by the actual Dirichlet matrix is the zero-extended
lattice Laplacian; this holds for arbitrary finite face sets. -/
theorem dirichlet_mulVec (U : Diagram) (f : {p // p∈U} → ℝ) (p : {p // p∈U}) :
    (fourIminusAdjacency U *ᵥ f) p=laplacian (extend U f) p.val := by
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [dirichlet_row,sub_mul]
  simp only [Finset.sum_sub_distrib]
  have hdiag : (∑ q : {q // q∈U}, (if p=q then (4 : ℝ) else 0)*f q)=4*f p := by
    simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [hdiag]
  simp only [ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp only [one_mul]
  have hs (t : Point) : (∑ q : {q // q∈U}, if q.val=t then f q else 0)=extend U f t := by
    simpa only [ite_mul,one_mul,zero_mul] using sum_delta_extend U f t
  simp_rw [hs]
  simp only [laplacian,extend_mem f p.property]

/-- The actual inverse Green function, zero outside its finite domain. -/
def green (U : Diagram) (p q : Point) : ℝ :=
  if hp : p∈U then if hq : q∈U then (fourIminusAdjacency U)⁻¹ ⟨p,hp⟩ ⟨q,hq⟩ else 0 else 0

@[simp] theorem green_mem {U : Diagram} {p q : Point} (hp : p∈U) (hq : q∈U) :
    green U p q=(fourIminusAdjacency U)⁻¹ ⟨p,hp⟩ ⟨q,hq⟩ := by simp [green,hp,hq]

theorem green_eq_extend {U : Diagram} {q : Point} (hq : q∈U) :
    (fun p => green U p q)=extend U (fun p => (fourIminusAdjacency U)⁻¹ p ⟨q,hq⟩) := by
  funext p
  simp [green,extend,hq]

theorem green_nonneg {R S : ℕ} {U : Diagram} (hU : U⊆faceRectangle R S) (p q : Point) :
    0≤green U p q := by
  unfold green
  split_ifs with hp hq
  · have hs := MatrixGreenSeries.face_inverse_walk_hasSum
      ((foundation_faceIndices R S).symm ▸ hU) ⟨p,hp⟩ ⟨q,hq⟩
    exact hasSum_le (fun n => by positivity) (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0) hs
  all_goals exact le_rfl

theorem green_equation {R S : ℕ} {U : Diagram} (hU : U⊆faceRectangle R S)
    {p q : Point} (hp : p∈U) (hq : q∈U) :
    laplacian (fun t => green U t q) p=if p=q then 1 else 0 := by
  rw [green_eq_extend hq,← dirichlet_mulVec U _ ⟨p,hp⟩]
  have h := congrArg (fun M => M ⟨p,hp⟩ ⟨q,hq⟩)
    (Matrix.mul_nonsing_inv (fourIminusAdjacency U)
      (isUnit_iff_ne_zero.mpr (dirichlet_posDef hU).det_pos.ne'))
  simpa only [Matrix.mulVec,dotProduct,Matrix.mul_apply,Matrix.one_apply,Subtype.ext_iff] using h

/-- Difference between two actual zero-extended Green functions. -/
def loss (U V : Diagram) (p q : Point) : ℝ := green V p q-green U p q

/-- The point sources cancel: actual finite-volume Green loss is harmonic
inside the smaller domain. No limiting Green kernel is assumed here. -/
theorem loss_harmonic {R S T W : ℕ} {U V : Diagram}
    (hU : U⊆faceRectangle R S) (hV : V⊆faceRectangle T W) (hUV : U⊆V)
    {p q : Point} (hp : p∈U) (hq : q∈U) :
    laplacian (fun t => loss U V t q) p=0 := by
  change laplacian (fun t => green V t q-green U t q) p=0
  rw [laplacian_sub,green_equation hV (hUV hp) (hUV hq),green_equation hU hp hq]
  exact sub_self _

end
end SpanningTreeIsoperimetry.BoundaryGreenLoss
