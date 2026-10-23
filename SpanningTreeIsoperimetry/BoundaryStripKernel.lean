module

public import SpanningTreeIsoperimetry.BoundaryScalarLimit
public import SpanningTreeIsoperimetry.BoundarySpectralKernel
public import SpanningTreeIsoperimetry.BoundaryKernelMajorant
public import SpanningTreeIsoperimetry.GreenSwap

@[expose] public section

/-! Fixed-width infinite-strip entries from actual finite inverses, followed
by the exact finite-y boundary-loss sum. No continuum kernel is assumed. -/
namespace SpanningTreeIsoperimetry.BoundaryStripKernel
open Ferrers CornerEnergy BoundaryGreenLoss BoundaryGreenBounds GreenStripLimits
open ScalarResolvent BoundarySineModes BoundarySeparatedGreen BoundarySpectralKernel
open BoundaryScalarLimit BoundaryTridiagonalGreen BoundaryKernelMajorant RectangularRemainder Filter
open scoped BigOperators Matrix Topology Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem rectangle_inverse_green (R S : ℕ) (p q : Fin R × Fin S) :
    (rectangleDirichlet R S)⁻¹ p q=
      green (faceRectangle R S) (p.1.val,p.2.val) (q.1.val,q.2.val) := by
  have hp : (p.1.val,p.2.val)∈SquareMaximality.Boundary.faceIndices R S := by
    rw [SquareMaximality.Boundary.mem_faceIndices]
    have hx:=p.1.isLt; have hy:=p.2.isLt
    omega
  have hq : (q.1.val,q.2.val)∈SquareMaximality.Boundary.faceIndices R S := by
    rw [SquareMaximality.Boundary.mem_faceIndices]
    have hx:=q.1.isLt; have hy:=q.2.isLt
    omega
  rw [← foundation_faceIndices R S,green_mem hp hq,
    rectangleDirichlet_eq_faceMatrix,Matrix.inv_submatrix_equiv]
  rfl

theorem stripY_entry (S a b : ℕ) (y z : Fin S) :
    stripY S (a,y.val) (b,z.val)=
      (2/((S : ℝ)+1))*∑ j : Fin S, mode S j y*mode S j z*halfEntry (modeGamma S j) a b := by
  have hleft : Tendsto (fun N => green (faceRectangle (pathLength N a b) S) (a,y.val) (b,z.val)) atTop
      (𝓝 (stripY S (a,y.val) (b,z.val))) := by
    simpa only [pathLength,Function.comp_def] using
      (stripY_tendsto S (a,y.val) (b,z.val)).comp (tendsto_add_atTop_nat (a+b+1))
  have hright : Tendsto (fun N => (2/((S : ℝ)+1))*∑ j : Fin S,
      mode S j y*mode S j z*finiteEntry N (modeGamma S j) a b) atTop
      (𝓝 ((2/((S : ℝ)+1))*∑ j : Fin S, mode S j y*mode S j z*halfEntry (modeGamma S j) a b)) :=
    (tendsto_finsetSum (Finset.univ : Finset (Fin S)) (fun (j : Fin S) _ =>
      (finiteEntry_tendsto (modeGamma S j) (modeGamma_pos S j) a b).const_mul (mode S j y*mode S j z))).const_mul _
  apply tendsto_nhds_unique hleft
  apply hright.congr
  intro N
  have he := rectangle_inverse_entry (pathLength N a b) S
    (leftSite N a b,y) (rightSite N a b,z)
  rw [rectangle_inverse_green] at he
  simpa only [leftSite,rightSite,finiteEntry,Prod.fst,Prod.snd] using he.symm

theorem modeGamma_eq_gamma (S : ℕ) (j : Fin S) : modeGamma S j=gamma (angle S j) := by
  rw [gamma_eq_kernel ⟨(angle_pos S j).le,(angle_lt_pi S j).le⟩,
    SquareMaximality.Rectangle.Concrete.kernel,modeGamma]
  have he : Real.pi*(angle S j/Real.pi)=angle S j := by field_simp
  rw [he]

theorem mode_sin (S : ℕ) (j y : Fin S) :
    mode S j y=Real.sin (((y.val+1 : ℕ) : ℝ)*angle S j) := by
  unfold mode
  push_cast
  congr 1
  ring

/-- At every finite y-width, the difference of an actual infinite-x strip
entry and the actual rectangle entry is exactly the separated loss sum. -/
theorem stripY_sub_rectangle (R S : ℕ) (i l : Fin R) (y z : Fin S) :
    stripY S (i.val,y.val) (l.val,z.val)-green (faceRectangle R S) (i.val,y.val) (l.val,z.val)=
      (4/((S : ℝ)+1))*∑ j : Fin S,
        density ((R : ℝ)+1) ((i.val : ℝ)+1) ((l.val : ℝ)+1) (y.val+1) (z.val+1) (angle S j) := by
  rw [stripY_entry,← rectangle_inverse_green R S (i,y) (l,z),rectangle_inverse_entry,
    ← mul_sub,← Finset.sum_sub_distrib]
  have he : (∑ j : Fin S, (mode S j y*mode S j z*halfEntry (modeGamma S j) i.val l.val-
      mode S j y*mode S j z*kernel R (modeGamma S j) i l))=
      2*∑ j : Fin S, density ((R : ℝ)+1) ((i.val : ℝ)+1) ((l.val : ℝ)+1)
        (y.val+1) (z.val+1) (angle S j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_sub,halfEntry_sub_kernel R (modeGamma S j) (modeGamma_pos S j) i l,
      mode_sin,mode_sin,modeGamma_eq_gamma]
    unfold density
    ring
  rw [he]
  ring

/-- Infinite strips of increasing y-width exhaust the same actual quadrant
kernel, by finite-square comparison and the already proved uniform bound. -/
theorem stripY_tendsto_quadrant (p q : Point) :
    Tendsto (fun S => stripY S p q) atTop (𝓝 (quadrantGreen p q)) := by
  apply (tendsto_add_atTop_iff_nat (f := fun S => stripY S p q) 1).mp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (green_tendsto_quadrant p q) tendsto_const_nhds
  · intro N
    exact finite_green_le_stripY (N+1) (N+1) p q
  · intro N
    exact stripY_le_quadrant (N+1) p q

end
end SpanningTreeIsoperimetry.BoundaryStripKernel
