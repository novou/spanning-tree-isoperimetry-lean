import SpanningTreeIsoperimetry.BoundaryStripKernel
import SpanningTreeIsoperimetry.BoundaryKernelContinuity
import SpanningTreeIsoperimetry.BoundaryRiemann

/-! The actual quadrant-to-strip Green loss is the separated continuum
integral, obtained as a limit of exact finite inverse formulas. -/
namespace SpanningTreeIsoperimetry.BoundaryLossKernel
open Ferrers CornerEnergy BoundaryGreenLoss BoundaryGreenBounds GreenStripLimits
open BoundaryStripKernel BoundarySineModes BoundaryKernelMajorant BoundaryKernelContinuity
open BoundaryRiemann RectangularRemainder Filter
open scoped BigOperators Topology Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

private theorem scaled_interior_sum (f : ℝ → ℝ) (S : ℕ) (hf0 : f 0=0) :
    (4/((S : ℝ)+1))*∑ j : Fin S, f (((j.val : ℝ)+1)/((S : ℝ)+1))=4*leftSum f (S+1) := by
  have hs := Fin.sum_univ_eq_sum_range (fun j : ℕ => f (((j : ℝ)+1)/((S : ℝ)+1))) S
  rw [hs]
  simp only [leftSum,node,Finset.sum_range_succ',Nat.cast_add,Nat.cast_one,Nat.cast_zero,zero_div,hf0,add_zero]
  ring

/-- The exact separated one-boundary integral for actual Green entries. -/
theorem stripX_loss_integral (R : ℕ) (i j : Fin R) (b b' : ℕ) :
    quadrantGreen (i.val,b) (j.val,b')-stripX R (i.val,b) (j.val,b')=
      (4/Real.pi)*(∫ θ in (0 : ℝ)..Real.pi,
        density ((R : ℝ)+1) ((i.val : ℝ)+1) ((j.val : ℝ)+1) (b+1) (b'+1) θ) := by
  let f : ℝ → ℝ := fun x => density ((R : ℝ)+1) ((i.val : ℝ)+1) ((j.val : ℝ)+1) (b+1) (b'+1) (Real.pi*x)
  have hR : 0<R := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hRreal : (0 : ℝ)<R := by exact_mod_cast hR
  have hiR : (i.val : ℝ)+1≤R := by exact_mod_cast Nat.succ_le_of_lt i.isLt
  have hjR : (j.val : ℝ)+1≤R := by exact_mod_cast Nat.succ_le_of_lt j.isLt
  have hraw := density_continuousOn (r := (R : ℝ)+1)
    (a := (i.val : ℝ)+1) (a' := (j.val : ℝ)+1) (c := (R : ℝ))
    (by positivity) (by positivity) hRreal hiR hjR (by linarith) (b+1) (b'+1)
  have hf : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    apply hraw.comp (by fun_prop)
    intro x hx
    constructor <;> nlinarith [Real.pi_pos,hx.1,hx.2]
  have hf0 : f 0=0 := by simp [f,density,gamma_zero]
  let S (N : ℕ) := N+(b+b'+1)
  let y (N : ℕ) : Fin (S N) := ⟨b,by dsimp [S]; omega⟩
  let z (N : ℕ) : Fin (S N) := ⟨b',by dsimp [S]; omega⟩
  have hS : Tendsto S atTop atTop := tendsto_add_atTop_nat (b+b'+1)
  have hS1 : Tendsto (fun N => S N+1) atTop atTop := by
    apply tendsto_atTop_mono (fun N => show N≤S N+1 by dsimp [S]; omega) tendsto_id
  have hactual : Tendsto (fun N => stripY (S N) (i.val,b) (j.val,b')-
      green (faceRectangle R (S N)) (i.val,b) (j.val,b')) atTop
      (𝓝 (quadrantGreen (i.val,b) (j.val,b')-stripX R (i.val,b) (j.val,b'))) := by
    simpa only [Function.comp_def] using
      ((stripY_tendsto_quadrant (i.val,b) (j.val,b')).comp hS).sub
        ((stripX_tendsto R (i.val,b) (j.val,b')).comp hS)
  have hrie := ((leftSum_tendsto hf).comp hS1).const_mul (4 : ℝ)
  have heq : quadrantGreen (i.val,b) (j.val,b')-stripX R (i.val,b) (j.val,b')=
      4*(∫ x in (0 : ℝ)..1, f x) := by
    apply tendsto_nhds_unique hactual
    apply hrie.congr
    intro N
    have h := stripY_sub_rectangle R (S N) i j (y N) (z N)
    have hs : (∑ l : Fin (S N),
        density ((R : ℝ)+1) ((i.val : ℝ)+1) ((j.val : ℝ)+1) (b+1) (b'+1) (angle (S N) l))=
        ∑ l : Fin (S N), f (((l.val : ℝ)+1)/((S N : ℝ)+1)) := by
      apply Finset.sum_congr rfl
      intro l _
      dsimp only [f]
      congr 1
      unfold angle
      ring
    change stripY (S N) (i.val,b) (j.val,b')-green (faceRectangle R (S N)) (i.val,b) (j.val,b')=_ at h
    change _=(4/((S N : ℝ)+1))*∑ l : Fin (S N),
      density ((R : ℝ)+1) ((i.val : ℝ)+1) ((j.val : ℝ)+1) (b+1) (b'+1) (angle (S N) l) at h
    rw [hs,scaled_interior_sum f (S N) hf0] at h
    exact h.symm
  rw [heq]
  have hscale := intervalIntegral.integral_comp_mul_left
    (f := density ((R : ℝ)+1) ((i.val : ℝ)+1) ((j.val : ℝ)+1) (b+1) (b'+1))
    (a := (0 : ℝ)) (b := 1) Real.pi_ne_zero
  simp only [mul_zero,mul_one,smul_eq_mul] at hscale
  change 4*(∫ x in (0 : ℝ)..1,
    density ((R : ℝ)+1) ((i.val : ℝ)+1) ((j.val : ℝ)+1) (b+1) (b'+1) (Real.pi*x))=_
  rw [hscale]
  ring

/-- Exact fourth-order bound for the actual loss caused by one far boundary. -/
theorem stripX_loss_le (R : ℕ) (i j : Fin R) (b b' : ℕ) :
    quadrantGreen (i.val,b) (j.val,b')-stripX R (i.val,b) (j.val,b')≤
      Real.pi^3*((i.val : ℝ)+1)*((j.val : ℝ)+1)*(b+1)*(b'+1)/
        (60*(((R : ℝ)+1)^2-(((max i.val j.val : ℕ) : ℝ)+1)^2)^2) := by
  rw [stripX_loss_integral]
  have hi : (i.val : ℝ)+1≤((max i.val j.val : ℕ) : ℝ)+1 := by exact_mod_cast Nat.add_le_add_right (le_max_left i.val j.val) 1
  have hj : (j.val : ℝ)+1≤((max i.val j.val : ℕ) : ℝ)+1 := by exact_mod_cast Nat.add_le_add_right (le_max_right i.val j.val) 1
  have hm : ((max i.val j.val : ℕ) : ℝ)<R := by exact_mod_cast (max_lt_iff.mpr ⟨i.isLt,j.isLt⟩)
  have h := density_integral_le (r := (R : ℝ)+1)
    (a := (i.val : ℝ)+1) (a' := (j.val : ℝ)+1)
    (c := ((max i.val j.val : ℕ) : ℝ)+1) (by positivity) (by positivity) (by positivity)
    hi hj (by linarith) (b+1) (b'+1)
  simpa only [Nat.cast_add,Nat.cast_one] using h

end
end SpanningTreeIsoperimetry.BoundaryLossKernel
