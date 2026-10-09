import SpanningTreeIsoperimetry.FiniteSingletonSmall
import SpanningTreeIsoperimetry.FixedDirichletSystems

/-! Exact tiny finite Dirichlet systems and their singleton square lower bounds. -/
namespace SpanningTreeIsoperimetry.FiniteSingletonSquares
open Ferrers CornerEnergy BoundaryGreenLoss BoundaryGreenBounds FiniteSingletonLower
  FixedDirichletSystems BoundaryStripKernel
open scoped Classical

def onePotential : Matrix (Fin 1 × Fin 1) (Fin 1) ℤ := fun _ _ => 1

def twoPotential : Matrix (Fin 2 × Fin 2) (Fin 1) ℤ := fun p _ =>
  if p==(0,0) then 7 else if p==(1,1) then 1 else 2

theorem one_system : ∀ p c, (gridKernel 1 1*onePotential) p c=
    4*selection (fun _ : Fin 1 => (0,0)) p c := by decide +kernel

theorem two_system : ∀ p c, (gridKernel 2 2*twoPotential) p c=
    24*selection (fun _ : Fin 1 => (0,0)) p c := by decide +kernel

noncomputable section

theorem green_one_square : green (faceRectangle 1 1) (0,0) (0,0)=(1 : ℝ)/4 := by
  have h := inverse_entries_of_integer_system (fun _ : Fin 1 => ((0,0) : Fin 1 × Fin 1))
    onePotential 4 (by norm_num) one_system (0,0) 0
  rw [rectangle_inverse_green] at h
  simpa only [onePotential,Int.cast_one,Int.cast_ofNat,Fin.val_zero] using h

theorem green_two_square : green (faceRectangle 2 2) (0,0) (0,0)=(7 : ℝ)/24 := by
  have h := inverse_entries_of_integer_system (fun _ : Fin 1 => ((0,0) : Fin 2 × Fin 2))
    twoPotential 24 (by norm_num) two_system (0,0) 0
  rw [rectangle_inverse_green] at h
  norm_num [twoPotential] at h
  exact h

theorem singleton_square_lower_small {R : ℕ} (hR : R=1 ∨ R=2) :
    12/(5*((R : ℝ)+1)^4)<correction (faceRectangle R R) {(0,0)} := by
  have hR0 : 0 < R := by rcases hR with hR | hR <;> omega
  have hfit : ({(0,0)} : Diagram)⊆faceRectangle R R := by
    intro p hp
    have hp' := Finset.mem_singleton.mp hp
    subst p
    exact mem_faceRectangle.mpr ⟨hR0,hR0⟩
  have hg : 0 < green (faceRectangle R R) (0,0) (0,0) := by
    rw [← singleton_minor hfit]
    exact greenMinor_det_pos (Finset.Subset.refl _) hfit
  have hq := quadrantGreen_origin_bounds.1
  have hq0 : 0 < quadrantGreen (0,0) (0,0) := by linarith
  have hqg : green (faceRectangle R R) (0,0) (0,0)<quadrantGreen (0,0) (0,0) := by
    rcases hR with rfl | rfl
    · rw [green_one_square]; linarith
    · rw [green_two_square]; linarith
  have hb : 12/(5*((R : ℝ)+1)^4)<
      (quadrantGreen (0,0) (0,0)-green (faceRectangle R R) (0,0) (0,0))/quadrantGreen (0,0) (0,0) := by
    rw [lt_div_iff₀ hq0]
    rcases hR with rfl | rfl
    · rw [green_one_square]; norm_num; linarith
    · rw [green_two_square]; norm_num; linarith
  rw [singleton_correction_eq hfit]
  exact hb.trans (log_loss_lower hg hqg)

end
end SpanningTreeIsoperimetry.FiniteSingletonSquares
