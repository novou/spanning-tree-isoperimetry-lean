module

public import SpanningTreeIsoperimetry.FiniteSingletonLower

@[expose] public section

/-! Exact one- and two-face infinite strips close the small-side cases of
the singleton correction bound. -/
namespace SpanningTreeIsoperimetry.FiniteSingletonSmall
open Ferrers CornerEnergy BoundaryGreenLoss BoundaryGreenBounds GreenStripLimits FiniteSingletonLower
  BoundaryStripKernel BoundaryScalarLimit BoundarySeparatedGreen BoundarySineModes SingletonEnergy
open scoped Classical BigOperators
noncomputable section

theorem exp_neg_arcosh {x : ℝ} (hx : 1≤x) :
    Real.exp (-Real.arcosh x)=x-Real.sqrt (x^2-1) := by
  rw [Real.exp_neg,Real.exp_arcosh hx]
  have hp : 0 < x+Real.sqrt (x^2-1) := by have hs := Real.sqrt_nonneg (x^2-1); linarith
  rw [inv_eq_one_div]
  apply (div_eq_iff hp.ne').mpr
  nlinarith [Real.sq_sqrt (show 0≤x^2-1 by nlinarith)]

theorem halfEntry_origin {t : ℝ} (ht : 0 < t) : halfEntry t 0 0=Real.exp (-t) := by
  have hs : Real.sinh t≠0 := (Real.sinh_pos_iff.mpr ht).ne'
  simp only [halfEntry,min_self,max_self,Nat.cast_zero,zero_add,one_mul]
  exact mul_div_cancel_left₀ _ hs

theorem stripY_one_origin : stripY 1 (0,0) (0,0)=2-Real.sqrt 3 := by
  have h := stripY_entry 1 0 0 (0 : Fin 1) (0 : Fin 1)
  simp only [Fin.sum_univ_one,halfEntry_origin (modeGamma_pos 1 0)] at h
  norm_num [mode,angle,modeGamma,Real.sin_pi_div_two,Real.cos_pi_div_two] at h
  rw [exp_neg_arcosh (by norm_num : (1 : ℝ)≤2)] at h
  norm_num at h
  exact h

theorem stripY_two_origin : stripY 2 (0,0) (0,0)=2-(Real.sqrt 5+Real.sqrt 21)/4 := by
  have h := stripY_entry 2 0 0 (0 : Fin 2) (0 : Fin 2)
  simp only [Fin.sum_univ_two,halfEntry_origin (modeGamma_pos 2 0),halfEntry_origin (modeGamma_pos 2 1)] at h
  have hs : Real.sin (Real.pi*2/3)=Real.sin (Real.pi/3) := by
    have he : Real.pi*2/3=Real.pi-Real.pi/3 := by ring
    rw [he,Real.sin_pi_sub]
  have hc : Real.cos (Real.pi*2/3)= -Real.cos (Real.pi/3) := by
    have he : Real.pi*2/3=Real.pi-Real.pi/3 := by ring
    rw [he,Real.cos_pi_sub]
  norm_num [mode,angle,modeGamma,hs,hc,Real.sin_pi_div_three,Real.cos_pi_div_three] at h
  rw [exp_neg_arcosh (by norm_num : (1 : ℝ)≤3/2),exp_neg_arcosh (by norm_num : (1 : ℝ)≤5/2)] at h
  norm_num [Real.sqrt_div] at h
  have hsq : Real.sqrt 3^2=(3 : ℝ) := Real.sq_sqrt (by norm_num)
  calc
    _=_ := h
    _=_ := by
      rw [show Real.sqrt 3/2*(Real.sqrt 3/2)=(3/4 : ℝ) by nlinarith only [hsq]]
      ring

theorem stripX_one_lt : stripX 1 (0,0) (0,0)<(67 : ℝ)/250 := by
  rw [stripX_swap]
  change stripY 1 (0,0) (0,0)<(67 : ℝ)/250
  rw [stripY_one_origin]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  nlinarith

theorem stripX_two_lt : stripX 2 (0,0) (0,0)<(591 : ℝ)/2000 := by
  rw [stripX_swap]
  change stripY 2 (0,0) (0,0)<(591 : ℝ)/2000
  rw [stripY_two_origin]
  have hs5 : (559/250 : ℝ)<Real.sqrt 5 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤5),Real.sqrt_nonneg (5 : ℝ)]
  have hs21 : (2291/500 : ℝ)<Real.sqrt 21 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤21),Real.sqrt_nonneg (21 : ℝ)]
  linarith

theorem singleton_correction_lower_small {R S : ℕ} (hR : R=1 ∨ R=2) (hS : 0 < S) :
    5/(3*((R : ℝ)+1)^4)<correction (faceRectangle R S) {(0,0)} := by
  have hR0 : 0 < R := by rcases hR with hR | hR <;> omega
  have hfit : ({(0,0)} : Diagram)⊆faceRectangle R S := by
    intro p hp
    have hp' := Finset.mem_singleton.mp hp
    subst p
    exact mem_faceRectangle.mpr ⟨hR0,hS⟩
  have hg : 0 < green (faceRectangle R S) (0,0) (0,0) := by
    rw [← singleton_minor hfit]
    exact greenMinor_det_pos (Finset.Subset.refl _) hfit
  have hmono := finite_green_le_stripX R S (0,0) (0,0)
  have hq := quadrantGreen_origin_bounds.1
  have hq0 : 0 < quadrantGreen (0,0) (0,0) := by linarith
  have hqg : green (faceRectangle R S) (0,0) (0,0)<quadrantGreen (0,0) (0,0) := by
    rcases hR with rfl | rfl
    · linarith [stripX_one_lt]
    · linarith [stripX_two_lt]
  have hb : 5/(3*((R : ℝ)+1)^4)<
      (quadrantGreen (0,0) (0,0)-green (faceRectangle R S) (0,0) (0,0))/quadrantGreen (0,0) (0,0) := by
    rw [lt_div_iff₀ hq0]
    rcases hR with rfl | rfl
    · norm_num
      linarith [stripX_one_lt]
    · norm_num
      linarith [stripX_two_lt]
  rw [singleton_correction_eq hfit]
  exact hb.trans (log_loss_lower hg hqg)

theorem singleton_correction_swap {R S : ℕ} (hR : 0 < R) (hS : 0 < S) :
    correction (faceRectangle R S) {(0,0)}=correction (faceRectangle S R) {(0,0)} := by
  have hfit (R S : ℕ) (hR : 0 < R) (hS : 0 < S) : ({(0,0)} : Diagram)⊆faceRectangle R S := by
    intro p hp
    have hp' := Finset.mem_singleton.mp hp
    subst p
    exact mem_faceRectangle.mpr ⟨hR,hS⟩
  rw [singleton_correction_eq (hfit R S hR hS),singleton_correction_eq (hfit S R hS hR),
    rectangle_green_swap R S]
  rfl

/-- The uniform singleton lower bound for every nonempty face rectangle.
Primal side lengths are R+1,S+1. -/
theorem singleton_correction_lower {R S : ℕ} (hR : 0 < R) (hS : 0 < S) :
    5/(3*((min R S : ℕ)+1 : ℝ)^4)<correction (faceRectangle R S) {(0,0)} := by
  have hleft (R S : ℕ) (hR : 0 < R) (hS : 0 < S) :
      5/(3*((R : ℝ)+1)^4)<correction (faceRectangle R S) {(0,0)} := by
    by_cases hR3 : 3≤R
    · exact singleton_correction_lower_left hR3 hS
    · exact singleton_correction_lower_small (by omega) hS
  rcases le_total R S with hrs | hsr
  · simpa only [min_eq_left hrs] using hleft R S hR hS
  · rw [min_eq_right hsr,singleton_correction_swap hR hS]
    exact hleft S R hS hR

end
end SpanningTreeIsoperimetry.FiniteSingletonSmall
