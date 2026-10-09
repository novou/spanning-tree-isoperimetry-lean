import SpanningTreeIsoperimetry.BoundarySquareMode

/-! The stronger actual singleton correction for every nonempty square. -/
namespace SpanningTreeIsoperimetry.FiniteSingletonSquareLower
open Ferrers CornerEnergy BoundaryGreenLoss BoundaryGreenBounds GreenStripLimits
  FiniteSingletonLower FiniteSingletonSquares BoundarySquareMode BoundarySingletonIntegral
  BoundaryStripKernel BoundarySineModes BoundaryKernelMajorant
open scoped Classical BigOperators
noncomputable section

theorem second_boundary_lower {R : ℕ} (hR : 3≤R) :
    (3/4 : ℝ)*quadrantGreen (0,0) (0,0)<((R : ℝ)+1)^4*
      (stripY R (0,0) (0,0)-green (faceRectangle R R) (0,0) (0,0)) := by
  have hr : (4 : ℝ)≤(R : ℝ)+1 := by exact_mod_cast (show 4≤R+1 by omega)
  have hE : 0 < Real.exp (2*Real.pi)-1 := by
    have hh := Real.one_lt_exp_iff.mpr (show 0 < 2*Real.pi by positivity)
    linarith
  have hc : (3/4 : ℝ)*quadrantGreen (0,0) (0,0)<4*Real.pi^3/(Real.exp (2*Real.pi)-1) := by
    have hq : (3/4 : ℝ)*quadrantGreen (0,0) (0,0)<5/22 := by linarith [quadrantGreen_origin_bounds.2]
    have hm := mul_lt_mul hq (show Real.exp (2*Real.pi)-1≤(539 : ℝ) by linarith [exp_two_pi_lt]) hE (by norm_num : (0 : ℝ)≤5/22)
    have hp : (157/50 : ℝ)<Real.pi := by linarith [Real.pi_gt_d2]
    have hp3 := pow_lt_pow_left₀ hp (by norm_num : (0 : ℝ)≤157/50) (by decide : 3≠0)
    rw [lt_div_iff₀ hE]
    nlinarith only [hm,hp3]
  have hm := first_mode_density hr
  have hsum : density ((R : ℝ)+1) 1 1 1 1 (angle R ⟨0,by omega⟩)≤
      ∑ j : Fin R, density ((R : ℝ)+1) 1 1 1 1 (angle R j) := by
    exact Finset.single_le_sum (s := (Finset.univ : Finset (Fin R)))
      (f := fun j : Fin R => density ((R : ℝ)+1) 1 1 1 1 (angle R j))
      (fun j _ => density_singleton_nonneg (by positivity) ⟨(angle_pos R j).le,(angle_lt_pi R j).le⟩)
      (Finset.mem_univ (⟨0,by omega⟩ : Fin R))
  have ha : angle R ⟨0,by omega⟩=Real.pi/((R : ℝ)+1) := by simp [angle]
  rw [ha] at hsum
  have he := stripY_sub_rectangle R R (⟨0,by omega⟩ : Fin R) (⟨0,by omega⟩ : Fin R)
    (⟨0,by omega⟩ : Fin R) (⟨0,by omega⟩ : Fin R)
  simp only [Nat.cast_zero,zero_add] at he
  rw [he]
  exact (hc.trans hm).trans_le (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hsum (by positivity)) (by positivity))

theorem singleton_square_correction_lower_large {R : ℕ} (hR : 3≤R) :
    12/(5*((R : ℝ)+1)^4)<correction (faceRectangle R R) {(0,0)} := by
  have hfit : ({(0,0)} : Diagram)⊆faceRectangle R R := by
    intro p hp
    have hp' := Finset.mem_singleton.mp hp
    subst p
    exact mem_faceRectangle.mpr ⟨by omega,by omega⟩
  have hg : 0 < green (faceRectangle R R) (0,0) (0,0) := by
    rw [← singleton_minor hfit]
    exact greenMinor_det_pos (Finset.Subset.refl _) hfit
  have hq := quadrantGreen_origin_bounds
  have hq0 : 0 < quadrantGreen (0,0) (0,0) := by linarith [hq.1]
  have hfirst := singleton_strip_loss_lower hR
  have hsecond := second_boundary_lower hR
  have hswap : stripX R (0,0) (0,0)=stripY R (0,0) (0,0) := stripX_swap R (0,0) (0,0)
  rw [hswap] at hfirst
  have htotal : (12/5 : ℝ)*quadrantGreen (0,0) (0,0)<((R : ℝ)+1)^4*
      (quadrantGreen (0,0) (0,0)-green (faceRectangle R R) (0,0) (0,0)) := by
    nlinarith only [hfirst,hsecond,hq.2,hq0]
  have hqg : green (faceRectangle R R) (0,0) (0,0)<quadrantGreen (0,0) (0,0) := by
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos (show 0≤((R : ℝ)+1)^4 by positivity) (sub_nonpos.mpr (le_of_not_gt hn))
    linarith
  have hb : 12/(5*((R : ℝ)+1)^4)<
      (quadrantGreen (0,0) (0,0)-green (faceRectangle R R) (0,0) (0,0))/quadrantGreen (0,0) (0,0) := by
    rw [div_lt_div_iff₀ (by positivity : 0 < 5*((R : ℝ)+1)^4) hq0]
    nlinarith only [htotal]
  rw [singleton_correction_eq hfit]
  exact hb.trans (log_loss_lower hg hqg)

/-- The appendix's stronger square singleton correction, including both
small primal sides 2 and 3 by exact actual finite inverse systems. -/
theorem singleton_square_correction_lower {R : ℕ} (hR : 0 < R) :
    12/(5*((R : ℝ)+1)^4)<correction (faceRectangle R R) {(0,0)} := by
  by_cases hR3 : 3≤R
  · exact singleton_square_correction_lower_large hR3
  · exact singleton_square_lower_small (by omega)

/-- Primal-side formulation of both quantitative singleton conclusions. -/
theorem singleton_lower_primal {r s : ℕ} (hr : 2≤r) (hs : 2≤s) :
    5/(3*((min r s : ℕ) : ℝ)^4)<correction (faceRectangle (r-1) (s-1)) {(0,0)} ∧
    12/(5*(r : ℝ)^4)<correction (faceRectangle (r-1) (r-1)) {(0,0)} := by
  have hu := FiniteSingletonSmall.singleton_correction_lower (R := r-1) (S := s-1) (by omega) (by omega)
  have hq := singleton_square_correction_lower (R := r-1) (by omega)
  have hm : ((min (r-1) (s-1) : ℕ) : ℝ)+1=(min r s : ℕ) := by
    exact_mod_cast (show min (r-1) (s-1)+1=min r s by omega)
  have hrr : ((r-1 : ℕ) : ℝ)+1=(r : ℝ) := by exact_mod_cast (show r-1+1=r by omega)
  rw [hm] at hu
  rw [hrr] at hq
  exact ⟨hu,hq⟩

end
end SpanningTreeIsoperimetry.FiniteSingletonSquareLower
