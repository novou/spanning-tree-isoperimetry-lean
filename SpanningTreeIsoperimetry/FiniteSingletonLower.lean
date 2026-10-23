module

public import SpanningTreeIsoperimetry.BoundarySingletonIntegral
public import SpanningTreeIsoperimetry.SingletonEnergy
public import SpanningTreeIsoperimetry.GreenSwap

@[expose] public section

/-! The actual finite singleton correction: scalar Green identification and
the fourth-order lower bound for primal short sides at least four. -/
namespace SpanningTreeIsoperimetry.FiniteSingletonLower
open Ferrers CornerEnergy BoundaryGreenLoss BoundaryGreenBounds BoundarySingletonIntegral
  GreenStripLimits SingletonEnergy Filter SquareMaximality.Boundary
open scoped Classical Topology
noncomputable section

theorem quadrantGreen_origin : quadrantGreen (0,0) (0,0)=2-(16/3)/Real.pi := by
  have hq := (green_tendsto_quadrant (0,0) (0,0)).comp (tendsto_add_atTop_nat 2)
  have he (N : ℕ) : green (box (N+2)) (0,0) (0,0)=QuadrantGreen.greenEntry N 0 0 := by
    have hb : box (N+2)=QuadrantGreen.window N := by
      unfold box QuadrantGreen.window
      rw [foundation_faceIndices]
    have hp : (0,0)∈QuadrantGreen.window N := by
      rw [QuadrantGreen.window,mem_faceIndices]
      constructor <;> omega
    rw [hb,green_mem hp hp]
    rfl
  have hg := QuadrantGreen.greenEntry_tendsto (0 : Fin 2) (0 : Fin 2)
  have hv := congrFun (congrFun QuadrantGreen.greenValue_matrix (0 : Fin 2)) (0 : Fin 2)
  norm_num at hv
  rw [hv] at hg
  apply tendsto_nhds_unique hq
  exact hg.congr (fun N => (he N).symm)

theorem quadrantGreen_origin_bounds : (151/500 : ℝ)<quadrantGreen (0,0) (0,0) ∧
    quadrantGreen (0,0) (0,0)<10/33 := by
  rw [quadrantGreen_origin]
  constructor
  · have h : (16/3)/Real.pi<(849 : ℝ)/500 := by
      rw [div_lt_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_d6]
    linarith
  · have h : (56 : ℝ)/33<(16/3)/Real.pi := by
      rw [lt_div_iff₀ Real.pi_pos]
      nlinarith [Real.pi_lt_d6]
    linarith

theorem singleton_minor {U : Diagram} (hfit : ({(0,0)} : Diagram)⊆U) :
    Matrix.det (greenMinor hfit)=green U (0,0) (0,0) := by
  rw [← Matrix.det_submatrix_equiv_self originEquiv,Matrix.det_fin_one]
  rw [green_mem (hfit (by simp)) (hfit (by simp))]
  rfl

theorem singleton_correction_eq {R S : ℕ} (hfit : ({(0,0)} : Diagram)⊆faceRectangle R S) :
    correction (faceRectangle R S) {(0,0)}=
      Real.log (quadrantGreen (0,0) (0,0))-Real.log (green (faceRectangle R S) (0,0) (0,0)) := by
  have h := dirichletEnergy_eq origin_isFerrers hfit
  unfold dirichletEnergy at h
  rw [singleton_minor,realEnergy_singleton] at h
  simp only [Finset.card_singleton,Nat.cast_one,mul_one] at h
  rw [quadrantGreen_origin]
  linarith only [h]

theorem log_loss_lower {g q : ℝ} (hg : 0 < g) (hqg : g < q) :
    (q-g)/q<Real.log q-Real.log g := by
  have hq : 0 < q := lt_trans hg hqg
  have hne : g/q≠1 := by intro h; have hh := (div_eq_one_iff_eq hq.ne').mp h; linarith
  have h := Real.log_lt_sub_one_of_pos (div_pos hg hq) hne
  rw [Real.log_div hg.ne' hq.ne'] at h
  have he : (q-g)/q=1-g/q := by field_simp
  rw [he]
  linarith

/-- Every rectangle whose first primal side is at least four has the
singleton lower correction with that side. In particular the bound applies
to the shorter side, after coordinate exchange. -/
theorem singleton_correction_lower_left {R S : ℕ} (hR : 3≤R) (hS : 0 < S) :
    5/(3*((R : ℝ)+1)^4)<correction (faceRectangle R S) {(0,0)} := by
  have hfit : ({(0,0)} : Diagram)⊆faceRectangle R S := by
    intro p hp
    have hp' := Finset.mem_singleton.mp hp
    subst p
    exact mem_faceRectangle.mpr ⟨by omega,hS⟩
  have hg : 0 < green (faceRectangle R S) (0,0) (0,0) := by
    rw [← singleton_minor hfit]
    exact greenMinor_det_pos (Finset.Subset.refl _) hfit
  have hr0 : (0 : ℝ)<(R : ℝ)+1 := by positivity
  have hw := singleton_strip_loss_lower hR
  have hmono := finite_green_le_stripX R S (0,0) (0,0)
  have hloss : (50/99 : ℝ)<((R : ℝ)+1)^4*
      (quadrantGreen (0,0) (0,0)-green (faceRectangle R S) (0,0) (0,0)) := by
    exact hw.trans_le (mul_le_mul_of_nonneg_left (sub_le_sub_left hmono _) (by positivity))
  have hqg : green (faceRectangle R S) (0,0) (0,0)<quadrantGreen (0,0) (0,0) := by
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos (show 0≤((R : ℝ)+1)^4 by positivity) (sub_nonpos.mpr (le_of_not_gt hn))
    linarith
  have hq := lt_trans hg hqg
  have hnum : 5/(3*((R : ℝ)+1)^4)<
      (quadrantGreen (0,0) (0,0)-green (faceRectangle R S) (0,0) (0,0))/quadrantGreen (0,0) (0,0) := by
    rw [div_lt_div_iff₀ (by positivity : 0 < 3*((R : ℝ)+1)^4) hq]
    nlinarith [quadrantGreen_origin_bounds.2]
  rw [singleton_correction_eq hfit]
  exact hnum.trans (log_loss_lower hg hqg)

end
end SpanningTreeIsoperimetry.FiniteSingletonLower
