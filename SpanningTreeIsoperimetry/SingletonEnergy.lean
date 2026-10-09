import SpanningTreeIsoperimetry.QuadrantGreen
import SpanningTreeIsoperimetry.UniformStripEnergy

/-! Exact singleton quadrant energy, with the actual Green entry and
finite-minor energy limits identified by uniqueness of limits. -/
namespace SpanningTreeIsoperimetry.SingletonEnergy

open Ferrers CornerEnergy QuadrantGreen Filter SquareMaximality.Boundary
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem originFit (N : ℕ) : ({(0,0)} : Diagram) ⊆ faceRectangle (N+3) (N+3) := by
  intro p hp
  have hp' := Finset.mem_singleton.mp hp
  subst p
  rw [mem_faceRectangle]
  omega

theorem originWindowFit (N : ℕ) : ({(0,0)} : Diagram) ⊆ window N := by
  rw [window,foundation_faceIndices]
  exact originFit N

def originEquiv : Fin 1 ≃ {p // p∈({(0,0)} : Diagram)} :=
  Equiv.ofBijective (fun _ => ⟨(0,0),by simp⟩) (by
    constructor
    · intro i j _
      exact Subsingleton.elim i j
    · intro p
      refine ⟨0,?_⟩
      apply Subtype.ext
      exact (Finset.mem_singleton.mp p.property).symm)

theorem originMinor_det (N : ℕ) : Matrix.det (greenMinor (originFit N))=greenEntry N 0 0 := by
  rw [UniformStripEnergy.greenMinor_det_transport
    (foundation_faceIndices (N+3) (N+3)).symm rfl (originFit N) (originWindowFit N)]
  rw [← Matrix.det_submatrix_equiv_self originEquiv,Matrix.det_fin_one]
  rfl

theorem origin_isFerrers : IsFerrers ({(0,0)} : Diagram) := by
  intro p hp q hx hy
  have hp' := Finset.mem_singleton.mp hp
  subst p
  apply Finset.mem_singleton.mpr
  apply Prod.ext <;> dsimp at hx hy ⊢ <;> omega

theorem origin_exp_energy :
    Real.exp (-realEnergy ({(0,0)} : Diagram)-SquareMaximality.squareLatticeEntropy)=
      2-(16/3)/Real.pi := by
  have hside : Tendsto (fun N : ℕ => N+3) atTop atTop :=
    tendsto_atTop_mono (fun N => by change N≤N+3; omega) tendsto_id
  have ht := greenMinor_det_tendsto origin_isFerrers originFit hside hside
  simp only [Finset.card_singleton,Nat.cast_one,mul_one,originMinor_det] at ht
  have hg := greenEntry_tendsto (0 : Fin 2) (0 : Fin 2)
  have he := congrFun (congrFun greenValue_matrix (0 : Fin 2)) (0 : Fin 2)
  norm_num at he
  rw [he] at hg
  exact tendsto_nhds_unique ht hg

/-- Exact first entry in the paper's small-diagram energy table. -/
theorem realEnergy_singleton :
    realEnergy ({(0,0)} : Diagram)=
      -Real.log (2-(16/3)/Real.pi)-SquareMaximality.squareLatticeEntropy := by
  have h := congrArg Real.log origin_exp_energy
  rw [Real.log_exp] at h
  linarith

theorem singleton_green_pos : 0<2-(16/3)/Real.pi := by
  rw [← origin_exp_energy]
  exact Real.exp_pos _

theorem singleton_green_lt : 2-(16/3)/Real.pi<(303 : ℝ)/1000 := by
  have ht : (1697 : ℝ)/1000<(16/3)/Real.pi := by
    rw [lt_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_lt_d6]
  linarith

/-- A short rational bound suffices for the three-exposed-cell obstruction. -/
theorem realEnergy_singleton_gt : (1 : ℝ)/40<realEnergy ({(0,0)} : Diagram) := by
  have hs := Real.hasSum_log_one_add (a := (697 : ℝ)/303) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 6) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  have hlog : (1193 : ℝ)/1000<Real.log ((1000 : ℝ)/303) := by linarith
  have hl := Real.log_lt_log singleton_green_pos singleton_green_lt
  have he : Real.log ((303 : ℝ)/1000)=-Real.log ((1000 : ℝ)/303) := by
    rw [show (303 : ℝ)/1000=((1000 : ℝ)/303)⁻¹ by norm_num,Real.log_inv]
  rw [he] at hl
  rw [realEnergy_singleton]
  linarith [StripEnergyBound.entropy_lt_729_625]

theorem realEnergy_three_maximal_gt {M : Diagram} (h : 3≤(maximalCells M).card) :
    (3 : ℝ)/40<realEnergy M := by
  have he := realEnergy_maximalCells M
  have hc : (3 : ℝ)≤(maximalCells M).card := by exact_mod_cast h
  have hs := realEnergy_singleton_gt
  have hmul : (3 : ℝ)*realEnergy ({(0,0)} : Diagram)≤
      (maximalCells M).card*realEnergy ({(0,0)} : Diagram) :=
    mul_le_mul_of_nonneg_right hc (realEnergy_nonneg _)
  linarith

theorem realEnergy_three_maximal_strip_gap {M : Diagram} (h : 3≤(maximalCells M).card) (k : ℕ) :
    (51 : ℝ)/5000<realEnergy M-realEnergy (horizontalStrip k) := by
  linarith [realEnergy_three_maximal_gt h,UniformStripEnergy.realEnergy_strip_lt k]

end
end SpanningTreeIsoperimetry.SingletonEnergy
