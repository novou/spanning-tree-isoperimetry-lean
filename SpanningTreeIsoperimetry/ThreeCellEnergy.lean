module

public import SpanningTreeIsoperimetry.QuadrantGreenRelations

@[expose] public section

/-! Exact three-cell quadrant energy and a strict uniform gap above strips. -/
namespace SpanningTreeIsoperimetry.ThreeCellEnergy

open Ferrers CornerEnergy QuadrantGreenRelations Filter
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def ellDet (t : ℝ) : ℝ := 77-(2368/5)*t+(32768/45)*t^2

theorem ell_isFerrers : IsFerrers threeCell := by
  intro p hp q hx hy
  simp only [threeCell,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff] at hp ⊢
  omega

theorem ell_exp_energy :
    Real.exp (-realEnergy threeCell-3*SquareMaximality.squareLatticeEntropy)=ellDet (1/Real.pi) := by
  have hside : Tendsto (fun N : ℕ => N+3) atTop atTop :=
    tendsto_atTop_mono (fun N => by change N≤N+3; omega) tendsto_id
  have ht := greenMinor_det_tendsto ell_isFerrers ellFit hside hside
  simp only [card_threeCell,Nat.cast_ofNat,ellMinor_det] at ht
  have hg := ((show Continuous (Matrix.det : Matrix (Fin 3) (Fin 3) ℝ → ℝ)
    from continuous_id.matrix_det).tendsto _).comp ellGreenMatrix_tendsto
  rw [ellGreenLimit_det] at hg
  have he : 77-(2368/5)/Real.pi+(32768/45)/(Real.pi^2)=ellDet (1/Real.pi) := by
    unfold ellDet
    ring
  rw [he] at hg
  simpa only [mul_comm] using tendsto_nhds_unique ht hg

theorem ellDet_pos : 0<ellDet (1/Real.pi) := by
  rw [← ell_exp_energy]
  exact Real.exp_pos _

theorem realEnergy_ell_exact : realEnergy threeCell=
    -Real.log (ellDet (1/Real.pi))-3*SquareMaximality.squareLatticeEntropy := by
  have h := congrArg Real.log ell_exp_energy
  rw [Real.log_exp] at h
  linarith

theorem ellDet_lt : ellDet (1/Real.pi)<(707 : ℝ)/25000 := by
  have hpL : (3141592653589793 : ℝ)/1000000000000000<Real.pi :=
    lt_trans (by norm_num) Real.pi_gt_d20
  have hpU : Real.pi<(3141592653589794 : ℝ)/1000000000000000 :=
    lt_trans Real.pi_lt_d20 (by norm_num)
  have hl := (div_lt_div_of_pos_left (by norm_num : (0 : ℝ)<1) Real.pi_pos hpU).le
  have hu := (div_lt_div_of_pos_left (by norm_num : (0 : ℝ)<1)
    (by norm_num : (0 : ℝ)<3141592653589793/1000000000000000) hpL).le
  have ht : 0≤1/Real.pi := by positivity
  have hu2 : (1/Real.pi)^2≤(1/((3141592653589793 : ℝ)/1000000000000000))^2 := by gcongr
  norm_num at hl hu hu2
  unfold ellDet
  simp only [one_div,inv_pow] at hu2 ⊢
  nlinarith only [hl,hu2]

theorem log_reciprocal_ell_lower : (35653 : ℝ)/10000<Real.log ((25000 : ℝ)/707) := by
  have hs2 := Real.hasSum_log_one_add (a := (1 : ℝ)) (by norm_num)
  have hb2 := sum_le_hasSum (Finset.range 6) (fun n _ => by positivity) hs2
  norm_num [Finset.sum_range_succ] at hb2
  have h2 : (693146 : ℝ)/1000000<Real.log 2 := by linarith
  have hsy := Real.hasSum_log_one_add (a := (2376 : ℝ)/22624) (by norm_num)
  have hby := sum_le_hasSum (Finset.range 1) (fun n _ => by positivity) hsy
  norm_num [Finset.sum_range_succ] at hby
  have hy : (9957 : ℝ)/100000<Real.log ((25000 : ℝ)/22624) := by linarith
  have he := Real.log_mul (by norm_num : (2 : ℝ)^5≠0)
    (by norm_num : (25000 : ℝ)/22624≠0)
  rw [show (2 : ℝ)^5*((25000 : ℝ)/22624)=(25000 : ℝ)/707 by norm_num,
    Real.log_pow] at he
  norm_num at he
  linarith

/-- A rational lower bound with ample room above the uniform strip estimate. -/
theorem realEnergy_ell_gt : (33 : ℝ)/500<realEnergy threeCell := by
  have hl := Real.log_lt_log ellDet_pos ellDet_lt
  have he : Real.log ((707 : ℝ)/25000)=-Real.log ((25000 : ℝ)/707) := by
    rw [show (707 : ℝ)/25000=((25000 : ℝ)/707)⁻¹ by norm_num,Real.log_inv]
  rw [he] at hl
  rw [realEnergy_ell_exact]
  linarith [log_reciprocal_ell_lower,StripEnergyBound.entropy_lt_729_625]

/-- The three-cell obstruction discharges every nonrectangular Ferrers shape,
with a gap independent of its size or the competing strip length. -/
theorem nonrectangle_limit_gap {M : Diagram} (hM : IsFerrers M) (hne : M.Nonempty)
    (hrect : ¬IsRectangle M) :
    (3 : ℝ)/2500<realEnergy M-UniformStripEnergy.stripEnergyLimit := by
  have hc := realEnergy_threeCell hM hne hrect
  have hn : 0≤((maximalCells M).card-2 : ℕ)*realEnergy ({(0,0)} : Diagram) :=
    mul_nonneg (by positivity) (realEnergy_nonneg _)
  linarith [realEnergy_ell_gt,UniformStripEnergy.stripEnergyLimit_lt]

theorem nonrectangle_strip_gap {M : Diagram} (hM : IsFerrers M) (hne : M.Nonempty)
    (hrect : ¬IsRectangle M) (k : ℕ) :
    (3 : ℝ)/2500<realEnergy M-realEnergy (horizontalStrip k) := by
  linarith [nonrectangle_limit_gap hM hne hrect,UniformStripEnergy.realEnergy_strip_le_limit k]

end
end SpanningTreeIsoperimetry.ThreeCellEnergy
