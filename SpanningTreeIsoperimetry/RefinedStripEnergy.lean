module

public import SpanningTreeIsoperimetry.RefinedStripEnclosures
public import SpanningTreeIsoperimetry.RefinedEntropyBounds

@[expose] public section

set_option backward.privateInPublic true

/-! Actual short-strip energy bounds from checked determinant and logarithm
certificates. These supply the supporting line through the fifth strip. -/
namespace SpanningTreeIsoperimetry.RefinedStripEnergy
open Ferrers CornerEnergy RefinedQuadrantBoundary RefinedStripPolynomials RefinedStripEnclosures
open RefinedEntropyBounds CornerNumericBounds
open scoped BigOperators
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

set_option maxHeartbeats 2000000 in
private theorem log_lower_1 : ((11961789/10000000) : ℝ)<Real.log ((10000000000 : ℝ)/3023472737) := by
  have hs := Real.hasSum_log_one_add (a := ((5000000000/3023472737) : ℝ)-1) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 10) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  have he : Real.log ((10000000000 : ℝ)/3023472737) =
      1*Real.log 2+Real.log ((5000000000/3023472737) : ℝ) := by
    rw [show ((5000000000/3023472737) : ℝ)=((10000000000 : ℝ)/3023472737)/2^1 by norm_num,
      Real.log_div (x := (10000000000 : ℝ)/3023472737) (y := (2 : ℝ)^1) (by norm_num) (by norm_num),Real.log_pow]
    ring
  rw [he]
  nlinarith [log_two_lower]

set_option maxHeartbeats 4000000 in
private theorem log_upper_1 : Real.log ((10000000000 : ℝ)/3023472736)<((11961791/10000000) : ℝ) := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤(11961791/10000000)) 32
  norm_num [Finset.sum_range_succ,Nat.factorial] at hs
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ)<10000000000/3023472736)).mpr
  linarith

theorem strip_energy_bounds_1 : ((5987/200000) : ℝ)<realEnergy (horizontalStrip 1) ∧
    realEnergy (horizontalStrip 1)<((149681/5000000) : ℝ) := by
  rw [RefinedQuadrantBoundary.strip_energy_exact (by decide : 1≤6),stripMatrix_det_1]
  have hd := stripDet1_bounds
  have hp : 0<stripDet1 (1/Real.pi) := lt_trans (by norm_num) hd.1
  have hl := Real.log_lt_log hp hd.2
  have hu := Real.log_lt_log (by norm_num : (0 : ℝ)<3023472736/10000000000) hd.1
  have hlogL := log_lower_1
  have hlogU := log_upper_1
  rw [show (10000000000 : ℝ)/3023472737=(3023472737/10000000000 : ℝ)⁻¹ by norm_num,Real.log_inv] at hlogL
  rw [show (10000000000 : ℝ)/3023472736=(3023472736/10000000000 : ℝ)⁻¹ by norm_num,Real.log_inv] at hlogU
  constructor <;> nlinarith [entropy_lower,entropy_upper]

set_option maxHeartbeats 2000000 in
private theorem log_lower_2 : ((5933297/2500000) : ℝ)<Real.log ((10000000000 : ℝ)/931709741) := by
  have hs := Real.hasSum_log_one_add (a := ((1250000000/931709741) : ℝ)-1) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 10) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  have he : Real.log ((10000000000 : ℝ)/931709741) =
      3*Real.log 2+Real.log ((1250000000/931709741) : ℝ) := by
    rw [show ((1250000000/931709741) : ℝ)=((10000000000 : ℝ)/931709741)/2^3 by norm_num,
      Real.log_div (x := (10000000000 : ℝ)/931709741) (y := (2 : ℝ)^3) (by norm_num) (by norm_num),Real.log_pow]
    ring
  rw [he]
  nlinarith [log_two_lower]

set_option maxHeartbeats 4000000 in
private theorem log_upper_2 : Real.log ((10000000000 : ℝ)/931709740)<((23733191/10000000) : ℝ) := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤(23733191/10000000)) 32
  norm_num [Finset.sum_range_succ,Nat.factorial] at hs
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ)<10000000000/931709740)).mpr
  linarith

theorem strip_energy_bounds_2 : ((40831/1000000) : ℝ)<realEnergy (horizontalStrip 2) ∧
    realEnergy (horizontalStrip 2)<((408333/10000000) : ℝ) := by
  rw [RefinedQuadrantBoundary.strip_energy_exact (by decide : 2≤6),stripMatrix_det_2]
  have hd := stripDet2_bounds
  have hp : 0<stripDet2 (1/Real.pi) := lt_trans (by norm_num) hd.1
  have hl := Real.log_lt_log hp hd.2
  have hu := Real.log_lt_log (by norm_num : (0 : ℝ)<931709740/10000000000) hd.1
  have hlogL := log_lower_2
  have hlogU := log_upper_2
  rw [show (10000000000 : ℝ)/931709741=(931709741/10000000000 : ℝ)⁻¹ by norm_num,Real.log_inv] at hlogL
  rw [show (10000000000 : ℝ)/931709740=(931709740/10000000000 : ℝ)⁻¹ by norm_num,Real.log_inv] at hlogU
  constructor <;> nlinarith [entropy_lower,entropy_upper]

set_option maxHeartbeats 2000000 in
private theorem log_lower_3 : ((35451007/10000000) : ℝ)<Real.log ((10000000000 : ℝ)/288657089) := by
  have hs := Real.hasSum_log_one_add (a := ((312500000/288657089) : ℝ)-1) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 10) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  have he : Real.log ((10000000000 : ℝ)/288657089) =
      5*Real.log 2+Real.log ((312500000/288657089) : ℝ) := by
    rw [show ((312500000/288657089) : ℝ)=((10000000000 : ℝ)/288657089)/2^5 by norm_num,
      Real.log_div (x := (10000000000 : ℝ)/288657089) (y := (2 : ℝ)^5) (by norm_num) (by norm_num),Real.log_pow]
    ring
  rw [he]
  nlinarith [log_two_lower]

set_option maxHeartbeats 4000000 in
private theorem log_upper_3 : Real.log ((10000000000 : ℝ)/288657088)<((8862753/2500000) : ℝ) := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤(8862753/2500000)) 32
  norm_num [Finset.sum_range_succ,Nat.factorial] at hs
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ)<10000000000/288657088)).mpr
  linarith

theorem strip_energy_bounds_3 : ((46369/1000000) : ℝ)<realEnergy (horizontalStrip 3) ∧
    realEnergy (horizontalStrip 3)<((18549/400000) : ℝ) := by
  rw [RefinedQuadrantBoundary.strip_energy_exact (by decide : 3≤6),stripMatrix_det_3]
  have hd := stripDet3_bounds
  have hp : 0<stripDet3 (1/Real.pi) := lt_trans (by norm_num) hd.1
  have hl := Real.log_lt_log hp hd.2
  have hu := Real.log_lt_log (by norm_num : (0 : ℝ)<288657088/10000000000) hd.1
  have hlogL := log_lower_3
  have hlogU := log_upper_3
  rw [show (10000000000 : ℝ)/288657089=(288657089/10000000000 : ℝ)⁻¹ by norm_num,Real.log_inv] at hlogL
  rw [show (10000000000 : ℝ)/288657088=(288657088/10000000000 : ℝ)⁻¹ by norm_num,Real.log_inv] at hlogU
  constructor <;> nlinarith [entropy_lower,entropy_upper]

set_option maxHeartbeats 2000000 in
private theorem log_lower_4 : ((47147081/10000000) : ℝ)<Real.log ((10000000000 : ℝ)/89624789) := by
  have hs := Real.hasSum_log_one_add (a := ((156250000/89624789) : ℝ)-1) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 10) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  have he : Real.log ((10000000000 : ℝ)/89624789) =
      6*Real.log 2+Real.log ((156250000/89624789) : ℝ) := by
    rw [show ((156250000/89624789) : ℝ)=((10000000000 : ℝ)/89624789)/2^6 by norm_num,
      Real.log_div (x := (10000000000 : ℝ)/89624789) (y := (2 : ℝ)^6) (by norm_num) (by norm_num),Real.log_pow]
    ring
  rw [he]
  nlinarith [log_two_lower]

set_option maxHeartbeats 4000000 in
private theorem log_upper_4 : Real.log ((10000000000 : ℝ)/89624788)<((23573543/5000000) : ℝ) := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤(23573543/5000000)) 32
  norm_num [Finset.sum_range_succ,Nat.factorial] at hs
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ)<10000000000/89624788)).mpr
  linarith

theorem strip_energy_bounds_4 : ((19893/400000) : ℝ)<realEnergy (horizontalStrip 4) ∧
    realEnergy (horizontalStrip 4)<((49737/1000000) : ℝ) := by
  rw [RefinedQuadrantBoundary.strip_energy_exact (by decide : 4≤6),stripMatrix_det_4]
  have hd := stripDet4_bounds
  have hp : 0<stripDet4 (1/Real.pi) := lt_trans (by norm_num) hd.1
  have hl := Real.log_lt_log hp hd.2
  have hu := Real.log_lt_log (by norm_num : (0 : ℝ)<89624788/10000000000) hd.1
  have hlogL := log_lower_4
  have hlogU := log_upper_4
  rw [show (10000000000 : ℝ)/89624789=(89624789/10000000000 : ℝ)⁻¹ by norm_num,Real.log_inv] at hlogL
  rw [show (10000000000 : ℝ)/89624788=(89624788/10000000000 : ℝ)⁻¹ by norm_num,Real.log_inv] at hlogU
  constructor <;> nlinarith [entropy_lower,entropy_upper]

set_option maxHeartbeats 2000000 in
private theorem log_lower_5 : ((11766439/2000000) : ℝ)<Real.log ((10000000000 : ℝ)/27858012) := by
  have hs := Real.hasSum_log_one_add (a := ((9765625/6964503) : ℝ)-1) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 10) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  have he : Real.log ((10000000000 : ℝ)/27858012) =
      8*Real.log 2+Real.log ((9765625/6964503) : ℝ) := by
    rw [show ((9765625/6964503) : ℝ)=((10000000000 : ℝ)/27858012)/2^8 by norm_num,
      Real.log_div (x := (10000000000 : ℝ)/27858012) (y := (2 : ℝ)^8) (by norm_num) (by norm_num),Real.log_pow]
    ring
  rw [he]
  nlinarith [log_two_lower]

set_option maxHeartbeats 4000000 in
private theorem log_upper_5 : Real.log ((10000000000 : ℝ)/27858011)<((294161/50000) : ℝ) := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤(294161/50000)) 32
  norm_num [Finset.sum_range_succ,Nat.factorial] at hs
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ)<10000000000/27858011)).mpr
  linarith

theorem strip_energy_bounds_5 : ((13/250) : ℝ)<realEnergy (horizontalStrip 5) ∧
    realEnergy (horizontalStrip 5)<((104011/2000000) : ℝ) := by
  rw [RefinedQuadrantBoundary.strip_energy_exact (by decide : 5≤6),stripMatrix_det_5]
  have hd := stripDet5_bounds
  have hp : 0<stripDet5 (1/Real.pi) := lt_trans (by norm_num) hd.1
  have hl := Real.log_lt_log hp hd.2
  have hu := Real.log_lt_log (by norm_num : (0 : ℝ)<27858011/10000000000) hd.1
  have hlogL := log_lower_5
  have hlogU := log_upper_5
  rw [show (10000000000 : ℝ)/27858012=(27858012/10000000000 : ℝ)⁻¹ by norm_num,Real.log_inv] at hlogL
  rw [show (10000000000 : ℝ)/27858011=(27858011/10000000000 : ℝ)⁻¹ by norm_num,Real.log_inv] at hlogU
  constructor <;> nlinarith [entropy_lower,entropy_upper]

set_option maxHeartbeats 2000000 in
private theorem log_lower_6 : ((70510989/10000000) : ℝ)<Real.log ((10000000000 : ℝ)/8664559) := by
  have hs := Real.hasSum_log_one_add (a := ((9765625/8664559) : ℝ)-1) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 10) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  have he : Real.log ((10000000000 : ℝ)/8664559) =
      10*Real.log 2+Real.log ((9765625/8664559) : ℝ) := by
    rw [show ((9765625/8664559) : ℝ)=((10000000000 : ℝ)/8664559)/2^10 by norm_num,
      Real.log_div (x := (10000000000 : ℝ)/8664559) (y := (2 : ℝ)^10) (by norm_num) (by norm_num),Real.log_pow]
    ring
  rw [he]
  nlinarith [log_two_lower]

set_option maxHeartbeats 4000000 in
private theorem log_upper_6 : Real.log ((10000000000 : ℝ)/8664558)<((70510999/10000000) : ℝ) := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ)≤(70510999/10000000)) 32
  norm_num [Finset.sum_range_succ,Nat.factorial] at hs
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ)<10000000000/8664558)).mpr
  linarith

theorem strip_energy_bounds_6 : ((107271/2000000) : ℝ)<realEnergy (horizontalStrip 6) ∧
    realEnergy (horizontalStrip 6)<((21457/400000) : ℝ) := by
  rw [RefinedQuadrantBoundary.strip_energy_exact (by decide : 6≤6),stripMatrix_det_6]
  have hd := stripDet6_bounds
  have hp : 0<stripDet6 (1/Real.pi) := lt_trans (by norm_num) hd.1
  have hl := Real.log_lt_log hp hd.2
  have hu := Real.log_lt_log (by norm_num : (0 : ℝ)<8664558/10000000000) hd.1
  have hlogL := log_lower_6
  have hlogU := log_upper_6
  rw [show (10000000000 : ℝ)/8664559=(8664559/10000000000 : ℝ)⁻¹ by norm_num,Real.log_inv] at hlogL
  rw [show (10000000000 : ℝ)/8664558=(8664558/10000000000 : ℝ)⁻¹ by norm_num,Real.log_inv] at hlogU
  constructor <;> nlinarith [entropy_lower,entropy_upper]

end
end SpanningTreeIsoperimetry.RefinedStripEnergy
