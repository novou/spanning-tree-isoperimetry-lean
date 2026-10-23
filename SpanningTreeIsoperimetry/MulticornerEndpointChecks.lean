module

public import SpanningTreeIsoperimetry.FixedStripEnergyUpper
public import SpanningTreeIsoperimetry.SmallFamilyProfiles
public import SpanningTreeIsoperimetry.SmallFamilyCostData
public import SpanningTreeIsoperimetry.RefinedStripEnergy
public import SpanningTreeIsoperimetry.RefinedObstructionEnergy_ell
public import SpanningTreeIsoperimetry.RefinedObstructionEnergy_square
public import SpanningTreeIsoperimetry.RefinedObstructionEnergy_rectangle23

@[expose] public section

/-! Exact small-family endpoint comparisons. All finite target energies,
logarithms, and quadrant-energy bounds are checked within the project. -/
namespace SpanningTreeIsoperimetry.MulticornerEndpointChecks
open Ferrers CornerEnergy CrossHullCountComparison FixedStripEnergyUpper
open SmallFamilyProfiles SmallFamilyMonotonicity SmallFamilyCosts RefinedStripEnergy FluxBounds
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def piUpper : ℝ := 31415927/10000000

theorem pi_le_upper : Real.pi≤piUpper := by unfold piUpper; linarith [Real.pi_lt_d20]

def logLower (x : ℝ) : ℝ := ∑ n∈Finset.range 8,
  2*(1/(2*(n : ℝ)+1))*(x/(x+2))^(2*n+1)

theorem logLower_le {x : ℝ} (hx : 0≤x) : logLower x≤Real.log (1+x) := by
  exact sum_le_hasSum (Finset.range 8) (fun n _ => by positivity) (Real.hasSum_log_one_add hx)

def rationalAspect (a h r : ℝ) : ℝ :=
  piUpper*h*(2*r+a)/(12*r*(r-h))-(1/2)*logLower (h/(r-h))

theorem aspectStep_le_rational {a h r : ℝ} (ha : 0≤a) (hh : 0<h) (hr : h<r) :
    aspectStep a h r≤rationalAspect a h r := by
  have hr0 : 0<r := hh.trans hr
  have hden : 0<r-h := by linarith
  have hl := logLower_le (show 0≤h/(r-h) by positivity)
  have he : 1+h/(r-h)=r/(r-h) := by field_simp; ring
  rw [he] at hl
  have hp : Real.pi*h*(2*r+a)/(12*r*(r-h))≤piUpper*h*(2*r+a)/(12*r*(r-h)) := by
    gcongr
    exact pi_le_upper
  rw [aspectStep_eq ha hh hr]
  unfold rationalAspect
  linarith only [hp,hl]

def rationalFlux (r s k : ℝ) : ℝ :=
  piUpper^3/60*((cubic k/3)*(1/(r^2-4)^2+1/(s^2-k^2)^2)+
    quadratic k*(1/(r^2-1)^2+1/(s^2-(k+1)^2)^2))

theorem flux_le_rational (r s : ℝ) {k : ℝ} (hk : 0≤k) : fluxBound r s k≤rationalFlux r s k := by
  have hpi := pow_le_pow_left₀ Real.pi_pos.le pi_le_upper 3
  have hfac : 0≤(cubic k/3)*(1/(r^2-4)^2+1/(s^2-k^2)^2)+
      quadratic k*(1/(r^2-1)^2+1/(s^2-(k+1)^2)^2) := by unfold cubic quadratic; positivity
  unfold fluxBound rationalFlux
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpi (by norm_num)) hfac

def targetCap : Fin 9 → ℝ := ![0,
  finiteTargetEnergy (by decide : 2≤4) (by decide : 1≤6-1),
  finiteTargetEnergy (by decide : 2≤4) (by decide : 2≤6-1),
  finiteTargetEnergy (by decide : 2≤4) (by decide : 2≤7-1),
  finiteTargetEnergy (by decide : 2≤5) (by decide : 2≤7-1),
  finiteTargetEnergy (by decide : 2≤5) (by decide : 3≤8-1),
  finiteTargetEnergy (by decide : 2≤6) (by decide : 3≤10-1),
  finiteTargetEnergy (by decide : 2≤7) (by decide : 4≤11-1),
  realEnergy (horizontalStrip 2)+fluxBound 7 12 2]

def targetUpper : Fin 9 → ℝ := ![0,37266/1000000,62474/1000000,61659/1000000,
  50390/1000000,64522/1000000,55677/1000000,58904/1000000,
  408333/10000000+rationalFlux 7 12 2]

theorem targetCap_le_upper (i : Fin 9) : targetCap i≤targetUpper i := by
  fin_cases i <;> simp only [targetCap,targetUpper,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons]
  · exact le_refl _
  · exact energy_1_4_6.le
  · exact energy_2_4_6.le
  · exact energy_2_4_7.le
  · exact energy_2_5_7.le
  · exact energy_3_5_8.le
  · exact energy_3_6_10.le
  · exact energy_4_7_11.le
  · exact add_le_add strip_energy_bounds_2.2.le (flux_le_rational 7 12 (by norm_num))

def quadrantValue : Fin 26 → ℝ := ![2*realEnergy (horizontalStrip 1),
  2*realEnergy (horizontalStrip 1),
  3*realEnergy (horizontalStrip 1),
  realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip 2),
  3*realEnergy (horizontalStrip 1),
  realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip 2),
  realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip 3),
  realEnergy (horizontalStrip 1)+realEnergy RefinedObstructionPolynomials.ell.diagram,
  2*realEnergy (horizontalStrip 2),
  3*realEnergy (horizontalStrip 1),
  realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip 3),
  realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip 4),
  realEnergy (horizontalStrip 1)+realEnergy RefinedObstructionPolynomials.square.diagram,
  realEnergy (horizontalStrip 1)+realEnergy RefinedObstructionPolynomials.ell.diagram,
  realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip 4),
  realEnergy (horizontalStrip 1)+realEnergy RefinedObstructionPolynomials.square.diagram,
  realEnergy (horizontalStrip 1)+realEnergy RefinedObstructionPolynomials.square.diagram,
  realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip 5),
  2*realEnergy (horizontalStrip 3),
  realEnergy (horizontalStrip 2)+realEnergy RefinedObstructionPolynomials.square.diagram,
  realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip 6),
  realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip 5),
  realEnergy (horizontalStrip 1)+realEnergy (horizontalStrip 6),
  realEnergy RefinedObstructionPolynomials.square.diagram,
  realEnergy RefinedObstructionPolynomials.rectangle23.diagram,
  realEnergy RefinedObstructionPolynomials.ell.diagram]

def quadrantFloor : Fin 26 → ℝ := ![2*(5987/200000),
  2*(5987/200000),
  3*(5987/200000),
  (5987/200000)+(40831/1000000),
  3*(5987/200000),
  (5987/200000)+(40831/1000000),
  (5987/200000)+(46369/1000000),
  (5987/200000)+(3357/50000),
  2*(40831/1000000),
  3*(5987/200000),
  (5987/200000)+(46369/1000000),
  (5987/200000)+(19893/400000),
  (5987/200000)+(2837/50000),
  (5987/200000)+(3357/50000),
  (5987/200000)+(19893/400000),
  (5987/200000)+(2837/50000),
  (5987/200000)+(2837/50000),
  (5987/200000)+(13/250),
  2*(46369/1000000),
  (40831/1000000)+(2837/50000),
  (5987/200000)+(107271/2000000),
  (5987/200000)+(13/250),
  (5987/200000)+(107271/2000000),
  (2837/50000),
  (3261/50000),
  (3357/50000)]

theorem quadrantFloor_lt (i : Fin 26) : quadrantFloor i<quadrantValue i := by
  have h1 := strip_energy_bounds_1.1
  have h2 := strip_energy_bounds_2.1
  have h3 := strip_energy_bounds_3.1
  have h4 := strip_energy_bounds_4.1
  have h5 := strip_energy_bounds_5.1
  have h6 := strip_energy_bounds_6.1
  have hl := RefinedObstructionEnergy.ell.energy_lower
  have hs := RefinedObstructionEnergy.square.energy_lower
  have hr := RefinedObstructionEnergy.rectangle23.energy_lower
  fin_cases i <;> norm_num [quadrantFloor,quadrantValue] <;>
    linarith only [h1,h2,h3,h4,h5,h6,hl,hs,hr]

def endpointCost (i : Fin 26) (r : ℝ) : ℝ :=
  upperCost (targetCap (targetCapKind i)) (errorCoeff i) (sourceShift i)
    (gap i) (hullShift i) Finset.univ (coeff i) shifts r

def rationalCost (i : Fin 26) (r : ℝ) : ℝ :=
  targetUpper (targetCapKind i)+rationalAspect (gap i) (hullShift i) r+
    remainderBound (errorCoeff i) (hullShift i) (sourceShift i)
      (hullShift i*(gap i+hullShift i)) r-weightedLoss Finset.univ (coeff i) shifts r

theorem endpointCost_le {i : Fin 26} {r : ℝ} (hr : hullShift i<r) :
    endpointCost i r≤rationalCost i r := by
  have ha : 0≤gap i := by fin_cases i <;> norm_num [gap]
  have hh : 0<hullShift i := by fin_cases i <;> norm_num [hullShift]
  have hc := targetCap_le_upper (targetCapKind i)
  have hf := aspectStep_le_rational ha hh hr
  unfold endpointCost upperCost rationalCost
  linarith only [hc,hf]

theorem rational_endpoint (i : Fin 26) : rationalCost i (leftEnd i)<quadrantFloor i := by
  fin_cases i <;>
    norm_num [rationalCost,rationalAspect,logLower,rationalFlux,piUpper,targetUpper,targetCapKind,
      remainderBound,weightedLoss,cubic,quadratic,gap,hullShift,leftEnd,coeff,shifts,errorCoeff,sourceShift,
      quadrantFloor,Fin.sum_univ_succ,Finset.sum_range_succ]

theorem profile_endpoint (i : Fin 26) : endpointCost i (leftEnd i)<quadrantValue i := by
  have hr : hullShift i<leftEnd i := by fin_cases i <;> norm_num [hullShift,leftEnd]
  exact (endpointCost_le hr).trans_lt ((rational_endpoint i).trans (quadrantFloor_lt i))

theorem extra_five_endpoint {i : Fin 26} (hi : i=6 ∨ i=7 ∨ i=23) :
    endpointCost i 5<quadrantValue i := by
  have hr : hullShift i<(5 : ℝ) := by rcases hi with rfl|rfl|rfl <;> norm_num [hullShift]
  apply (endpointCost_le hr).trans_lt
  apply lt_trans _ (quadrantFloor_lt i)
  rcases hi with rfl|rfl|rfl <;>
    norm_num [rationalCost,rationalAspect,logLower,rationalFlux,piUpper,targetUpper,targetCapKind,
      remainderBound,weightedLoss,cubic,quadratic,gap,hullShift,coeff,shifts,errorCoeff,sourceShift,
      quadrantFloor,Fin.sum_univ_succ,Finset.sum_range_succ]


def stripUpper : Fin 6 → ℝ :=
  ![0,149681/5000000,408333/10000000,18549/400000,49737/1000000,104011/2000000]

theorem strip_le_upper (j : Fin 6) : realEnergy (horizontalStrip j.val)≤stripUpper j := by
  fin_cases j <;> simp only [stripUpper,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons]
  · have he : horizontalStrip 0=(∅ : Diagram) := by decide +kernel
    rw [he,realEnergy_empty]
    exact le_refl 0
  · exact strip_energy_bounds_1.2.le
  · exact strip_energy_bounds_2.2.le
  · exact strip_energy_bounds_3.2.le
  · exact strip_energy_bounds_4.2.le
  · exact strip_energy_bounds_5.2.le

def oddTwoCost (j : Fin 6) : ℝ :=
  realEnergy (horizontalStrip j.val)+aspectStep 1 2 (j.val+7)+
    fluxBound (j.val+5) (j.val+10) j.val

def oddTwoFloor (j : Fin 6) : ℝ :=
  (5987/200000 : ℝ)+(if j=0 then 46369/1000000 else 19893/400000)

theorem odd_two_normalized_endpoint (j : Fin 6) :
    oddTwoCost j<realEnergy (horizontalStrip 1)+
      realEnergy (horizontalStrip (if j=0 then 3 else 4)) := by
  have hE := strip_le_upper j
  have hA := aspectStep_le_rational (by norm_num : (0 : ℝ)≤1) (by norm_num : (0 : ℝ)<2)
    (show (2 : ℝ)<(j.val : ℝ)+7 by have hj := Nat.cast_nonneg (α := ℝ) j.val; linarith)
  have hB := flux_le_rational ((j.val : ℝ)+5) ((j.val : ℝ)+10) (Nat.cast_nonneg (α := ℝ) j.val)
  have hn : stripUpper j+rationalAspect 1 2 (j.val+7)+
      rationalFlux (j.val+5) (j.val+10) j.val<oddTwoFloor j := by
    fin_cases j <;> norm_num [stripUpper,rationalAspect,rationalFlux,logLower,piUpper,
      cubic,quadratic,oddTwoFloor,Finset.sum_range_succ]
  have hq : oddTwoFloor j<realEnergy (horizontalStrip 1)+
      realEnergy (horizontalStrip (if j=0 then 3 else 4)) := by
    by_cases he : j=0
    · simp only [oddTwoFloor,if_pos he]
      linarith only [strip_energy_bounds_1.1,strip_energy_bounds_3.1]
    · simp only [oddTwoFloor,if_neg he]
      linarith only [strip_energy_bounds_1.1,strip_energy_bounds_4.1]
  unfold oddTwoCost
  linarith only [hE,hA,hB,hn,hq]


def singleOddCost (j : Fin 6) : ℝ :=
  realEnergy (horizontalStrip j.val)+aspectStep 3 1 (j.val+6)+
    fluxBound (j.val+5) (j.val+10) j.val

theorem single_odd_endpoint (j : Fin 6) :
    singleOddCost j<(if j=0 then (2837 : ℝ)/50000 else 7421/100000) := by
  have hE := strip_le_upper j
  have hA := aspectStep_le_rational (by norm_num : (0 : ℝ)≤3) (by norm_num : (0 : ℝ)<1)
    (show (1 : ℝ)<(j.val : ℝ)+6 by have hj := Nat.cast_nonneg (α := ℝ) j.val; linarith)
  have hB := flux_le_rational ((j.val : ℝ)+5) ((j.val : ℝ)+10) (Nat.cast_nonneg (α := ℝ) j.val)
  have hn : stripUpper j+rationalAspect 3 1 (j.val+6)+
      rationalFlux (j.val+5) (j.val+10) j.val<
        (if j=0 then (2837 : ℝ)/50000 else 7421/100000) := by
    fin_cases j <;> norm_num [stripUpper,rationalAspect,rationalFlux,logLower,piUpper,
      cubic,quadratic,Finset.sum_range_succ]
  unfold singleOddCost
  linarith only [hE,hA,hB,hn]

def stripUpperEight : Fin 8 → ℝ :=
  ![0,149681/5000000,408333/10000000,18549/400000,49737/1000000,104011/2000000,
    21457/400000,2*(21457/400000)-13/250]

theorem strip_le_upper_eight (j : Fin 8) : realEnergy (horizontalStrip j.val)≤stripUpperEight j := by
  fin_cases j <;> simp only [stripUpperEight,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons]
  · have he : horizontalStrip 0=(∅ : Diagram) := by decide +kernel
    rw [he,realEnergy_empty]
    exact le_refl 0
  · exact strip_energy_bounds_1.2.le
  · exact strip_energy_bounds_2.2.le
  · exact strip_energy_bounds_3.2.le
  · exact strip_energy_bounds_4.2.le
  · exact strip_energy_bounds_5.2.le
  · exact strip_energy_bounds_6.2.le
  · change realEnergy (horizontalStrip 7)≤2*(21457/400000)-13/250
    have hc := realEnergy_strip_concave 5
    norm_num at hc
    linarith only [hc,strip_energy_bounds_6.2,strip_energy_bounds_5.1]

def rangeStart : Fin 6 → ℝ := ![0,2,4,0,2,4]
def rangeEnd : Fin 6 → Fin 8 := ![1,3,6,1,3,7]
def shallowGap : Fin 6 → ℝ := ![4,4,4,3,3,3]
def shallowShift : Fin 6 → ℝ := ![1,1,1,2,2,2]
def sourceBase : Fin 6 → ℝ := ![8,8,8,12,12,12]
def fluxShortBase : Fin 6 → ℝ := ![7,7,7,10,10,10]
def fluxLongBase : Fin 6 → ℝ := ![13,13,13,17,17,17]
def shallowUpper : Fin 6 → ℝ := ![574/10000,662/10000,711/10000,569/10000,669/10000,732/10000]

def shallowCost (i : Fin 6) : ℝ :=
  realEnergy (horizontalStrip (rangeEnd i).val)+
    aspectStep (shallowGap i) (shallowShift i) (rangeStart i+sourceBase i)+
    fluxBound ((rangeEnd i).val+fluxShortBase i) ((rangeEnd i).val+fluxLongBase i) (rangeEnd i).val

theorem shallow_three_endpoint (i : Fin 6) : shallowCost i<shallowUpper i := by
  have hE := strip_le_upper_eight (rangeEnd i)
  have ha : 0≤shallowGap i := by fin_cases i <;> norm_num [shallowGap]
  have hh : 0<shallowShift i := by fin_cases i <;> norm_num [shallowShift]
  have hr : shallowShift i<rangeStart i+sourceBase i := by
    fin_cases i <;> norm_num [shallowShift,rangeStart,sourceBase]
  have hA := aspectStep_le_rational ha hh hr
  have hB := flux_le_rational ((rangeEnd i).val+fluxShortBase i) ((rangeEnd i).val+fluxLongBase i)
    (Nat.cast_nonneg (α := ℝ) (rangeEnd i).val)
  have hn : stripUpperEight (rangeEnd i)+
      rationalAspect (shallowGap i) (shallowShift i) (rangeStart i+sourceBase i)+
      rationalFlux ((rangeEnd i).val+fluxShortBase i) ((rangeEnd i).val+fluxLongBase i) (rangeEnd i).val<
      shallowUpper i := by
    fin_cases i <;> norm_num [stripUpperEight,rangeEnd,rationalAspect,rationalFlux,logLower,piUpper,
      cubic,quadratic,rangeStart,shallowGap,shallowShift,sourceBase,fluxShortBase,fluxLongBase,
      shallowUpper,Finset.sum_range_succ]
  unfold shallowCost
  linarith only [hE,hA,hB,hn]

end
end SpanningTreeIsoperimetry.MulticornerEndpointChecks
