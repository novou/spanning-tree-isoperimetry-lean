import SpanningTreeIsoperimetry.SmallFamilyMonotonicity
import SpanningTreeIsoperimetry.SmallFamilyProfiles
import Mathlib.Analysis.Real.Pi.Bounds

/-! Exact endpoint certificates for the inverse-fourth correction profiles
in the small-family and rectangular-notch comparisons. -/
namespace SpanningTreeIsoperimetry.SmallFamilyDerivativeChecks
open SmallFamilyMonotonicity SmallFamilyProfiles Set
open scoped BigOperators
noncomputable section


theorem geometric_conditions (j : Fin 26) :
    0≤gap j ∧ 0<hullShift j ∧ 3*hullShift j≤leftEnd j ∧
      ∀ i : Fin 4, 0≤coeff j i ∧ 0≤shifts i ∧ shifts i<leftEnd j := by
  fin_cases j <;> norm_num [gap,hullShift,leftEnd,coeff,shifts] <;>
    intro i <;> fin_cases i <;> norm_num

set_option maxHeartbeats 2000000 in
theorem endpoint_checked (j : Fin 26) :
    normalizedWeight Finset.univ (coeff j) shifts (leftEnd j)≤
      normalizedSlope (gap j) (hullShift j) (leftEnd j) := by
  have hp : (157/50 : ℝ)<Real.pi := by linarith [Real.pi_gt_d2]
  fin_cases j <;>
    norm_num [normalizedWeight,normalizedSlope,gap,hullShift,leftEnd,coeff,shifts,Fin.sum_univ_succ] <;>
    nlinarith only [hp]

/-- Every listed weighted aspect profile decreases on its certified range.
Rows6/7 start at6; their separate integer endpoint5 is checked with the cost. -/
theorem profile_antitone (j : Fin 26) :
    AntitoneOn (fun r : ℝ => aspectStep (gap j) (hullShift j) r-
      weightedLoss Finset.univ (coeff j) shifts r) (Ici (leftEnd j)) := by
  have h := geometric_conditions j
  exact corrected_aspect_antitone Finset.univ (coeff j) shifts h.1 h.2.1 h.2.2.1
    (fun i _ => (h.2.2.2 i).1) (fun i _ => (h.2.2.2 i).2.1)
    (fun i _ => (h.2.2.2 i).2.2) (endpoint_checked j)

set_option maxHeartbeats 1000000 in
theorem odd_two_endpoint (j : Fin 6) :
    normalizedWeight ({0} : Finset ℕ) (fun _ => 5*((j.val : ℝ)+4)/3) (fun _ => 0) (j.val+7)≤
      normalizedSlope 1 2 (j.val+7) := by
  have hp : (157/50 : ℝ)<Real.pi := by linarith [Real.pi_gt_d2]
  fin_cases j <;> norm_num [normalizedWeight,normalizedSlope] <;> nlinarith only [hp]

theorem odd_two_profile_antitone (j : Fin 6) :
    AntitoneOn (fun r : ℝ => aspectStep 1 2 r-
      (5*((j.val : ℝ)+4)/3)/r^4) (Ici (j.val+7)) := by
  have hj := Nat.cast_nonneg (α := ℝ) j.val
  have h := corrected_aspect_antitone ({0} : Finset ℕ) (fun _ => 5*((j.val : ℝ)+4)/3)
    (fun _ => 0) (by norm_num : (0 : ℝ)≤1) (by norm_num : (0 : ℝ)<2)
    (by linarith : (3 : ℝ)*2≤(j.val : ℝ)+7)
    (fun i hi => by positivity) (fun i hi => by norm_num) (fun i hi => by linarith)
    (odd_two_endpoint j)
  simpa only [weightedLoss,Finset.sum_singleton,sub_zero] using h

end
end SpanningTreeIsoperimetry.SmallFamilyDerivativeChecks
