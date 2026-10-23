module

public import SpanningTreeIsoperimetry.SmallFamilyCosts
public import SpanningTreeIsoperimetry.MulticornerEndpointChecks

@[expose] public section

/-! Uniform cost bounds from the checked finite profile endpoints. -/
namespace SpanningTreeIsoperimetry.SmallFamilyCostBounds
open SmallFamilyProfiles SmallFamilyDerivativeChecks SmallFamilyCosts
  MulticornerEndpointChecks Set
noncomputable section

theorem endpointCost_antitone (i : Fin 26) :
    AntitoneOn (endpointCost i) (Ici (leftEnd i)) := by
  have h := geometric_conditions i
  have hq : 0≤errorCoeff i := by fin_cases i <;> norm_num [errorCoeff]
  have hs : sourceShift i≤hullShift i := by
    fin_cases i <;> norm_num [sourceShift,hullShift]
  exact upperCost_antitone _ _ _ Finset.univ (coeff i) shifts hq hs
    h.1 h.2.1 h.2.2.1 (fun j _ => (h.2.2.2 j).1)
    (fun j _ => (h.2.2.2 j).2.1) (fun j _ => (h.2.2.2 j).2.2)
    (endpoint_checked i)

theorem endpointCost_lt_floor (i : Fin 26) {r : ℝ} (hr : leftEnd i≤r) :
    endpointCost i r<quadrantFloor i := by
  have h := geometric_conditions i
  have hp : hullShift i<leftEnd i := by linarith [h.2.1,h.2.2.1]
  exact (endpointCost_antitone i (show leftEnd i∈Ici (leftEnd i) by change leftEnd i≤leftEnd i; exact le_refl (leftEnd i))
    (show r∈Ici (leftEnd i) from hr) hr).trans_lt
    ((endpointCost_le hp).trans_lt (rational_endpoint i))

theorem endpointCost_lt (i : Fin 26) {r : ℝ} (hr : leftEnd i≤r) :
    endpointCost i r<quadrantValue i :=
  (endpointCost_lt_floor i hr).trans (quadrantFloor_lt i)

theorem extra_five_lt_floor {i : Fin 26} (hi : i=6 ∨ i=7 ∨ i=23) :
    endpointCost i 5<quadrantFloor i := by
  have hr : hullShift i<(5 : ℝ) := by
    rcases hi with rfl|rfl|rfl <;> norm_num [hullShift]
  apply (endpointCost_le hr).trans_lt
  rcases hi with rfl|rfl|rfl <;>
    norm_num [rationalCost,rationalAspect,logLower,rationalFlux,piUpper,targetUpper,targetCapKind,
      remainderBound,SmallFamilyMonotonicity.weightedLoss,FluxBounds.cubic,FluxBounds.quadratic,
      gap,hullShift,coeff,shifts,errorCoeff,sourceShift,quadrantFloor,
      Fin.sum_univ_succ,Finset.sum_range_succ]

end
end SpanningTreeIsoperimetry.SmallFamilyCostBounds
