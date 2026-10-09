import SpanningTreeIsoperimetry.CanonicalAsymptoticGeometry
import SpanningTreeIsoperimetry.FirstProfileQuadratic

/-! The actual canonical strip has the full O(N^(-1/2)) count expansion.
Replacing its count by the global maximum is a separate classification step. -/
namespace SpanningTreeIsoperimetry.CanonicalCountAsymptotic
open CanonicalCountExpansion CanonicalAsymptoticGeometry FirstProfileQuadratic
open RectangularRemainder Filter Asymptotics
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000

def mainTerm (N : ℕ) : ℝ := SquareMaximality.squareLatticeEntropy*N-
  Real.log (1+Real.sqrt 2)*minimumSideSum N-(1/4)*Real.log (N : ℝ)+squareConstant-
    CornerEnergy.realEnergy (Ferrers.horizontalStrip (stripLength N))

theorem remainder_le_reciprocal {C ε : ℝ} (hC : 0<C)
    (hquad : ∀ u : ℝ, 1≤u → u≤1+ε → |J u-J 1|≤C*(u-1)^2)
    {N : ℕ} (hN : 0<N) (hr4 : 4≤shortSide N) (hu : aspect N≤1+ε) :
    |canonicalRemainder N|≤(18*C+16*Real.pi^3/45+1)/(shortSide N : ℝ) := by
  let a := J (aspect N)-squareConstant
  let e := error (shortSide N) (longSide N)
  let c := stripCorrection N
  let l := Real.log (1+(stripLength N : ℝ)/N)
  have hp := properties hN
  have hr0 : (0 : ℝ)<shortSide N := by exact_mod_cast hp.1
  have hr1 : (1 : ℝ)≤shortSide N := by exact_mod_cast (show 1≤shortSide N by omega)
  have hJ : |a|≤18*C/(shortSide N : ℝ) := by
    have hh := hquad (aspect N) (aspect_ge_one hN) hu
    rw [← squareConstant_eq_J_one] at hh
    calc
      |a|≤C*(aspect N-1)^2 := hh
      _≤C*(18/(shortSide N : ℝ)) := mul_le_mul_of_nonneg_left (aspect_offset_sq_le hN) hC.le
      _=_ := by ring
  have he : |e|≤(1/2 : ℝ)/(shortSide N : ℝ) := by
    have hh := UniformRectangleError.error_uniform hp.1 hp.2.1 (long_le_three_short hN)
    have hsq : (shortSide N : ℝ)≤(shortSide N : ℝ)^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hr1) hr0.le]
    calc
      |e|≤1/(2*(shortSide N : ℝ)^2) := hh
      _≤1/(2*(shortSide N : ℝ)) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      _=_ := by field_simp [hr0.ne'] <;> ring
  have hc : |c|≤(16*Real.pi^3/45)/(shortSide N : ℝ) := stripCorrection_le_reciprocal hN hr4
  have hl : |l|≤2/(shortSide N : ℝ) := log_area_ratio_bound hN
  have ht1 := abs_add_le a e
  have ht2 : |a+e-c|≤|a+e|+|c| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (a+e) (-c)
  have ht3 : |a+e-c-(1/4)*l|≤|a+e-c|+(1/4)*|l| := by
    simpa only [sub_eq_add_neg,abs_neg,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ)≤1/4)]
      using abs_add_le (a+e-c) (-((1/4)*l))
  change |a+e-c-(1/4)*l|≤_
  calc
    _≤18*C/(shortSide N : ℝ)+(1/2 : ℝ)/(shortSide N : ℝ)+
        (16*Real.pi^3/45)/(shortSide N : ℝ)+(1/4)*(2/(shortSide N : ℝ)) := by
      linarith only [hJ,he,hc,hl,ht1,ht2,ht3]
    _=_ := by ring

theorem canonicalRemainder_isBigO :
    canonicalRemainder=O[atTop] (fun N : ℕ => 1/Real.sqrt (N : ℝ)) := by
  obtain ⟨C,ε,hC,hε,hquad⟩ := exists_quadratic_bound
  let A := 18*C+16*Real.pi^3/45+1
  have hA : 0≤A := by dsimp [A]; positivity
  have hu : ∀ᶠ N in atTop, aspect N≤1+ε :=
    aspect_tendsto.eventually (eventually_le_nhds (show (1 : ℝ)<1+ε by linarith))
  apply Asymptotics.IsBigO.of_bound (2*A)
  filter_upwards [eventually_ge_atTop 1,tendsto_atTop.1 shortSide_tendsto 4,hu] with N hN hr hau
  have hb := remainder_le_reciprocal hC hquad (show 0<N by omega) hr hau
  have hi := reciprocal_short_le_sqrt (show 0<N by omega)
  simp only [Real.norm_eq_abs,abs_of_nonneg (by positivity : (0 : ℝ)≤1/Real.sqrt (N : ℝ))]
  calc
    |canonicalRemainder N|≤A/(shortSide N : ℝ) := hb
    _=A*(1/(shortSide N : ℝ)) := by ring
    _≤A*(2/Real.sqrt (N : ℝ)) := mul_le_mul_of_nonneg_left hi hA
    _=(2*A)*(1/Real.sqrt (N : ℝ)) := by ring

theorem canonical_count_asymptotic :
    (fun N : ℕ => Real.log (treeCount (canonicalDomain N) : ℝ)-mainTerm N)=O[atTop]
      (fun N : ℕ => 1/Real.sqrt (N : ℝ)) := by
  obtain ⟨C,hC⟩ := canonicalRemainder_isBigO.bound
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hC,eventually_ge_atTop 1,tendsto_atTop.1 shortSide_tendsto 2] with N hbound hN hr
  have he : Real.log (treeCount (canonicalDomain N) : ℝ)-mainTerm N=canonicalRemainder N := by
    rw [canonical_log_decomposition (by omega) hr]
    unfold mainTerm stripLength
    ring
  rw [he]
  exact hbound

end
end SpanningTreeIsoperimetry.CanonicalCountAsymptotic
