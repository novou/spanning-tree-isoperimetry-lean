import SpanningTreeIsoperimetry.BoundaryGreenCoefficients
import SpanningTreeIsoperimetry.BoundaryWalkCount

/-! Exact sums of actual half-plane boundary path coefficients. -/
namespace SpanningTreeIsoperimetry.BoundaryGreen

open scoped BigOperators Topology
open CornerEnergy Filter

theorem shifted_choose_ratio (m j : ℕ) :
    ((2*m+j).choose m : ℝ)=
      (Nat.centralBinom m : ℝ)*(∏ l ∈ Finset.range j, (2*(m : ℝ)+l+1)) /
        (∏ l ∈ Finset.range j, ((m : ℝ)+l+1)) := by
  have hd (u : ℕ) : (∏ l ∈ Finset.range u, ((m : ℝ)+l+1))≠0 :=
    (Finset.prod_pos (fun l _ => by positivity)).ne'
  induction j with
  | zero => simp [Nat.centralBinom]
  | succ j ih =>
    have h := Nat.choose_mul_succ_eq (2*m+j) m
    rw [show 2*m+j+1-m=m+j+1 by omega] at h
    have hR : ((2*m+(j+1)).choose m : ℝ)*((m : ℝ)+j+1)=
        ((2*m+j).choose m : ℝ)*(2*m+j+1) := by
      exact_mod_cast h.symm
    have he : ((2*m+(j+1)).choose m : ℝ)=
        ((2*m+j).choose m : ℝ)*(2*m+j+1)/((m : ℝ)+j+1) :=
      (eq_div_iff (by positivity : (m : ℝ)+j+1≠0)).mpr hR
    rw [he,ih,Finset.prod_range_succ,Finset.prod_range_succ]
    field_simp [hd j]
    <;> ring

theorem halfPlaneCoefficient_shift_eq (j : Fin 6) (m : ℕ) :
    halfPlaneCoefficient (2*m+j.val) j.val=boundaryCoefficientSix j m := by
  unfold halfPlaneCoefficient
  rw [halfPlane_count_real,shifted_choose_ratio]
  unfold boundaryCoefficientSix
  rw [wallisReciprocal_eq_central]
  unfold normalizedCentralBinom
  simp only [Finset.prod_pow]
  have hd : (∏ l ∈ Finset.range j.val, ((m : ℝ)+l+1))≠0 :=
    (Finset.prod_pos (fun l _ => by positivity)).ne'
  have hp : (4 : ℝ)^(2*m+j.val+1)=(4^m)^2*4^(j.val+1) := by
    rw [show 2*m+j.val+1=m*2+(j.val+1) by omega,pow_add,pow_mul]
  rw [hp]
  field_simp [hd]
  <;> ring

noncomputable def boundaryValue (j : Fin 6) : ℝ := 2/Real.pi*limitSix j-initialSix j

theorem boundaryValue_explicit (j : Fin 6) :
    boundaryValue j=
      ![1-2/Real.pi,-1/2+2/Real.pi,-1+(10/3)/Real.pi,
        -4+(38/3)/Real.pi,-17+(802/15)/Real.pi,-76+(1194/5)/Real.pi] j := by
  fin_cases j <;> norm_num [boundaryValue,limitSix,initialSix] <;> ring

/-- Exact coefficient sum, including vanishing short lengths and wrong parity. -/
theorem halfPlaneCoefficient_hasSum (j : Fin 6) :
    HasSum (fun n => halfPlaneCoefficient n j.val) (boundaryValue j) := by
  have heven : HasSum (fun m => halfPlaneCoefficient (2*m+j.val) j.val) (boundaryValue j) := by
    exact (boundaryCoefficientSix_hasSum j).congr_fun
      (fun m => halfPlaneCoefficient_shift_eq j m)
  have hodd : HasSum (fun m => halfPlaneCoefficient (2*m+1+j.val) j.val) (0 : ℝ) := by
    simp [halfPlaneCoefficient,halfPlane_count_wrongParity]
  have hshift : HasSum (fun n => halfPlaneCoefficient (n+j.val) j.val) (boundaryValue j) := by
    simpa only [add_zero] using heven.even_add_odd (f := fun n => halfPlaneCoefficient (n+j.val) j.val) hodd
  have hprefix : ∑ n ∈ Finset.range j.val, halfPlaneCoefficient n j.val=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [halfPlaneCoefficient,halfPlane_count_short (Finset.mem_range.mp hn),Nat.cast_zero,zero_div]
  simpa only [hprefix,zero_add] using hshift.sum_range_add
    (f := fun n => halfPlaneCoefficient n j.val) (k := j.val)

end SpanningTreeIsoperimetry.BoundaryGreen
