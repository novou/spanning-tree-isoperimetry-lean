module

public import SpanningTreeIsoperimetry.BoundaryLossIntegral

@[expose] public section

/-! Exact Bose moments used in the finite singleton and short-defect lower
corrections. All sums are derived from the positive geometric expansion. -/
namespace SpanningTreeIsoperimetry.BoundaryBoseMoments
open MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section

def laplaceMoment (m : ℕ) (a x : ℝ) : ℝ := x^m*Real.exp (-(a*x))
def bose (m : ℕ) (r x : ℝ) : ℝ := x^m/(Real.exp (2*r*x)-1)

theorem laplaceMoment_integrable (m : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (laplaceMoment m a) (Ioi 0) := by
  change IntegrableOn (fun x : ℝ => x^m*Real.exp (-(a*x))) (Ioi 0)
  have hs : (-1 : ℝ) < (m : ℝ) := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  simpa only [laplaceMoment,Real.rpow_natCast,Real.rpow_one,neg_mul] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (m : ℝ))
      hs (by norm_num) ha)

theorem integral_laplaceMoment (m : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Ioi 0, laplaceMoment m a x)=(m.factorial : ℝ)/a^(m+1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (m : ℝ)+1) (r := a) (by positivity) ha
  have hg : Real.Gamma ((m : ℝ)+1)=(m.factorial : ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using Real.Gamma_nat_eq_factorial m
  rw [hg] at h
  rw [show (m : ℝ)+1=((m+1 : ℕ) : ℝ) by push_cast; rfl] at h
  simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right,Real.rpow_natCast] at h
  have he : (1/a)^((m : ℝ)+1)=(1/a)^(m+1) := by
    rw [show (m : ℝ)+1=((m+1 : ℕ) : ℝ) by push_cast; rfl,Real.rpow_natCast]
  rw [he] at h
  simpa only [one_div_pow,laplaceMoment,div_mul_eq_mul_div,one_mul] using h

theorem geometric_hasSum (m : ℕ) {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    HasSum (fun n : ℕ => laplaceMoment m (2*r*(n+1)) x) (bose m r x) := by
  let q := Real.exp (-(2*r*x))
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hs := ((hasSum_geometric_of_abs_lt_one (by rw [abs_of_pos hq0]; exact hq1)).mul_left q).mul_left (x^m)
  have heq : q*(1-q)⁻¹=1/(Real.exp (2*r*x)-1) := by
    dsimp only [q]
    rw [Real.exp_neg]
    have he : Real.exp (2*r*x)≠0 := (Real.exp_pos _).ne'
    have he1 : Real.exp (2*r*x)-1≠0 := by
      have hh : 1 < Real.exp (2*r*x) := Real.one_lt_exp_iff.mpr (by positivity)
      linarith
    field_simp
    <;> ring
  have hlim : x^m*(q*(1-q)⁻¹)=bose m r x := by rw [heq]; unfold bose; ring
  rw [hlim] at hs
  apply hs.congr_fun
  intro n
  unfold laplaceMoment
  congr 1
  dsimp only [q]
  rw [← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  ring

/-- A reusable integral identity; the concrete moments below discharge the
power-series premise with checked zeta values. -/
theorem integral_bose_of_hasSum (m : ℕ) {r z : ℝ} (hr : 0 < r)
    (hz : HasSum (fun n : ℕ => 1/(n+1 : ℝ)^(m+1)) z) :
    (∫ x : ℝ in Ioi 0, bose m r x)=(m.factorial : ℝ)/(2*r)^(m+1)*z := by
  have hp (n : ℕ) : 0 < 2*r*((n : ℝ)+1) := by positivity
  have hi (n : ℕ) : (∫ x : ℝ in Ioi 0, laplaceMoment m (2*r*(n+1)) x)=
      (m.factorial : ℝ)/(2*r)^(m+1)*(1/(n+1 : ℝ)^(m+1)) := by
    rw [integral_laplaceMoment m (hp n),mul_pow]
    simp only [div_eq_mul_inv,mul_inv_rev,one_mul]
    ring
  have hn (n : ℕ) : (∫ x : ℝ in Ioi 0, ‖laplaceMoment m (2*r*(n+1)) x‖)=
      (m.factorial : ℝ)/(2*r)^(m+1)*(1/(n+1 : ℝ)^(m+1)) := by
    rw [← hi]
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    apply Real.norm_of_nonneg
    unfold laplaceMoment
    exact mul_nonneg (pow_nonneg hx.le _) (Real.exp_pos _).le
  have hsum := hasSum_integral_of_summable_integral_norm
    (fun n => laplaceMoment_integrable m (hp n))
    (show Summable (fun n : ℕ => ∫ x : ℝ in Ioi 0, ‖laplaceMoment m (2*r*(n+1)) x‖) by
      simp_rw [hn]; exact hz.summable.mul_left _)
  have hpoint : (fun x : ℝ => ∑' n : ℕ, laplaceMoment m (2*r*(n+1)) x)=ᵐ[volume.restrict (Ioi 0)] bose m r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact (geometric_hasSum m hr hx).tsum_eq
  calc
    _=∫ x : ℝ in Ioi 0, ∑' n : ℕ, laplaceMoment m (2*r*(n+1)) x := (integral_congr_ae hpoint).symm
    _=∑' n : ℕ, ∫ x : ℝ in Ioi 0, laplaceMoment m (2*r*(n+1)) x := hsum.tsum_eq.symm
    _=_ := by simp_rw [hi]; exact (hz.mul_left _).tsum_eq

private theorem zeta_six : HasSum (fun n : ℕ => (1 : ℝ)/(n : ℝ)^6) (Real.pi^6/945) := by
  have h := hasSum_zeta_nat (k := 3) (by decide)
  have hb : bernoulli 6=(1/42 : ℚ) := by decide +kernel
  norm_num [hb,Nat.factorial] at h
  convert h using 1 <;> ring

private theorem zeta_eight : HasSum (fun n : ℕ => (1 : ℝ)/(n : ℝ)^8) (Real.pi^8/9450) := by
  have h := hasSum_zeta_nat (k := 4) (by decide)
  have hb : bernoulli 8=(-1/30 : ℚ) := by decide +kernel
  norm_num [hb,Nat.factorial] at h
  convert h using 1 <;> ring

theorem integral_bose_three {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ in Ioi 0, bose 3 r x)=Real.pi^4/(240*r^4) := by
  have hz : HasSum (fun n : ℕ => 1/(n+1 : ℝ)^4) (Real.pi^4/90) := by
    simpa using (hasSum_nat_add_iff' 1).2 hasSum_zeta_four
  rw [integral_bose_of_hasSum 3 hr hz]
  norm_num [Nat.factorial]
  ring

theorem integral_bose_five {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ in Ioi 0, bose 5 r x)=Real.pi^6/(504*r^6) := by
  have hz : HasSum (fun n : ℕ => 1/(n+1 : ℝ)^6) (Real.pi^6/945) := by
    simpa using (hasSum_nat_add_iff' 1).2 zeta_six
  rw [integral_bose_of_hasSum 5 hr hz]
  norm_num [Nat.factorial]
  ring

theorem integral_bose_seven {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ in Ioi 0, bose 7 r x)=Real.pi^8/(480*r^8) := by
  have hz : HasSum (fun n : ℕ => 1/(n+1 : ℝ)^8) (Real.pi^8/9450) := by
    simpa using (hasSum_nat_add_iff' 1).2 zeta_eight
  rw [integral_bose_of_hasSum 7 hr hz]
  norm_num [Nat.factorial]
  ring

theorem bose_three_integrable {r : ℝ} (hr : 0 < r) : IntegrableOn (bose 3 r) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_bose_three hr]
  positivity

theorem bose_five_integrable {r : ℝ} (hr : 0 < r) : IntegrableOn (bose 5 r) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_bose_five hr]
  positivity

theorem bose_seven_integrable {r : ℝ} (hr : 0 < r) : IntegrableOn (bose 7 r) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_bose_seven hr]
  positivity

end
end SpanningTreeIsoperimetry.BoundaryBoseMoments
