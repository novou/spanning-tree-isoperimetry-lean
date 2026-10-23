module

public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

set_option backward.privateInPublic true

/-!
# The scalar closed-walk series

This file evaluates the last scalar series produced by the finite closed-walk
counting argument.  The proof is kept independent of the graph-theoretic
development: it establishes the central-binomial generating function, proves
summability at its boundary, and applies Abel's limit theorem.
-/

namespace SquareMaximality
namespace ClosedWalk

open Filter Finset
open scoped Topology

private lemma multichoose_succ_mul (r : ℝ) (n : ℕ) :
    (n + 1 : ℝ) * Ring.multichoose r (n + 1) =
      (r + n) * Ring.multichoose r n := by
  apply mul_left_cancel₀ (a := (n.factorial : ℝ)) (by positivity)
  calc
    (n.factorial : ℝ) * ((n + 1 : ℝ) * Ring.multichoose r (n + 1)) =
        ((n + 1).factorial : ℝ) * Ring.multichoose r (n + 1) := by
          rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          ring
    _ = (ascPochhammer ℕ (n + 1)).smeval r := by
          simpa [nsmul_eq_mul] using
            (Ring.factorial_nsmul_multichoose_eq_ascPochhammer r (n + 1))
    _ = (ascPochhammer ℕ n).smeval r * (r + n) := by
          rw [ascPochhammer_succ_right, Polynomial.smeval_mul,
            Polynomial.smeval_add, Polynomial.smeval_X,
            Polynomial.smeval_natCast]
          simp
    _ = (n.factorial : ℝ) * ((r + n) * Ring.multichoose r n) := by
          rw [← Ring.factorial_nsmul_multichoose_eq_ascPochhammer]
          simp only [nsmul_eq_mul]
          ring

private lemma four_pow_mul_multichoose_half (n : ℕ) :
    (4 : ℝ) ^ n * Ring.multichoose (1 / 2 : ℝ) n = Nat.centralBinom n := by
  induction n with
  | zero => simp [Nat.centralBinom_zero]
  | succ n ih =>
      apply mul_left_cancel₀ (a := (n + 1 : ℝ)) (by positivity)
      calc
        (n + 1 : ℝ) *
            ((4 : ℝ) ^ (n + 1) * Ring.multichoose (1 / 2 : ℝ) (n + 1)) =
            (4 : ℝ) ^ n * 4 *
              ((n + 1 : ℝ) * Ring.multichoose (1 / 2 : ℝ) (n + 1)) := by
                rw [pow_succ]
                ring
        _ = (4 : ℝ) ^ n * 4 *
              (((1 / 2 : ℝ) + n) * Ring.multichoose (1 / 2 : ℝ) n) := by
                rw [multichoose_succ_mul]
        _ = (2 * (2 * n + 1) : ℝ) *
              ((4 : ℝ) ^ n * Ring.multichoose (1 / 2 : ℝ) n) := by
                ring
        _ = (2 * (2 * n + 1) : ℝ) * Nat.centralBinom n := by rw [ih]
        _ = (n + 1 : ℝ) * Nat.centralBinom (n + 1) := by
              exact_mod_cast (Nat.succ_mul_centralBinom_succ n).symm

private lemma choose_neg_half_mul_neg_four_pow (n : ℕ) :
    Ring.choose (-1 / 2 : ℝ) n * (-4 : ℝ) ^ n = Nat.centralBinom n := by
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Ring.choose_neg']
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul,
    Int.cast_negOnePow_natCast]
  rw [show (-4 : ℝ) = (-1) * 4 by ring, mul_pow]
  have hs : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (-1 : ℝ) ^ n * Ring.multichoose (1 / 2 : ℝ) n *
        ((-1 : ℝ) ^ n * 4 ^ n) =
        ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
          (4 ^ n * Ring.multichoose (1 / 2 : ℝ) n) := by ring
    _ = 4 ^ n * Ring.multichoose (1 / 2 : ℝ) n := by rw [hs, one_mul]
    _ = Nat.centralBinom n := four_pow_mul_multichoose_half n

private lemma choose_neg_half_term (x : ℝ) (n : ℕ) :
    Ring.choose (-1 / 2 : ℝ) n * (-4 * x) ^ n =
      (Nat.centralBinom n : ℝ) * x ^ n := by
  rw [mul_pow, ← mul_assoc, choose_neg_half_mul_neg_four_pow]

private noncomputable def centralRatio (n : ℕ) : ℝ :=
  (Nat.centralBinom n : ℝ) / (4 : ℝ) ^ n

private lemma centralRatio_nonneg (n : ℕ) : 0 ≤ centralRatio n := by
  exact div_nonneg (by positivity) (by positivity)

private lemma centralRatio_succ (n : ℕ) :
    centralRatio (n + 1) = ((2 * n + 1 : ℝ) / (2 * (n + 1))) * centralRatio n := by
  have hrec : (n + 1 : ℝ) * Nat.centralBinom (n + 1) =
      (2 * (2 * n + 1) : ℝ) * Nat.centralBinom n := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  dsimp [centralRatio]
  rw [pow_succ]
  field_simp
  nlinarith

private lemma centralRatio_sq_le (n : ℕ) :
    centralRatio n ^ 2 ≤ 1 / (n + 1 : ℝ) := by
  induction n with
  | zero => norm_num [centralRatio, Nat.centralBinom_zero]
  | succ n ih =>
      rw [centralRatio_succ]
      have hn : (0 : ℝ) ≤ n := by positivity
      have hn1 : (0 : ℝ) < n + 1 := by positivity
      have hn2 : (0 : ℝ) < n + 2 := by positivity
      calc
        (((2 * n + 1 : ℝ) / (2 * (n + 1))) * centralRatio n) ^ 2 ≤
            ((2 * n + 1 : ℝ) / (2 * (n + 1))) ^ 2 *
              (1 / (n + 1 : ℝ)) := by
                rw [mul_pow]
                gcongr
        _ ≤ 1 / (n + 2 : ℝ) := by
              field_simp
              nlinarith [sq_nonneg (n : ℝ)]
        _ = 1 / ((n + 1 : ℕ) + 1 : ℝ) := by push_cast; ring

private lemma centralRatio_succ_le_inv_sqrt (n : ℕ) :
    centralRatio (n + 1) ≤ 1 / Real.sqrt (n + 1 : ℝ) := by
  have hN : (0 : ℝ) < n + 1 := by positivity
  apply le_of_sq_le_sq _ (by positivity)
  calc
    centralRatio (n + 1) ^ 2 ≤ 1 / ((n + 1 : ℕ) + 1 : ℝ) :=
      centralRatio_sq_le (n + 1)
    _ ≤ 1 / (n + 1 : ℝ) := by
      gcongr
      norm_num
    _ = (1 / Real.sqrt (n + 1 : ℝ)) ^ 2 := by
      rw [div_pow, one_pow, Real.sq_sqrt hN.le]

private noncomputable def boundaryCentralCoeff (n : ℕ) : ℝ :=
  centralRatio (n + 1) / (n + 1 : ℝ)

private lemma boundaryCentralCoeff_nonneg (n : ℕ) :
    0 ≤ boundaryCentralCoeff n := by
  exact div_nonneg (centralRatio_nonneg _) (by positivity)

private lemma boundaryCentralCoeff_norm_le (n : ℕ) :
    ‖boundaryCentralCoeff n‖ ≤ 1 / (n + 1 : ℝ) ^ (3 / 2 : ℝ) := by
  have hN : (0 : ℝ) < n + 1 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (boundaryCentralCoeff_nonneg n)]
  calc
    boundaryCentralCoeff n ≤ (1 / Real.sqrt (n + 1 : ℝ)) / (n + 1 : ℝ) := by
      dsimp [boundaryCentralCoeff]
      gcongr
      exact centralRatio_succ_le_inv_sqrt n
    _ = 1 / ((n + 1 : ℝ) * Real.sqrt (n + 1 : ℝ)) := by
      field_simp [Real.sqrt_ne_zero'.mpr hN]
    _ = 1 / (n + 1 : ℝ) ^ (3 / 2 : ℝ) := by
      congr 1
      calc
        (n + 1 : ℝ) * Real.sqrt (n + 1 : ℝ) =
            (n + 1 : ℝ) ^ (1 : ℝ) * (n + 1 : ℝ) ^ (1 / 2 : ℝ) := by
              rw [Real.rpow_one, Real.sqrt_eq_rpow]
        _ = (n + 1 : ℝ) ^ ((1 : ℝ) + 1 / 2) :=
              (Real.rpow_add hN 1 (1 / 2)).symm
        _ = (n + 1 : ℝ) ^ (3 / 2 : ℝ) := by norm_num

/-- Absolute convergence of the central-binomial logarithmic series at its
radius of convergence. -/
theorem summable_boundaryCentralCoeff : Summable boundaryCentralCoeff := by
  have hp : Summable (fun n : ℕ ↦ 1 / (n + 1 : ℝ) ^ (3 / 2 : ℝ)) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 (3 / 2)).2 (by norm_num)
    convert h using 1
    ext n
    rw [abs_of_pos (by positivity)]
  exact hp.of_norm_bounded boundaryCentralCoeff_norm_le

/-- The central-binomial generating function on its open disk of convergence. -/
theorem hasSum_centralBinom_mul_pow {x : ℝ} (hx : |4 * x| < 1) :
    HasSum (fun n : ℕ ↦ (Nat.centralBinom n : ℝ) * x ^ n)
      (1 / Real.sqrt (1 - 4 * x)) := by
  have hmem : (-4 * x : ℝ) ∈ Metric.eball 0 1 := by
    simp only [Metric.mem_eball, edist_dist, Real.dist_eq, sub_zero, ENNReal.ofReal_lt_one]
    simpa [abs_mul, mul_comm] using hx
  have h :=
    (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (-1 / 2 : ℝ))).hasSum_sub hmem
  have h' : HasSum (fun n : ℕ ↦ (Nat.centralBinom n : ℝ) * x ^ n)
      ((1 + -4 * x) ^ (-1 / 2 : ℝ)) := h.congr fun n ↦ by
    simp only [binomialSeries_apply, sub_zero, smul_eq_mul, List.ofFn_const,
      List.prod_replicate, choose_neg_half_term]
  have hbase : 0 < 1 - 4 * x := by
    rw [abs_lt] at hx
    linarith
  have hrpow : (1 + -4 * x) ^ (-1 / 2 : ℝ) = 1 / Real.sqrt (1 - 4 * x) := by
    rw [show 1 + -4 * x = 1 - 4 * x by ring,
      show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hbase.le,
      ← Real.sqrt_eq_rpow]
    rw [one_div]
  rwa [hrpow] at h'

private lemma hasSum_centralRatio_mul_pow {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n : ℕ ↦ centralRatio n * t ^ n)
      (1 / Real.sqrt (1 - t)) := by
  have harg : |4 * (t / 4)| < 1 := by
    have hfour : (4 : ℝ) * (t / 4) = t := by ring
    rwa [hfour]
  have h := hasSum_centralBinom_mul_pow harg
  have heq : (fun n : ℕ ↦ (Nat.centralBinom n : ℝ) * (t / 4) ^ n) =
      (fun n : ℕ ↦ centralRatio n * t ^ n) := by
    funext n
    dsimp [centralRatio]
    rw [div_pow]
    ring
  rw [heq] at h
  have h' : HasSum (fun n : ℕ ↦ centralRatio n * t ^ n)
      (1 / Real.sqrt (1 - 4 * (t / 4))) := h
  convert h' using 1
  congr 2
  ring

private lemma hasSum_centralRatio_succ_mul_pow {t : ℝ} (ht : |t| < 1)
    (ht0 : t ≠ 0) :
    HasSum (fun n : ℕ ↦ centralRatio (n + 1) * t ^ n)
      ((1 / Real.sqrt (1 - t) - 1) / t) := by
  let f : ℕ → ℝ := fun n ↦ centralRatio n * t ^ n
  have htail : HasSum (fun n : ℕ ↦ f (n + 1))
      (1 / Real.sqrt (1 - t) - 1) := by
    have h := (hasSum_nat_add_iff' 1).2 (hasSum_centralRatio_mul_pow ht)
    simpa [f, centralRatio, Nat.centralBinom_zero] using h
  have hscaled := htail.mul_left t⁻¹
  have heq : (fun n : ℕ ↦ t⁻¹ * f (n + 1)) =
      (fun n : ℕ ↦ centralRatio (n + 1) * t ^ n) := by
    funext n
    dsimp [f]
    rw [pow_succ]
    field_simp
  rw [heq] at hscaled
  have hscaled' : HasSum (fun n : ℕ ↦ centralRatio (n + 1) * t ^ n)
      (t⁻¹ * (1 / Real.sqrt (1 - t) - 1)) := hscaled
  convert hscaled' using 1
  rw [div_eq_mul_inv]
  ring

private lemma centralRatio_le_one (n : ℕ) : centralRatio n ≤ 1 := by
  dsimp [centralRatio]
  rw [div_le_one (by positivity)]
  exact_mod_cast Nat.centralBinom_le_four_pow n

/-- The logarithmic central-binomial generating series, normalized so that
its radius of convergence is one. -/
noncomputable def centralLogGenerating (t : ℝ) : ℝ :=
  ∑' n : ℕ, boundaryCentralCoeff n * t ^ (n + 1)

private lemma hasDerivAt_boundaryCentralTerm (n : ℕ) (t : ℝ) :
    HasDerivAt (fun z : ℝ ↦ boundaryCentralCoeff n * z ^ (n + 1))
      (centralRatio (n + 1) * t ^ n) t := by
  apply ((hasDerivAt_pow (n + 1) t).const_mul (boundaryCentralCoeff n)).congr_deriv
  dsimp [boundaryCentralCoeff]
  field_simp
  simp

private lemma boundaryCentralDeriv_norm_le {r t : ℝ} (_hr0 : 0 ≤ r)
    (ht : t ∈ Set.Ioo (-r) r) (n : ℕ) :
    ‖centralRatio (n + 1) * t ^ n‖ ≤ r ^ n := by
  have habs : |t| ≤ r := (abs_lt.2 ht).le
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (centralRatio_nonneg _), norm_pow,
    Real.norm_eq_abs]
  calc
    centralRatio (n + 1) * |t| ^ n ≤ 1 * r ^ n := by
      gcongr
      · exact centralRatio_le_one _
    _ = r ^ n := one_mul _

/-- Termwise differentiation of the logarithmic generating series throughout
the open unit interval. -/
theorem hasDerivAt_centralLogGenerating {t : ℝ} (ht : |t| < 1) :
    HasDerivAt centralLogGenerating
      (∑' n : ℕ, centralRatio (n + 1) * t ^ n) t := by
  let r : ℝ := (|t| + 1) / 2
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by dsimp [r]; linarith
  have htr : t ∈ Set.Ioo (-r) r := by
    rw [Set.mem_Ioo, ← abs_lt]
    dsimp [r]
    linarith
  have hu : Summable (fun n : ℕ ↦ r ^ n) := summable_geometric_of_lt_one hr0 hr1
  have hderiv := hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ ↦ r ^ n)
    (g := fun (n : ℕ) (z : ℝ) ↦ boundaryCentralCoeff n * z ^ (n + 1))
    (g' := fun (n : ℕ) (z : ℝ) ↦ centralRatio (n + 1) * z ^ n)
    (t := Set.Ioo (-r) r) (y₀ := 0) (y := t)
    hu isOpen_Ioo (convex_Ioo (-r) r).isPreconnected
    (fun n z _ ↦ hasDerivAt_boundaryCentralTerm n z)
    (fun n z hz ↦ boundaryCentralDeriv_norm_le hr0 hz n)
    (by simp [hrpos]) (by simp) htr
  change HasDerivAt (fun z : ℝ ↦ ∑' n : ℕ, boundaryCentralCoeff n * z ^ (n + 1))
    (∑' n : ℕ, centralRatio (n + 1) * t ^ n) t
  exact hderiv

/-- Closed form of `centralLogGenerating` on the open unit interval. -/
noncomputable def centralLogClosedForm (t : ℝ) : ℝ :=
  -2 * Real.log ((1 + Real.sqrt (1 - t)) / 2)

private lemma hasDerivAt_centralLogClosedForm {t : ℝ} (ht : |t| < 1) :
    HasDerivAt centralLogClosedForm
      (1 / (Real.sqrt (1 - t) * (1 + Real.sqrt (1 - t)))) t := by
  have hbase : 0 < 1 - t := by
    rw [abs_lt] at ht
    linarith
  have hsqrt : HasDerivAt (fun z : ℝ ↦ Real.sqrt (1 - z))
      (-1 / (2 * Real.sqrt (1 - t))) t := by
    simpa only [Pi.sub_apply, Function.const_apply, id_eq, zero_sub] using
      (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).sqrt hbase.ne')
  have harg : HasDerivAt (fun z : ℝ ↦ (1 + Real.sqrt (1 - z)) / 2)
      ((-1 / (2 * Real.sqrt (1 - t))) / 2) t := by
    simpa only [Pi.add_apply, Function.const_apply, zero_add] using
      ((hasDerivAt_const t 1).add hsqrt).div_const 2
  have harg_ne : (1 + Real.sqrt (1 - t)) / 2 ≠ 0 := by positivity
  have hlog := harg.log harg_ne
  change HasDerivAt (fun z : ℝ ↦ -2 * Real.log ((1 + Real.sqrt (1 - z)) / 2)) _ t
  apply (hlog.const_mul (-2)).congr_deriv
  field_simp [Real.sqrt_ne_zero'.mpr hbase]

private lemma tsum_centralRatio_succ_mul_pow {t : ℝ} (ht : |t| < 1) :
    (∑' n : ℕ, centralRatio (n + 1) * t ^ n) =
      1 / (Real.sqrt (1 - t) * (1 + Real.sqrt (1 - t))) := by
  have hbase : 0 ≤ 1 - t := by
    rw [abs_lt] at ht
    linarith
  by_cases ht0 : t = 0
  · subst t
    rw [tsum_eq_single 0]
    · norm_num [centralRatio, Nat.centralBinom]
    · intro n hn
      simp [hn]
  · rw [(hasSum_centralRatio_succ_mul_pow ht ht0).tsum_eq]
    have hsqrt_ne : Real.sqrt (1 - t) ≠ 0 := by
      apply Real.sqrt_ne_zero'.mpr
      rw [abs_lt] at ht
      linarith
    have hsquare : Real.sqrt (1 - t) ^ 2 = 1 - t := Real.sq_sqrt hbase
    field_simp
    nlinarith

/-- Exact open-disk evaluation of the logarithmic central-binomial series. -/
theorem centralLogGenerating_eq_closedForm {t : ℝ} (ht : |t| < 1) :
    centralLogGenerating t = centralLogClosedForm t := by
  have hdiffSeries : DifferentiableOn ℝ centralLogGenerating (Set.Ioo (-1) 1) :=
    fun z hz ↦ (hasDerivAt_centralLogGenerating (abs_lt.2 hz)).differentiableAt.differentiableWithinAt
  have hdiffClosed : DifferentiableOn ℝ centralLogClosedForm (Set.Ioo (-1) 1) :=
    fun z hz ↦ (hasDerivAt_centralLogClosedForm (abs_lt.2 hz)).differentiableAt.differentiableWithinAt
  have hderiv : Set.EqOn (deriv centralLogGenerating) (deriv centralLogClosedForm)
      (Set.Ioo (-1) 1) := by
    intro z hz
    rw [(hasDerivAt_centralLogGenerating (abs_lt.2 hz)).deriv,
      (hasDerivAt_centralLogClosedForm (abs_lt.2 hz)).deriv,
      tsum_centralRatio_succ_mul_pow (abs_lt.2 hz)]
  have heq := isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo (-1 : ℝ) 1).isPreconnected
    hdiffSeries hdiffClosed hderiv (show (0 : ℝ) ∈ Set.Ioo (-1) 1 by norm_num)
    (by norm_num [centralLogGenerating, centralLogClosedForm])
  exact heq (abs_lt.1 ht)

private lemma centralLogGenerating_eq_mul_tsum (t : ℝ) :
    centralLogGenerating t =
      t * ∑' n : ℕ, boundaryCentralCoeff n * t ^ n := by
  rw [centralLogGenerating, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [pow_succ]
  ring

/-- Abel's theorem evaluates the unsigned boundary series. -/
theorem tsum_boundaryCentralCoeff :
    (∑' n : ℕ, boundaryCentralCoeff n) = centralLogClosedForm 1 := by
  have habel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    summable_boundaryCentralCoeff.hasSum.tendsto_sum_nat
  have hid : Tendsto (fun t : ℝ ↦ t) (𝓝[<] 1) (𝓝 1) :=
    tendsto_id.mono_left inf_le_left
  have hgen : Tendsto centralLogGenerating (𝓝[<] 1)
      (𝓝 (∑' n : ℕ, boundaryCentralCoeff n)) := by
    have hmul := hid.mul habel
    have heq : (fun t : ℝ ↦ t * ∑' n : ℕ, boundaryCentralCoeff n * t ^ n) =ᶠ[𝓝[<] 1]
        centralLogGenerating := by
      filter_upwards with t
      exact (centralLogGenerating_eq_mul_tsum t).symm
    simpa only [one_mul] using hmul.congr' heq
  have hopen : centralLogGenerating =ᶠ[𝓝[<] 1] centralLogClosedForm := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact centralLogGenerating_eq_closedForm (abs_lt.2 ⟨by linarith [ht.1], ht.2⟩)
  have hclosed : Tendsto centralLogClosedForm (𝓝[<] 1)
      (𝓝 (centralLogClosedForm 1)) := by
    have hc : ContinuousAt centralLogClosedForm 1 := by
      unfold centralLogClosedForm
      fun_prop (disch := norm_num)
    exact hc.tendsto.mono_left inf_le_left
  exact tendsto_nhds_unique (hgen.congr' hopen) hclosed

private noncomputable def signedBoundaryCentralCoeff (n : ℕ) : ℝ :=
  boundaryCentralCoeff n * (-1 : ℝ) ^ (n + 1)

private lemma summable_signedBoundaryCentralCoeff : Summable signedBoundaryCentralCoeff := by
  apply summable_boundaryCentralCoeff.norm.of_norm_bounded
  intro n
  simp [signedBoundaryCentralCoeff]

private lemma centralLogGenerating_neg_eq_mul_signed_tsum (t : ℝ) :
    centralLogGenerating (-t) =
      t * ∑' n : ℕ, signedBoundaryCentralCoeff n * t ^ n := by
  rw [centralLogGenerating, ← tsum_mul_left]
  apply tsum_congr
  intro n
  dsimp [signedBoundaryCentralCoeff]
  rw [neg_pow, pow_succ]
  ring

/-- Abel's theorem also evaluates the alternating boundary series. -/
private theorem tsum_signedBoundaryCentralCoeff :
    (∑' n : ℕ, signedBoundaryCentralCoeff n) = centralLogClosedForm (-1) := by
  have habel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    summable_signedBoundaryCentralCoeff.hasSum.tendsto_sum_nat
  have hid : Tendsto (fun t : ℝ ↦ t) (𝓝[<] 1) (𝓝 1) :=
    tendsto_id.mono_left inf_le_left
  have hgen : Tendsto (fun t : ℝ ↦ centralLogGenerating (-t)) (𝓝[<] 1)
      (𝓝 (∑' n : ℕ, signedBoundaryCentralCoeff n)) := by
    have hmul := hid.mul habel
    have heq : (fun t : ℝ ↦ t * ∑' n : ℕ, signedBoundaryCentralCoeff n * t ^ n) =ᶠ[𝓝[<] 1]
        (fun t : ℝ ↦ centralLogGenerating (-t)) := by
      filter_upwards with t
      exact (centralLogGenerating_neg_eq_mul_signed_tsum t).symm
    simpa only [one_mul] using hmul.congr' heq
  have hopen : (fun t : ℝ ↦ centralLogGenerating (-t)) =ᶠ[𝓝[<] 1]
      (fun t : ℝ ↦ centralLogClosedForm (-t)) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
    apply centralLogGenerating_eq_closedForm
    rw [abs_neg]
    exact abs_lt.2 ⟨by linarith [ht.1], ht.2⟩
  have hclosed : Tendsto (fun t : ℝ ↦ centralLogClosedForm (-t)) (𝓝[<] 1)
      (𝓝 (centralLogClosedForm (-1))) := by
    have hc : ContinuousAt (fun t : ℝ ↦ centralLogClosedForm (-t)) 1 := by
      unfold centralLogClosedForm
      fun_prop (disch := positivity)
    exact hc.tendsto.mono_left inf_le_left
  exact tendsto_nhds_unique (hgen.congr' hopen) hclosed

private lemma signedBoundaryCentralCoeff_even (n : ℕ) :
    signedBoundaryCentralCoeff (2 * n) = -boundaryCentralCoeff (2 * n) := by
  simp [signedBoundaryCentralCoeff, pow_succ]

private lemma signedBoundaryCentralCoeff_odd (n : ℕ) :
    signedBoundaryCentralCoeff (2 * n + 1) = boundaryCentralCoeff (2 * n + 1) := by
  simp [signedBoundaryCentralCoeff, pow_succ]

/-- The odd-indexed half of the boundary series is the average of its
unsigned and alternating endpoint values. -/
theorem tsum_boundaryCentralCoeff_odd :
    (∑' n : ℕ, boundaryCentralCoeff (2 * n + 1)) =
      (centralLogClosedForm 1 + centralLogClosedForm (-1)) / 2 := by
  have he : Summable (fun n : ℕ ↦ boundaryCentralCoeff (2 * n)) :=
    summable_boundaryCentralCoeff.comp_injective (fun _ _ h ↦ by omega)
  have ho : Summable (fun n : ℕ ↦ boundaryCentralCoeff (2 * n + 1)) :=
    summable_boundaryCentralCoeff.comp_injective (fun _ _ h ↦ by omega)
  have hse : Summable (fun n : ℕ ↦ signedBoundaryCentralCoeff (2 * n)) :=
    summable_signedBoundaryCentralCoeff.comp_injective (fun _ _ h ↦ by omega)
  have hso : Summable (fun n : ℕ ↦ signedBoundaryCentralCoeff (2 * n + 1)) :=
    summable_signedBoundaryCentralCoeff.comp_injective (fun _ _ h ↦ by omega)
  have htotal := tsum_even_add_odd he ho
  rw [tsum_boundaryCentralCoeff] at htotal
  have hsigned := tsum_even_add_odd hse hso
  have hseval : (∑' n : ℕ, signedBoundaryCentralCoeff (2 * n)) =
      -∑' n : ℕ, boundaryCentralCoeff (2 * n) := by
    calc
      (∑' n : ℕ, signedBoundaryCentralCoeff (2 * n)) =
          ∑' n : ℕ, -boundaryCentralCoeff (2 * n) :=
            tsum_congr signedBoundaryCentralCoeff_even
      _ = -∑' n : ℕ, boundaryCentralCoeff (2 * n) := tsum_neg
  have hsoval : (∑' n : ℕ, signedBoundaryCentralCoeff (2 * n + 1)) =
      ∑' n : ℕ, boundaryCentralCoeff (2 * n + 1) :=
    tsum_congr signedBoundaryCentralCoeff_odd
  rw [hseval, hsoval, tsum_signedBoundaryCentralCoeff] at hsigned
  linarith

private lemma closedForm_endpoint_average :
    (centralLogClosedForm 1 + centralLogClosedForm (-1)) / 2 =
      Real.log (4 / (1 + Real.sqrt 2)) := by
  rw [centralLogClosedForm, centralLogClosedForm]
  norm_num only [Real.sqrt_zero, add_zero, neg_neg]
  rw [Real.log_div, Real.log_div, Real.log_div, Real.log_one]
  all_goals try norm_num
  all_goals try positivity
  have hlog4 : Real.log (4 : ℝ) = Real.log 2 + Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  rw [hlog4]
  ring

/-- The odd-indexed normalized boundary series in its final logarithmic form. -/
theorem tsum_boundaryCentralCoeff_odd_log :
    (∑' n : ℕ, boundaryCentralCoeff (2 * n + 1)) =
      Real.log (4 / (1 + Real.sqrt 2)) :=
  tsum_boundaryCentralCoeff_odd.trans closedForm_endpoint_average

/-- The `a`th positive even central-binomial term, with `a = 0`
representing the manuscript's index `1`. -/
noncomputable def evenCentralLogTerm (a : ℕ) : ℝ :=
  (Nat.choose (4 * (a + 1)) (2 * (a + 1)) : ℝ) /
    ((2 * (a + 1) : ℕ) * (4 : ℝ) ^ (2 * (a + 1)))

private lemma boundaryCentralCoeff_odd_eq_evenCentralLogTerm (a : ℕ) :
    boundaryCentralCoeff (2 * a + 1) = evenCentralLogTerm a := by
  have harg₁ : 2 * (2 * a + 2) = 4 * (a + 1) := by omega
  have harg₂ : 2 * a + 2 = 2 * (a + 1) := by omega
  dsimp [boundaryCentralCoeff, centralRatio, evenCentralLogTerm]
  rw [Nat.centralBinom_eq_two_mul_choose, harg₁, harg₂]
  push_cast
  field_simp
  ring

/-- Absolute convergence of the exact scalar series appearing at the end of
the closed-walk span calculation. -/
theorem summable_evenCentralLogTerm : Summable evenCentralLogTerm := by
  have h : Summable (fun a : ℕ ↦ boundaryCentralCoeff (2 * a + 1)) :=
    summable_boundaryCentralCoeff.comp_injective (fun _ _ h ↦ by omega)
  have heq : (fun a : ℕ ↦ boundaryCentralCoeff (2 * a + 1)) = evenCentralLogTerm := by
    funext a
    exact boundaryCentralCoeff_odd_eq_evenCentralLogTerm a
  rwa [heq] at h

/-- Final endpoint identity:
`sum_{a ≥ 1} choose(4a,2a) / (2a 4^(2a)) = log(4/(1+√2))`. -/
theorem tsum_evenCentralLogTerm :
    (∑' a : ℕ, evenCentralLogTerm a) = Real.log (4 / (1 + Real.sqrt 2)) := by
  rw [← tsum_boundaryCentralCoeff_odd_log]
  apply tsum_congr
  exact fun a ↦ (boundaryCentralCoeff_odd_eq_evenCentralLogTerm a).symm

/-- `HasSum` form of `tsum_evenCentralLogTerm`, packaging convergence and
the exact endpoint value in one statement. -/
theorem hasSum_evenCentralLogTerm :
    HasSum evenCentralLogTerm (Real.log (4 / (1 + Real.sqrt 2))) := by
  rw [← tsum_evenCentralLogTerm]
  exact summable_evenCentralLogTerm.hasSum

/-- Expanded, definition-free spelling of the endpoint identity. -/
theorem centralBinomialEvenSeries :
    (∑' a : ℕ,
      (Nat.choose (4 * (a + 1)) (2 * (a + 1)) : ℝ) /
        ((2 * (a + 1) : ℕ) * (4 : ℝ) ^ (2 * (a + 1)))) =
      Real.log (4 / (1 + Real.sqrt 2)) := by
  simpa [evenCentralLogTerm] using tsum_evenCentralLogTerm

end ClosedWalk
end SquareMaximality
