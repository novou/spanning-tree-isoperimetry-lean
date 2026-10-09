import SpanningTreeIsoperimetry.PowerSeriesCircle
import SpanningTreeIsoperimetry.WeightedExponentialRemainder

/-! Identification of the formal positive-frequency exponential with the
actual complex exponential on the circle. Absolute double-sum control
justifies the substitution step. The deformation parameter remains real. -/
namespace SpanningTreeIsoperimetry.PowerSeriesCircle
open PowerSeries WeightedPowerSeries PositiveFrequencyExponential WeightedExponentialRemainder
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance : Fact (0<(2*Real.pi : ℝ)) := ⟨by positivity⟩

theorem value_subst {p q : PowerSeries ℝ} (hp0 : p.constantCoeff=0)
    (hp : SummableWeighted p)
    (hq : Summable (fun m => |PowerSeries.coeff m q| * (mass p)^m))
    (x : CircleDomain) :
    value (q.subst p) x=∑' m,((PowerSeries.coeff m q : ℝ) : ℂ)*(value p x)^m := by
  let F : ℕ×ℕ → ℝ := fun a => |PowerSeries.coeff a.1 q| * term (p^a.1) a.2
  have hF0 (a : ℕ×ℕ) : 0≤F a := mul_nonneg (abs_nonneg _) (term_nonneg _ _)
  have hFn (m : ℕ) : Summable (fun n => F (m,n)) := (pow_control hp m).1.mul_left |PowerSeries.coeff m q|
  have hFe (m : ℕ) : (∑' n,F (m,n))=|PowerSeries.coeff m q| * mass (p^m) := by
    dsimp only [F,mass]
    convert! (pow_control hp m).1.tsum_mul_left |PowerSeries.coeff m q| using 1
  have hFm : Summable (fun m => ∑' n,F (m,n)) := by
    simp_rw [hFe]
    exact Summable.of_nonneg_of_le (fun m => mul_nonneg (abs_nonneg _) (mass_nonneg _))
      (fun m => mul_le_mul_of_nonneg_left (pow_control hp m).2 (abs_nonneg _)) hq
  have hF : Summable F := (summable_prod_of_nonneg hF0).mpr ⟨hFn,hFm⟩
  let G : ℕ×ℕ → ℂ := fun a => ((PowerSeries.coeff a.1 q : ℝ) : ℂ)*mode (p^a.1) a.2 x
  have hG : Summable G := by
    apply Summable.of_norm_bounded hF
    intro a
    dsimp only [G,F]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_mode]
    exact mul_le_mul_of_nonneg_left (abs_coefficient_le_term _ _) (abs_nonneg _)
  have hn (n : ℕ) : mode (q.subst p) n x=∑' m,G (m,n) := by
    rw [tsum_eq_sum (s := Finset.range (n+1))]
    · rw [mode,coefficient_substitution hp0]
      push_cast
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m _
      dsimp only [G,mode]
      ring
    · intro m hm
      have hnm : n<m := by
        simp only [Finset.mem_range] at hm
        omega
      dsimp only [G,mode]
      rw [power_coefficient_zero hp0 hnm]
      simp
  calc
    value (q.subst p) x=(∑' n : ℕ,∑' m : ℕ,G (m,n)) := tsum_congr hn
    _=(∑' m : ℕ,∑' n : ℕ,G (m,n)) := hG.tsum_comm
    _=(∑' m : ℕ,((PowerSeries.coeff m q : ℝ) : ℂ)*(value p x)^m) := by
      apply tsum_congr
      intro m
      dsimp only [G]
      rw [tsum_mul_left]
      change ((PowerSeries.coeff m q : ℝ) : ℂ)*value (p^m) x=_
      rw [value_pow hp]

theorem value_exponential {V : PowerSeries ℝ} (hV0 : V.constantCoeff=0)
    (hV : SummableWeighted V) (t : ℝ) (x : CircleDomain) :
    value (exponential V t) x=Complex.exp ((t : ℂ)*value V x) := by
  have hsum (y : ℝ) : HasSum (fun m : ℕ => y^m/(m.factorial : ℝ)) (Real.exp y) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp y
  have hq : Summable (fun m => |PowerSeries.coeff m (outer t)| * (mass V)^m) := by
    simpa only [outer_majorant] using (hsum (|t| * mass V)).summable
  change value ((outer t).subst V) x=_
  rw [value_subst hV0 hV hq]
  have he : (∑' m : ℕ,((t : ℂ)*value V x)^m/(m.factorial : ℂ))=
      Complex.exp ((t : ℂ)*value V x) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact (NormedSpace.expSeries_div_hasSum_exp ((t : ℂ)*value V x)).tsum_eq
  rw [← he]
  apply tsum_congr
  intro m
  rw [outer_coefficient]
  push_cast
  rw [mul_pow]
  ring

end
end SpanningTreeIsoperimetry.PowerSeriesCircle
