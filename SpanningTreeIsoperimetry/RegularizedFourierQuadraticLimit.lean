import SpanningTreeIsoperimetry.RegularizedFourierDecay
import SpanningTreeIsoperimetry.RegularizedFourierQuadratic

/-! Actual summability and critical limit, discharging the uniform bound
in the generic dominated-convergence bridge. -/
namespace SpanningTreeIsoperimetry.RegularizedFourierQuadraticLimit
open RegularizedStripSymbol RegularizedFourierDecay RegularizedFourierQuadratic Filter
open scoped Topology
noncomputable section

theorem coefficient_abs_summable {z : ℝ} (hz : 4≤z) :
    Summable (fun n : ℕ => |coefficientZ z (n+1)|) := by
  have hs := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by decide : 1<2))
  have hmajor : Summable (fun n : ℕ => 2/(Real.pi*((n+1 : ℕ) : ℝ)^2)) := by
    convert hs.mul_left (2/Real.pi) using 1
    funext n
    ring
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun n => coefficient_bound hz (by omega : 0<n+1)) hmajor

theorem quadratic_summable {z : ℝ} (hz : 4≤z) :
    Summable (fun n : ℕ => ((n+1 : ℕ) : ℝ)*coefficientZ z (n+1)^2) :=
  Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun n => weighted_square_le n (coefficient_bound hz (by omega : 0<n+1))) majorant_summable

theorem critical_limit : Tendsto quadratic (nhdsWithin 4 (Set.Ici 4))
    (𝓝 (∑' n : ℕ,((n+1 : ℕ) : ℝ)*StripFourierCoefficients.coefficient (n+1)^2)) :=
  critical_limit_of_uniform_bound (fun _ hz _ hj => coefficient_bound hz hj)

def evenMajorant (n : ℕ) : ℝ := 2/(Real.pi*((2*(n+1) : ℕ) : ℝ)^2)

theorem even_majorant_summable : Summable evenMajorant := by
  have hs := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by decide : 1<2))
  convert hs.mul_left (1/(2*Real.pi)) using 1
  funext n
  unfold evenMajorant
  simp only [Nat.cast_mul,Nat.cast_ofNat,mul_pow,div_eq_mul_inv,mul_inv_rev]
  ring

def evenSum (z : ℝ) : ℝ := ∑' n : ℕ,coefficientZ z (2*(n+1))

theorem even_abs_summable {z : ℝ} (hz : 4≤z) :
    Summable (fun n : ℕ => |coefficientZ z (2*(n+1))|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun n => coefficient_bound hz (by omega : 0<2*(n+1))) even_majorant_summable

theorem even_critical_limit : Tendsto evenSum (nhdsWithin 4 (Set.Ici 4))
    (𝓝 (∑' n : ℕ,StripFourierCoefficients.coefficient (2*(n+1)))) := by
  apply tendsto_tsum_of_dominated_convergence even_majorant_summable
  · intro n
    exact coefficient_critical_limit (2*(n+1))
  · filter_upwards [self_mem_nhdsWithin] with z hz
    intro n
    rw [Real.norm_eq_abs]
    exact coefficient_bound hz (by omega : 0<2*(n+1))

end
end SpanningTreeIsoperimetry.RegularizedFourierQuadraticLimit
