import SpanningTreeIsoperimetry.RegularizedStripSymbol
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.Tannery

/-! Dominated passage to the critical quadratic Fourier sum. The uniform
coefficient estimate is an explicit input of this analytic bridge; this file
alone does not claim that estimate or the strip determinant identity. -/
namespace SpanningTreeIsoperimetry.RegularizedFourierQuadratic
open RegularizedStripSymbol Filter
open scoped Topology
noncomputable section

def majorant (n : ℕ) : ℝ := 4/(Real.pi^2*((n+1 : ℕ) : ℝ)^3)

theorem majorant_summable : Summable majorant := by
  have hs := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by decide : 1<3))
  convert hs.mul_left (4/Real.pi^2) using 1
  funext n
  unfold majorant
  ring

theorem weighted_square_le {x : ℝ} (n : ℕ)
    (hx : |x|≤2/(Real.pi*((n+1 : ℕ) : ℝ)^2)) :
    ((n+1 : ℕ) : ℝ)*x^2≤majorant n := by
  have hn : (0 : ℝ)<(n+1 : ℕ) := by positivity
  calc
    ((n+1 : ℕ) : ℝ)*x^2≤
        ((n+1 : ℕ) : ℝ)*(2/(Real.pi*((n+1 : ℕ) : ℝ)^2))^2 := by
      apply mul_le_mul_of_nonneg_left _ hn.le
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hx 2
    _=majorant n := by
      unfold majorant
      field_simp
      <;> ring

def quadratic (z : ℝ) : ℝ :=
  ∑' n : ℕ,((n+1 : ℕ) : ℝ)*coefficientZ z (n+1)^2

theorem critical_limit_of_uniform_bound
    (hbound : ∀ z : ℝ,4≤z → ∀ j : ℕ,0<j →
      |coefficientZ z j|≤2/(Real.pi*(j : ℝ)^2)) :
    Tendsto quadratic (nhdsWithin 4 (Set.Ici 4))
      (𝓝 (∑' n : ℕ,((n+1 : ℕ) : ℝ)*StripFourierCoefficients.coefficient (n+1)^2)) := by
  apply tendsto_tsum_of_dominated_convergence majorant_summable
  · intro n
    exact ((coefficient_critical_limit (n+1)).pow 2).const_mul _
  · filter_upwards [self_mem_nhdsWithin] with z hz
    intro n
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact weighted_square_le n (hbound z hz (n+1) (by omega))

end
end SpanningTreeIsoperimetry.RegularizedFourierQuadratic
