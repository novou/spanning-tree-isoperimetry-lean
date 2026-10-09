import SpanningTreeIsoperimetry.EnergyConvergence
import Mathlib.Analysis.Real.Pi.Wallis

/-!
# Boundary return coefficients

The scalar Wallis telescoping identities used by half-plane Green entries.
The connection to finite-volume inverse entries is proved separately.
-/

namespace SpanningTreeIsoperimetry.BoundaryGreen

open scoped BigOperators Topology
open Filter CornerEnergy

noncomputable section

def wallisReciprocal (m : ℕ) : ℝ := (Real.Wallis.W m)⁻¹

@[simp] theorem wallisReciprocal_zero : wallisReciprocal 0 = 1 := by
  simp [wallisReciprocal, Real.Wallis.W]

theorem wallisReciprocal_pos (m : ℕ) : 0 < wallisReciprocal m :=
  inv_pos.mpr (Real.Wallis.W_pos m)

theorem wallisReciprocal_succ (m : ℕ) :
    wallisReciprocal (m + 1) =
      wallisReciprocal m * ((2 * m + 1) * (2 * m + 3) / (4 * (m + 1 : ℝ) ^ 2)) := by
  unfold wallisReciprocal
  rw [Real.Wallis.W_succ]
  have hw := (Real.Wallis.W_pos m).ne'
  have h1 : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (2 * (m : ℝ) + 2) ≠ 0 := by positivity
  have h3 : (2 * (m : ℝ) + 3) ≠ 0 := by positivity
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  <;> ring

theorem wallisReciprocal_tendsto :
    Tendsto wallisReciprocal atTop (𝓝 (2 / Real.pi)) := by
  change Tendsto (fun m => (Real.Wallis.W m)⁻¹) atTop (𝓝 (2 / Real.pi))
  simpa only [inv_div] using
    Real.Wallis.tendsto_W_nhds_pi_div_two.inv₀ (by positivity)

/-- Central-binomial form of the reciprocal Wallis product. -/
theorem wallisReciprocal_eq_central (m : ℕ) :
    wallisReciprocal m = (2 * m + 1 : ℝ) * normalizedCentralBinom m ^ 2 := by
  induction m with
  | zero => norm_num [normalizedCentralBinom]
  | succ m ih =>
    rw [wallisReciprocal_succ, normalizedCentralBinom_succ, ih]
    push_cast
    field_simp
    <;> ring

/-- The reflected return coefficient at length `2m`, including the Green
normalization `1/4`. -/
def boundaryReturnCoefficient (m : ℕ) : ℝ :=
  (normalizedCentralBinom m ^ 2 * (2 * m + 1)) / (4 * (m + 1 : ℝ) ^ 2)

theorem boundaryReturnCoefficient_nonneg (m : ℕ) : 0 ≤ boundaryReturnCoefficient m := by
  unfold boundaryReturnCoefficient
  positivity

theorem boundaryReturnCoefficient_telescope (m : ℕ) :
    boundaryReturnCoefficient m = wallisReciprocal m - wallisReciprocal (m + 1) := by
  rw [wallisReciprocal_succ]
  rw [wallisReciprocal_eq_central]
  unfold boundaryReturnCoefficient
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  <;> ring

theorem sum_boundaryReturnCoefficient (N : ℕ) :
    ∑ m ∈ Finset.range N, boundaryReturnCoefficient m = 1 - wallisReciprocal N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, boundaryReturnCoefficient_telescope]
    ring

/-- Exact diagonal half-plane coefficient sum, with the complete Wallis proof
imported from mathlib. -/
theorem boundaryReturnCoefficient_hasSum :
    HasSum boundaryReturnCoefficient (1 - 2 / Real.pi) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg boundaryReturnCoefficient_nonneg]
  simpa only [sum_boundaryReturnCoefficient] using wallisReciprocal_tendsto.const_sub 1

/-- A general nonnegative Wallis telescoping principle. It evaluates an actual
coefficient sequence once its rational telescoper and endpoint limit are proved. -/
theorem hasSum_of_wallis_telescope (f c : ℕ → ℝ) (L : ℝ)
    (hf : ∀ m, 0 ≤ f m)
    (ht : ∀ m, f m = wallisReciprocal (m + 1) * c (m + 1) - wallisReciprocal m * c m)
    (hc : Tendsto c atTop (𝓝 L)) :
    HasSum f (2 / Real.pi * L - c 0) := by
  have hs (N : ℕ) : ∑ m ∈ Finset.range N, f m = wallisReciprocal N * c N - c 0 := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, ht]
      ring
  rw [hasSum_iff_tendsto_nat_of_nonneg hf]
  simpa only [hs] using (wallisReciprocal_tendsto.mul hc).sub_const (c 0)

def boundaryNeighborCoefficient (m : ℕ) : ℝ :=
  wallisReciprocal m * (2 * m + 1) /
    (8 * (m + 1 : ℝ) ^ 2 * (m + 2))

private def neighborTelescoper (m : ℕ) : ℝ := 1 - 1 / (2 * (m + 1))

theorem boundaryNeighborCoefficient_hasSum :
    HasSum boundaryNeighborCoefficient (-1 / 2 + 2 / Real.pi) := by
  have hc : Tendsto neighborTelescoper atTop (𝓝 (1 : ℝ)) := by
    change Tendsto (fun m : ℕ => 1 - 1 / (2 * ((m : ℝ) + 1))) atTop (𝓝 1)
    have ht : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
      Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds
    have hm : Tendsto (fun m : ℕ => 2 * ((m : ℝ) + 1)) atTop atTop :=
      ht.const_mul_atTop (by norm_num)
    simpa only [neighborTelescoper, sub_zero] using
      (tendsto_const_nhds.div_atTop hm : Tendsto (fun m : ℕ => (1 : ℝ) / (2 * (m + 1)))
        atTop (𝓝 0)).const_sub 1
  have hf (m : ℕ) : 0 ≤ boundaryNeighborCoefficient m := by
    unfold boundaryNeighborCoefficient
    exact div_nonneg (mul_nonneg (wallisReciprocal_pos m).le (by positivity)) (by positivity)
  have h := hasSum_of_wallis_telescope boundaryNeighborCoefficient neighborTelescoper 1 hf
    (by
      intro m
      rw [wallisReciprocal_succ]
      unfold boundaryNeighborCoefficient neighborTelescoper
      push_cast
      have hm : (m : ℝ) + 1 ≠ 0 := by positivity
      have hm2 : (m : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      <;> ring) hc
  convert h using 1
  norm_num [neighborTelescoper]
  ring

end
end SpanningTreeIsoperimetry.BoundaryGreen
