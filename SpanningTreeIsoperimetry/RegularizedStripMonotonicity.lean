import SpanningTreeIsoperimetry.StripSpectralRegularization
import SpanningTreeIsoperimetry.StripStrictness

/-! The actual regularized strip energies increase to their supremum.
This is a wordwise statement, independent of a determinant asymptotic. -/
namespace SpanningTreeIsoperimetry.RegularizedStripMonotonicity
open StripSpectralRegularization Ferrers CornerEnergy Filter
open scoped Topology
noncomputable section

theorem strip_monotone {z : ℝ} (hz : 4≤z) :
    Monotone (fun k => spectralEnergy (horizontalStrip k) z) := by
  intro j k hjk
  apply (term_summable (horizontalStrip j) hz).tsum_le_tsum _
    (term_summable (horizontalStrip k) hz)
  intro n
  unfold term
  exact mul_le_mul_of_nonneg_left (realEnergyTerm_strip_mono hjk n) (pow_nonneg (by positivity) _)

theorem strip_tendsto {z : ℝ} (hz : 4≤z) :
    Tendsto (fun k => spectralEnergy (horizontalStrip k) z) atTop (𝓝 (stripSupremum z)) :=
  tendsto_atTop_ciSup (strip_monotone hz) (strip_range_bdd hz)

theorem stripSupremum_eq_of_limit {z L : ℝ} (hz : 4≤z)
    (hL : Tendsto (fun k => spectralEnergy (horizontalStrip k) z) atTop (𝓝 L)) :
    stripSupremum z=L := tendsto_nhds_unique (strip_tendsto hz) hL

end
end SpanningTreeIsoperimetry.RegularizedStripMonotonicity
