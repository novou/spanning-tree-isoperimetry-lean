module

public import SpanningTreeIsoperimetry.StripSpectralRegularization
public import SpanningTreeIsoperimetry.CriticalEvenFourierSum

@[expose] public section

/-! The actual regularized strip supremum tends to the critical strip energy.
This conclusion uses only fixed-strip continuity and the uniform word-energy
bound. The separate Fourier profile has its own checked limit; their equality
is not asserted here. -/
namespace SpanningTreeIsoperimetry.RegularizedStripCriticalLimit
open Ferrers CornerEnergy StripSpectralRegularization UniformStripEnergy Filter
open scoped Topology
noncomputable section

/-- Critical convergence of the actual supremum, for every approach from the
valid spectral region. No determinant or Fourier identity is a premise. -/
theorem stripSupremum_tendsto {ι : Type*} {l : Filter ι} {z : ι → ℝ}
    (hz : Tendsto z l (𝓝 4)) (hlower : ∀ᶠ i in l,4≤z i) :
    Tendsto (fun i => stripSupremum (z i)) l (𝓝 stripEnergyLimit) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨k,hk⟩ := (realEnergy_strip_tendsto.eventually (lt_mem_nhds ha)).exists
    have ht := spectralEnergy_tendsto (horizontalStrip k) hz hlower
    filter_upwards [hlower,ht.eventually (lt_mem_nhds hk)] with i hi hki
    exact hki.trans_le (le_ciSup (strip_range_bdd hi) k)
  · intro b hb
    filter_upwards [hlower] with i hi
    exact (stripSupremum_le hi).trans_lt hb

/-- In particular, the massive strip supremum has the required right limit
at the critical value 4. -/
theorem stripSupremum_right_limit :
    Tendsto stripSupremum (nhdsWithin 4 (Set.Ioi 4)) (𝓝 stripEnergyLimit) := by
  apply stripSupremum_tendsto (tendsto_id.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact hz.le

/-- The Fourier expression appearing in the independent determinant limit. -/
def fourierProfile (z : ℝ) : ℝ := RegularizedFourierQuadraticLimit.evenSum z-
  (1/2)*RegularizedFourierQuadratic.quadratic z

def criticalFourierProfile : ℝ :=
  (SquareMaximality.squareLatticeEntropy-Real.log (1+Real.sqrt 2))/2-
    (1/2)*∑' n : ℕ,((n+1 : ℕ) : ℝ)*StripFourierCoefficients.coefficient (n+1)^2

/-- Convergence of the actual even and quadratic Fourier sums. This does not
identify their difference with an energy. -/
theorem fourierProfile_limit :
    Tendsto fourierProfile (nhdsWithin 4 (Set.Ici 4)) (𝓝 criticalFourierProfile) := by
  exact CriticalEvenFourierSum.critical_even_limit.sub
    (RegularizedFourierQuadraticLimit.critical_limit.const_mul (1/2))

theorem fourierProfile_right_limit :
    Tendsto fourierProfile (nhdsWithin 4 (Set.Ioi 4)) (𝓝 criticalFourierProfile) :=
  fourierProfile_limit.mono_left (nhdsWithin_mono (4 : ℝ) (show Set.Ioi (4 : ℝ)⊆Set.Ici 4 by
    intro x hx
    change (4 : ℝ)<x at hx
    change (4 : ℝ)≤x
    exact hx.le))

end
end SpanningTreeIsoperimetry.RegularizedStripCriticalLimit
