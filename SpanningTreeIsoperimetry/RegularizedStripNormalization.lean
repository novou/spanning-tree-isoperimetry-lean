module

public import SpanningTreeIsoperimetry.RegularizedCornerLimit
public import SpanningTreeIsoperimetry.RegularizedBoundaryKernel

@[expose] public section

/-! Actual strip-minor normalization and its leading determinant limit.
The final uniqueness lemma is an intermediate bridge: it explicitly requires
an independently proved first-order determinant limit. It does not assert the
remaining symbol asymptotic or assume it as a paper theorem. -/
namespace SpanningTreeIsoperimetry.RegularizedStripNormalization
open Ferrers CornerEnergy RegularizedCornerDeterminant RegularizedCornerLimit
open StripSpectralRegularization RegularizedBoundaryKernel UniformStripEnergy Filter
open scoped Topology Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def stripEquiv (k : ℕ) : Fin k ≃ {p // p∈horizontalStrip k} where
  toFun i := ⟨(i.val,0),mem_horizontalStrip.mpr ⟨i.isLt,rfl⟩⟩
  invFun p := ⟨p.val.1,(mem_horizontalStrip.mp p.property).1⟩
  left_inv i := by apply Fin.ext; rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (mem_horizontalStrip.mp p.property).2.symm

theorem strip_energy_logdet {z : ℝ} (hz : 4≤z) (k : ℕ) :
    spectralEnergy (horizontalStrip k) z= -Real.log (boundaryMatrix z k).det-bulkEntropy z*k := by
  have h := spectralEnergy_eq_log_det hz (horizontalStrip_isFerrers k) (stripEquiv k)
  change spectralEnergy (horizontalStrip k) z=
    -Real.log (boundaryMatrix z k).det-bulkEntropy z*(horizontalStrip k).card at h
  rw [card_horizontalStrip] at h
  exact h

theorem strip_det_pos {z : ℝ} (hz : 4≤z) (k : ℕ) : 0<(boundaryMatrix z k).det :=
  quadrantMinorZ_det_pos hz (horizontalStrip_isFerrers k) (stripEquiv k)

theorem spectralEnergy_div_length_tendsto_zero {z : ℝ} (hz : 4≤z) :
    Tendsto (fun k : ℕ => spectralEnergy (horizontalStrip k) z/(k : ℝ)) atTop (𝓝 0) := by
  have hb : Tendsto (fun k : ℕ => stripEnergyLimit/(k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero' _ _ hb
  · exact Eventually.of_forall (fun k => div_nonneg (spectralEnergy_nonneg _ hz) (Nat.cast_nonneg k))
  · exact Eventually.of_forall (fun k => div_le_div_of_nonneg_right
      ((spectralEnergy_le _ hz).trans (realEnergy_strip_le_limit k)) (Nat.cast_nonneg k))

/-- The actual bounded loop energy fixes the leading logarithmic determinant
coefficient, with no symbol asymptotic used. -/
theorem logdet_div_length_tendsto {z : ℝ} (hz : 4≤z) :
    Tendsto (fun k : ℕ => Real.log (boundaryMatrix z k).det/(k : ℝ)) atTop
      (𝓝 (-bulkEntropy z)) := by
  have h := (spectralEnergy_div_length_tendsto_zero hz).neg.sub_const (bulkEntropy z)
  simp only [neg_zero,zero_sub] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk0 : (k : ℝ)≠0 := by exact_mod_cast (by omega : k≠0)
  have he := strip_energy_logdet hz k
  have hlog : Real.log (boundaryMatrix z k).det=
      -spectralEnergy (horizontalStrip k) z-bulkEntropy z*k := by linarith
  rw [hlog]
  field_simp
  <;> ring

/-- Intermediate uniqueness bridge. The independently established determinant
limit must be supplied explicitly; it is not an assumed scalar normalization. -/
theorem bulkEntropy_eq_neg_of_logdet_limit {z v : ℝ} (hz : 4≤z)
    (hv : Tendsto (fun k : ℕ => Real.log (boundaryMatrix z k).det/(k : ℝ)) atTop (𝓝 v)) :
    bulkEntropy z= -v := by
  have h := tendsto_nhds_unique (logdet_div_length_tendsto hz) hv
  linarith

/-- Intermediate symbol specialization. This becomes the final bulk-to-symbol
normalization only after the actual matrix limit premise is discharged. -/
theorem bulkEntropy_eq_neg_coefficient_of_limit {z : ℝ} (hz : 4<z)
    (hv : Tendsto (fun k : ℕ => Real.log (toeplitzHankelMatrix z k).det/(k : ℝ)) atTop
      (𝓝 (RegularizedStripSymbol.coefficientZ z 0))) :
    bulkEntropy z= -RegularizedStripSymbol.coefficientZ z 0 := by
  apply bulkEntropy_eq_neg_of_logdet_limit hz.le
  simpa only [boundaryMatrix_eq_toeplitzHankel hz] using hv

end
end SpanningTreeIsoperimetry.RegularizedStripNormalization
