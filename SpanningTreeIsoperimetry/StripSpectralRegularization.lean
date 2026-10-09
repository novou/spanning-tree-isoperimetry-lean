import SpanningTreeIsoperimetry.UniformStripEnergy
import Mathlib.Analysis.Normed.Group.Tannery

/-! Spectral regularization of the actual nonnegative loop-energy series.
The critical strip supremum is the supremum of the regularized suprema.
This limit exchange does not assume a Toeplitz determinant asymptotic. -/
namespace SpanningTreeIsoperimetry.StripSpectralRegularization
open Ferrers CornerEnergy UniformStripEnergy Filter
open scoped Topology
noncomputable section

def term (M : Diagram) (z : ℝ) (n : ℕ) : ℝ := (4/z)^(n+1)*realEnergyTerm M n

def spectralEnergy (M : Diagram) (z : ℝ) : ℝ := ∑' n,term M z n

theorem term_eq_defectSum (M : Diagram) {z : ℝ} (hz : 4≤z) (n : ℕ) :
    term M z n=(defectSum M (n+1) : ℝ)/(((n : ℝ)+1)*z^(n+1)) := by
  have hz0 : z≠0 := by linarith
  have hn : (n : ℝ)+1≠0 := by positivity
  unfold term realEnergyTerm
  rw [div_pow]
  field_simp
  <;> ring

theorem term_nonneg (M : Diagram) {z : ℝ} (hz : 4≤z) (n : ℕ) : 0≤term M z n := by
  unfold term
  exact mul_nonneg (pow_nonneg (by positivity) _) (realEnergyTerm_nonneg M n)

theorem term_le (M : Diagram) {z : ℝ} (hz : 4≤z) (n : ℕ) : term M z n≤realEnergyTerm M n := by
  have hz0 : 0<z := by linarith
  have hq : 4/z≤1 := (div_le_one hz0).mpr hz
  have hp : (4/z)^(n+1)≤1 := pow_le_one₀ (by positivity) hq
  exact mul_le_of_le_one_left (realEnergyTerm_nonneg M n) hp

theorem term_summable (M : Diagram) {z : ℝ} (hz : 4≤z) : Summable (term M z) :=
  Summable.of_nonneg_of_le (term_nonneg M hz) (term_le M hz) (realEnergyTerm_summable M)

theorem spectralEnergy_nonneg (M : Diagram) {z : ℝ} (hz : 4≤z) : 0≤spectralEnergy M z :=
  tsum_nonneg (term_nonneg M hz)

theorem spectralEnergy_le (M : Diagram) {z : ℝ} (hz : 4≤z) : spectralEnergy M z≤realEnergy M := by
  rw [spectralEnergy,realEnergy_eq_tsum]
  exact (term_summable M hz).tsum_le_tsum (term_le M hz) (realEnergyTerm_summable M)

theorem spectralEnergy_four (M : Diagram) : spectralEnergy M 4=realEnergy M := by
  simp only [spectralEnergy,term,div_self (by norm_num : (4 : ℝ)≠0),one_pow,one_mul,realEnergy_eq_tsum]

theorem spectralEnergy_tendsto (M : Diagram) {ι : Type*} {l : Filter ι} {z : ι → ℝ}
    (hz : Tendsto z l (𝓝 4)) (hlower : ∀ᶠ i in l, 4≤z i) :
    Tendsto (fun i => spectralEnergy M (z i)) l (𝓝 (realEnergy M)) := by
  have h := tendsto_tsum_of_dominated_convergence (realEnergyTerm_summable M)
    (f := fun i n => term M (z i) n) (g := realEnergyTerm M)
    (fun n => by
      have hq : Tendsto (fun i => (4 : ℝ)/z i) l (𝓝 (4/4 : ℝ)) :=
        tendsto_const_nhds.div hz (by norm_num)
      have hh := (hq.pow (n+1)).mul_const (realEnergyTerm M n)
      simpa only [term,div_self (by norm_num : (4 : ℝ)≠0),one_pow,one_mul] using hh)
    (hlower.mono (fun i hi n => by
      rw [Real.norm_eq_abs,abs_of_nonneg (term_nonneg M hi n)]
      exact term_le M hi n))
  simpa only [spectralEnergy,← realEnergy_eq_tsum] using h

def stripSupremum (z : ℝ) : ℝ := ⨆ k : ℕ,spectralEnergy (horizontalStrip k) z

theorem strip_range_bdd {z : ℝ} (hz : 4≤z) :
    BddAbove (Set.range (fun k => spectralEnergy (horizontalStrip k) z)) :=
  by
    refine ⟨stripEnergyLimit,?_⟩
    rintro x ⟨k,rfl⟩
    exact (spectralEnergy_le _ hz).trans (realEnergy_strip_le_limit k)

theorem stripSupremum_le {z : ℝ} (hz : 4≤z) : stripSupremum z≤stripEnergyLimit := by
  apply ciSup_le
  intro k
  exact (spectralEnergy_le _ hz).trans (realEnergy_strip_le_limit k)

def regularizedSupremum : ℝ := ⨆ z : {z : ℝ // 4<z},stripSupremum z.val

theorem regularized_range_bdd :
    BddAbove (Set.range (fun z : {z : ℝ // 4<z} => stripSupremum z.val)) :=
  by
    refine ⟨stripEnergyLimit,?_⟩
    rintro x ⟨z,rfl⟩
    exact stripSupremum_le z.property.le

/-- The critical strip constant is exactly the supremum over z>4 and strip
length. Every passage uses the actual nonnegative loop coefficients. -/
theorem regularizedSupremum_eq : regularizedSupremum=stripEnergyLimit := by
  letI : Nonempty {z : ℝ // 4<z} := ⟨⟨5,by norm_num⟩⟩
  apply le_antisymm
  · apply ciSup_le
    intro z
    exact stripSupremum_le z.property.le
  · apply ciSup_le
    intro k
    let z : ℕ → ℝ := fun n => 4+1/((n : ℝ)+1)
    have hz (n : ℕ) : 4<z n := by
      have hp : (0 : ℝ)<1/((n : ℝ)+1) := by positivity
      dsimp [z]
      linarith
    have ht : Tendsto z atTop (𝓝 4) := by
      simpa only [z,add_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 4)).add
          tendsto_one_div_add_atTop_nhds_zero_nat
    apply le_of_tendsto (spectralEnergy_tendsto (horizontalStrip k) ht (Filter.Eventually.of_forall (fun n => (hz n).le)))
    apply Filter.Eventually.of_forall
    intro n
    exact (le_ciSup (strip_range_bdd (hz n).le) k).trans
      (le_ciSup regularized_range_bdd (⟨z n,hz n⟩ : {z : ℝ // 4<z}))

end
end SpanningTreeIsoperimetry.StripSpectralRegularization
