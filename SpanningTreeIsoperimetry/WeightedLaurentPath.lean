import SpanningTreeIsoperimetry.LaurentWeightedConvolution
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Elementary path estimates in the concrete weighted Laurent mass.
No normed-space instance is introduced. -/
namespace SpanningTreeIsoperimetry.WeightedLaurentPath
open ToeplitzHankelKernels LaurentWeightedConvolution Filter Asymptotics
open scoped Topology
noncomputable section

def remainder (a : ℝ → Laurent) (a1 : Laurent) (t : ℝ) : Laurent := a t-a 0-t • a1

theorem remainder_weighted {a : ℝ → Laurent} {a1 : Laurent}
    (ha : ∀ t,WeightedSummable (a t)) (ha1 : WeightedSummable a1) (t : ℝ) :
    WeightedSummable (remainder a a1 t) :=
  weighted_sub (weighted_sub (ha t) (ha 0)) (weighted_smul ha1 t)

theorem difference_mass_le {a : ℝ → Laurent} {a1 : Laurent}
    (ha : ∀ t,WeightedSummable (a t)) (ha1 : WeightedSummable a1) (t : ℝ) :
    weightedMass (a t-a 0)≤weightedMass (remainder a a1 t)+|t| *weightedMass a1 := by
  have he : a t-a 0=remainder a a1 t+t • a1 := by unfold remainder; abel
  rw [he]
  have h := weightedMass_add_le (remainder_weighted ha ha1 t) (weighted_smul ha1 t)
  rwa [weightedMass_smul] at h

theorem difference_mass_tendsto_zero {a : ℝ → Laurent} {a1 : Laurent}
    (ha : ∀ t,WeightedSummable (a t)) (ha1 : WeightedSummable a1)
    (hr : (fun t => weightedMass (remainder a a1 t)) =o[𝓝 0] fun t => t) :
    Tendsto (fun t => weightedMass (a t-a 0)) (𝓝 0) (𝓝 0) := by
  have hrem := hr.trans_tendsto (tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0))
  have ht : Tendsto (fun t : ℝ => |t|) (𝓝 0) (𝓝 0) := by
    simpa only [abs_zero] using continuous_abs.tendsto (0 : ℝ)
  have hmajor : Tendsto (fun t => weightedMass (remainder a a1 t)+|t| *weightedMass a1)
      (𝓝 0) (𝓝 0) := by
    simpa only [zero_mul,zero_add] using hrem.add (ht.mul_const (weightedMass a1))
  apply squeeze_zero' _ _ hmajor
  · exact Eventually.of_forall (fun t => weightedMass_nonneg _)
  · exact Eventually.of_forall (difference_mass_le ha ha1)

theorem weightedMass_eventually_bounded {a : ℝ → Laurent} {a1 : Laurent}
    (ha : ∀ t,WeightedSummable (a t)) (ha1 : WeightedSummable a1)
    (hr : (fun t => weightedMass (remainder a a1 t)) =o[𝓝 0] fun t => t) :
    ∀ᶠ t in 𝓝 (0 : ℝ),weightedMass (a t)≤1+weightedMass (a 0)+weightedMass a1 := by
  have hrem := hr.trans_tendsto (tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0))
  have ht : Tendsto (fun t : ℝ => |t|) (𝓝 0) (𝓝 0) := by
    simpa only [abs_zero] using continuous_abs.tendsto (0 : ℝ)
  filter_upwards [hrem.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))] with t hr ht
  have hdiff := difference_mass_le ha ha1 t
  have hmass := weightedMass_add_le (weighted_sub (ha t) (ha 0)) (ha 0)
  rw [sub_add_cancel] at hmass
  have hscale := mul_le_of_le_one_left (weightedMass_nonneg a1) ht.le
  linarith

end
end SpanningTreeIsoperimetry.WeightedLaurentPath
