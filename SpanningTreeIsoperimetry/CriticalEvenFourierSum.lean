module

public import SpanningTreeIsoperimetry.EvenFourierReconstruction
public import SpanningTreeIsoperimetry.RegularizedFourierQuadraticLimit

@[expose] public section

/-! Actual even-mode normalization for the critical strip symbol. The
periodic function is -gammaZ, including its correct values outside[0,pi]. -/
namespace SpanningTreeIsoperimetry.CriticalEvenFourierSum
open EvenPeriodicFourier RegularizedStripSymbol StripFourierCoefficients
open RegularizedFourierQuadraticLimit Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem regularized_even_sum {z : ℝ} (hz : 4≤z) :
    (∑' n : ℕ,coefficientZ z (2*(n+1)))=
      (-gammaZ z 0-gammaZ z Real.pi-2*coefficientZ z 0)/4 := by
  let f : ℝ → ℝ := fun θ => -gammaZ z θ
  have hc : Continuous f := by
    have h := continuous_clipped_gamma.comp (show Continuous (fun θ : ℝ => (z,θ)) by fun_prop)
    have hb : Continuous (fun θ : ℝ => gammaZ z θ) := by
      simpa only [Function.comp_def,max_eq_right hz] using h
    exact hb.neg
  have hp : Function.Periodic f (2*Real.pi) := by
    intro θ
    dsimp only [f]
    rw [gammaZ_periodic z θ]
  have he : Function.Even f := by
    intro θ
    dsimp only [f]
    rw [gammaZ_even z θ]
  have hpos : Summable (fun n : ℕ => coefficientZ z (n+1)) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using coefficient_abs_summable hz
  have hs : Summable (cosineCoeff f) := by
    change Summable (coefficientZ z)
    exact (summable_nat_add_iff 1).mp hpos
  have h := EvenFourierReconstruction.even_sum f hc hp he hs
  change (∑' n : ℕ,coefficientZ z (2*(n+1)))=
    ((-gammaZ z 0)+(-gammaZ z Real.pi)-2*coefficientZ z 0)/4 at h
  simpa only [sub_eq_add_neg] using h

theorem critical_even_sum_alpha :
    (∑' n : ℕ,coefficient (2*(n+1)))=
      (SquareMaximality.squareLatticeEntropy-SquareMaximality.Rectangle.Concrete.alpha)/2 := by
  have h := regularized_even_sum (z := 4) (by norm_num)
  simp_rw [coefficientZ_four] at h
  rw [gammaZ_four (show (0 : ℝ)∈Set.Icc 0 Real.pi from ⟨le_rfl,Real.pi_pos.le⟩),
    gammaZ_four (show Real.pi∈Set.Icc 0 Real.pi from ⟨Real.pi_pos.le,le_rfl⟩),
    RectangularRemainder.gamma_zero,RectangularRemainder.gamma_pi,coefficient_zero] at h
  convert h using 1 <;> ring

theorem critical_even_sum :
    (∑' n : ℕ,coefficient (2*(n+1)))=
      (SquareMaximality.squareLatticeEntropy-Real.log (1+Real.sqrt 2))/2 := by
  rw [critical_even_sum_alpha]
  have ha : SquareMaximality.Rectangle.Concrete.alpha=Real.log (1+Real.sqrt 2) := by
    norm_num [SquareMaximality.Rectangle.Concrete.alpha,Real.arsinh]
  rw [ha]

theorem critical_even_limit : Tendsto evenSum (nhdsWithin 4 (Set.Ici 4))
    (𝓝 ((SquareMaximality.squareLatticeEntropy-Real.log (1+Real.sqrt 2))/2)) := by
  have h := even_critical_limit
  rwa [critical_even_sum] at h

end
end SpanningTreeIsoperimetry.CriticalEvenFourierSum
