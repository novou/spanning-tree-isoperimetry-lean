import SpanningTreeIsoperimetry.StabilitySharpnessGeometry
import SpanningTreeIsoperimetry.RectangleProfileContinuity
import SpanningTreeIsoperimetry.UniformRectangleError

/-! Sharpness of the actual stability coefficient along exact-area
rectangles a² by (a+1)². -/
namespace SpanningTreeIsoperimetry.StabilitySharpness
open StabilitySharpnessGeometry RectangleProfileContinuity RectangularRemainder Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000

def logRatio (a : ℕ) : ℝ := Real.log
  ((treeCount (rectangle (squareSide a) (squareSide a)) : ℝ)/treeCount (witness a))

private theorem alpha_eq_log : SquareMaximality.Rectangle.Concrete.alpha=Real.log (1+Real.sqrt 2) := by
  rw [← SquareMaximality.Rectangle.Concrete.exp_alpha,Real.log_exp]

theorem logRatio_exact {a : ℕ} (ha : 0<a) :
    logRatio a=Real.log (1+Real.sqrt 2)+J 1-J ((longSide a : ℝ)/shortSide a)+
      error (squareSide a) (squareSide a)-error (shortSide a) (longSide a) := by
  let r := shortSide a
  let s := longSide a
  let n := squareSide a
  have hr : 0<r := by dsimp [r,shortSide]; positivity
  have hs : 0<s := by dsimp [s,longSide]; positivity
  have hn : 0<n := by dsimp [n,squareSide]; positivity
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  have harea : (r : ℝ)*s=(n : ℝ)^2 := by exact_mod_cast witness_area a
  have hsum : (r : ℝ)+s=2*n+1 := by exact_mod_cast witness_perimeter a
  have hbulk : SquareMaximality.squareLatticeEntropy*(r : ℝ)*s=
      SquareMaximality.squareLatticeEntropy*(n : ℝ)*n := by
    rw [mul_assoc,harea]
    ring
  have hlog : Real.log ((n : ℝ)*n)=Real.log ((r : ℝ)*s) := by
    congr 1
    nlinarith [harea]
  have hF1 := F_eq_J hn hn
  have hF2 := F_eq_J hr hs
  rw [div_self hn0] at hF1
  unfold F at hF1 hF2
  rw [hbulk,hsum,alpha_eq_log] at hF2
  rw [hlog,alpha_eq_log] at hF1
  have hpN : (0 : ℝ)<treeCount (rectangle n n) := by
    rw [rectangle_treeCount_eq_foundation]
    exact_mod_cast SquareMaximality.tauRect_pos hn hn
  have hpW : (0 : ℝ)<treeCount (witness a) := by
    exact_mod_cast (treeCount_pos_iff_connected _).mpr (witness_connected ha)
  unfold logRatio
  rw [Real.log_div hpN.ne' hpW.ne']
  change Real.log (treeCount (rectangle n n) : ℝ)-Real.log (treeCount (rectangle r s) : ℝ)=_
  linarith

theorem error_tendsto {r s : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hshape : ∀ᶠ a in atTop, 0<r a ∧ r a≤s a ∧ s a≤3*r a) :
    Tendsto (fun a => error (r a) (s a)) atTop (𝓝 0) := by
  have hrR : Tendsto (fun a => (r a : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hr
  have hi : Tendsto (fun a => (r a : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hrR
  have hb : Tendsto (fun a => (1/2 : ℝ)*((r a : ℝ)⁻¹)^2) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2≠0),mul_zero] using (hi.pow 2).const_mul (1/2 : ℝ)
  apply squeeze_zero_norm' _ hb
  filter_upwards [hshape] with a ha
  calc
    ‖error (r a) (s a)‖≤1/(2*(r a : ℝ)^2) := by
      simpa only [Real.norm_eq_abs] using UniformRectangleError.error_uniform ha.1 ha.2.1 ha.2.2
    _ = (1/2 : ℝ)*((r a : ℝ)⁻¹)^2 := by
      simp only [div_eq_mul_inv,one_mul,mul_inv_rev,inv_pow]
      ring

theorem shortSide_tendsto : Tendsto shortSide atTop atTop := by
  apply tendsto_atTop_mono (fun a => ?_) tendsto_id
  change a≤a^2
  simpa only [pow_two] using Nat.le_mul_self a

theorem squareSide_tendsto : Tendsto squareSide atTop atTop := by
  apply tendsto_atTop_mono (fun a => ?_) tendsto_id
  change a≤a*(a+1)
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left a (show 1≤a+1 by omega)

theorem witness_error_tendsto :
    Tendsto (fun a => error (shortSide a) (longSide a)) atTop (𝓝 0) := by
  apply error_tendsto shortSide_tendsto
  filter_upwards [eventually_ge_atTop 2] with a ha
  refine ⟨by unfold shortSide; positivity,(witness_order a).1.trans (witness_order a).2,
    witness_aspect_le_three ha⟩

theorem square_error_tendsto :
    Tendsto (fun a => error (squareSide a) (squareSide a)) atTop (𝓝 0) := by
  apply error_tendsto squareSide_tendsto
  filter_upwards [eventually_ge_atTop 1] with a ha
  refine ⟨by unfold squareSide; positivity,le_rfl,by omega⟩

theorem aspect_tendsto : Tendsto (fun a => (longSide a : ℝ)/shortSide a) atTop (𝓝 1) := by
  have hi : Tendsto (fun a : ℕ => (a : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hb : Tendsto (fun a : ℕ => (1+(a : ℝ)⁻¹)^2) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hi).pow 2
  apply hb.congr'
  filter_upwards [eventually_ge_atTop 1] with a ha
  unfold longSide shortSide
  push_cast
  have ha0 : (a : ℝ)≠0 := by exact_mod_cast (show a≠0 by omega)
  field_simp [ha0] <;> ring

theorem logRatio_tendsto : Tendsto logRatio atTop (𝓝 (Real.log (1+Real.sqrt 2))) := by
  have hJ := (continuousAt_J (by norm_num : (0 : ℝ)<1)).tendsto.comp aspect_tendsto
  have hb : Tendsto (fun a => Real.log (1+Real.sqrt 2)+J 1-J ((longSide a : ℝ)/shortSide a)+
      error (squareSide a) (squareSide a)-error (shortSide a) (longSide a))
      atTop (𝓝 (Real.log (1+Real.sqrt 2))) := by
    have hc : Tendsto (fun _ : ℕ => Real.log (1+Real.sqrt 2)+J 1) atTop
        (𝓝 (Real.log (1+Real.sqrt 2)+J 1)) := tendsto_const_nhds
    simpa using (((hc.sub hJ).add square_error_tendsto).sub witness_error_tendsto)
  apply hb.congr'
  filter_upwards [eventually_ge_atTop 1] with a ha
  exact (logRatio_exact (by omega)).symm

theorem weight_tendsto :
    Tendsto (fun a => (squareSide a : ℝ)*normalizedAsymmetry (squareSide a) (witness a)^2)
      atTop (𝓝 4) := by
  have htop : Tendsto (fun a : ℕ => (a : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun a => by change (a : ℝ)≤(a : ℝ)+1; linarith) tendsto_natCast_atTop_atTop
  have hi := tendsto_inv_atTop_zero.comp htop
  have hb : Tendsto (fun a : ℕ => (4 : ℝ)-4*((a : ℝ)+1)⁻¹) atTop (𝓝 4) := by
    simpa using (tendsto_const_nhds.sub (hi.const_mul 4))
  apply hb.congr
  intro a
  rw [witness_weight]
  have ha1 : (a : ℝ)+1≠0 := by positivity
  field_simp [ha1]
  ring

theorem sharpness_ratio_tendsto :
    Tendsto (fun a => logRatio a /
      ((squareSide a : ℝ)*normalizedAsymmetry (squareSide a) (witness a)^2))
      atTop (𝓝 (Real.log (1+Real.sqrt 2)/4)) :=
  logRatio_tendsto.div weight_tendsto (by norm_num)

/-- Any coefficient valid uniformly in the actual connected square-area
stability inequality is at most α/4. -/
theorem coefficient_optimal {C : ℝ}
    (hC : ∀ n : ℕ, 0<n → ∀ S : Domain, S.card=n^2 → (domainGraph S).Connected →
      C*n*normalizedAsymmetry n S^2≤Real.log ((treeCount (rectangle n n) : ℝ)/treeCount S)) :
    C≤Real.log (1+Real.sqrt 2)/4 := by
  have he : ∀ᶠ a in atTop,
      C*((squareSide a : ℝ)*normalizedAsymmetry (squareSide a) (witness a)^2)≤logRatio a := by
    filter_upwards [eventually_ge_atTop 1] with a ha
    have hn : 0<squareSide a := by unfold squareSide; positivity
    have hh := hC (squareSide a) hn (witness a) (witness_card a) (witness_connected (by omega))
    simpa only [logRatio,mul_assoc] using hh
  have hh := le_of_tendsto_of_tendsto (weight_tendsto.const_mul C) logRatio_tendsto he
  linarith

end
end SpanningTreeIsoperimetry.StabilitySharpness
