module

public import SpanningTreeIsoperimetry.SmallFamilyDerivativeChecks
public import SpanningTreeIsoperimetry.SmallFamilyCostData

@[expose] public section

/-! Exact aspect-cost simplification and monotone rational remainder
majorants used to reduce small noncanonical families to finite endpoints. -/
namespace SpanningTreeIsoperimetry.SmallFamilyCosts
open SmallFamilyMonotonicity Set AspectCost
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false



theorem remainderBound_antitone {q a b g x y : ℝ} (hq : 0≤q) (hg : 0≤g)
    (hxa : a<x) (hxb : b<x) (hxy : x≤y) : remainderBound q a b g y≤remainderBound q a b g x := by
  have hxa0 : 0<x-a := by linarith
  have hxb0 : 0<x-b := by linarith
  have hya0 : 0<y-a := by linarith
  have hyb0 : 0<y-b := by linarith
  have ha2 := pow_le_pow_left₀ hxa0.le (show x-a≤y-a by linarith) 2
  have hb2 := pow_le_pow_left₀ hxb0.le (show x-b≤y-b by linarith) 2
  have ha4 := pow_le_pow_left₀ hxa0.le (show x-a≤y-a by linarith) 4
  have hb4 := pow_le_pow_left₀ hxb0.le (show x-b≤y-b by linarith) 4
  have hden : 2*(x-a)^2*(x-b)^2≤2*(y-a)^2*(y-b)^2 := by gcongr
  have h1 := div_le_div_of_nonneg_left hg (show 0<2*(x-a)^2*(x-b)^2 by positivity) hden
  have h2 := one_div_le_one_div_of_le (show 0<4*(x-b)^4 by positivity)
    (mul_le_mul_of_nonneg_left hb4 (by norm_num : (0 : ℝ)≤4))
  have h3 := div_le_div_of_nonneg_left hq (pow_pos hxa0 4) ha4
  exact add_le_add (add_le_add h1 h2) h3

variable {ι : Type*}

theorem upperCost_antitone (C q sourceShift : ℝ) (I : Finset ι) (c shift : ι → ℝ)
    {a h r₀ : ℝ} (hq : 0≤q) (hsource : sourceShift≤h)
    (ha : 0≤a) (hh : 0<h) (hr : 3*h≤r₀)
    (hc : ∀ i∈I, 0≤c i) (hs : ∀ i∈I, 0≤shift i) (hpole : ∀ i∈I, shift i<r₀)
    (hend : normalizedWeight I c shift r₀≤normalizedSlope a h r₀) :
    AntitoneOn (upperCost C q sourceShift a h I c shift) (Ici r₀) := by
  intro x hx y hy hxy
  have hx' : r₀≤x := hx
  have hA := corrected_aspect_antitone I c shift ha hh hr hc hs hpole hend hx hy hxy
  have hP := remainderBound_antitone hq (show 0≤h*(a+h) by positivity)
    (show h<x by linarith) (show sourceShift<x by linarith) hxy
  unfold upperCost
  linarith only [hA,hP]

end
end SpanningTreeIsoperimetry.SmallFamilyCosts
