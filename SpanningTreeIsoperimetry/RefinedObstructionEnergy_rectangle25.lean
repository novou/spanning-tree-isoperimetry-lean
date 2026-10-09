import SpanningTreeIsoperimetry.RefinedObstruction_rectangle25
import SpanningTreeIsoperimetry.RefinedPiBounds
import SpanningTreeIsoperimetry.RefinedEntropyBounds

/-! Actual rectangle25 energy threshold for the refined corner envelope. -/
namespace SpanningTreeIsoperimetry.RefinedObstructionEnergy
open CornerEnergy CornerNumericBounds RefinedPiBounds RefinedEntropyBounds
open RefinedObstructionPolynomials
open scoped BigOperators
noncomputable section
namespace rectangle25
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

def centered (u : ℝ) : ℝ := (727828212604975623773202177476632964159859315632801784378605222627172507071308043674555197881183148763213/91031953318160944172724173589391099723714534386331820314808283001184463500976562500000000000000000000000000000) + (-1598628710483162786078001945210139018639179861629315639781512181315335202508155902142959363/25286653699489151159090048219275305478809592885092172309668967500329017639160156250000000)*u^1 + (8969703916852850902055725140204510643485395833663168603544761043729892380222464/1242889602637290757771594050073819814894449109488050453364849090576171875)*u^2 + (-434422022045135166889964799732973318754104388845389331518615124443136/39097926239249993808633210079506170586682856082916259765625)*u^3 + (18240464410993874477519012552296606363699061475283828736/3504029667029726624605245888233184814453125)*u^4 + (-5348386316394765005873599003515665702031720448/7164770753663957118988037109375)*u^5 + (385365782469381738054997774434304/20489472703074375)*u^6

theorem determinant_centered (t : ℝ) : rectangle25.determinant t=centered (t-center) := by
  unfold rectangle25.determinant centered center
  ring

theorem determinant_upper : rectangle25.determinant (1/Real.pi)<((39976523961/5000000000000000) : ℝ) := by
  obtain ⟨hl1,hu1⟩ := abs_le.mp (power_bounds 1)
  obtain ⟨hl2,hu2⟩ := abs_le.mp (power_bounds 2)
  obtain ⟨hl3,hu3⟩ := abs_le.mp (power_bounds 3)
  obtain ⟨hl4,hu4⟩ := abs_le.mp (power_bounds 4)
  obtain ⟨hl5,hu5⟩ := abs_le.mp (power_bounds 5)
  obtain ⟨hl6,hu6⟩ := abs_le.mp (power_bounds 6)
  norm_num [radius] at hl1 hu1 hl2 hu2 hl3 hu3 hl4 hu4 hl5 hu5 hl6 hu6
  rw [determinant_centered]
  unfold centered
  simp only [one_div]
  nlinarith only [hl1,hu1,hl2,hu2,hl3,hu3,hl4,hu4,hl5,hu5,hl6,hu6]

theorem logarithm_lower : ((11736649/1000000) : ℝ)<Real.log ((5000000000000000/39976523961) : ℝ) := by
  have hs := Real.hasSum_log_one_add (a := ((152587890625/79953047922) : ℝ)-1) (by norm_num)
  have hb := sum_le_hasSum (Finset.range 10) (fun n _ => by positivity) hs
  norm_num [Finset.sum_range_succ] at hb
  have he : Real.log ((5000000000000000/39976523961) : ℝ)=16*Real.log 2+Real.log ((152587890625/79953047922) : ℝ) := by
    rw [show ((152587890625/79953047922) : ℝ)=((5000000000000000/39976523961) : ℝ)/2^16 by norm_num,
      Real.log_div (x := ((5000000000000000/39976523961) : ℝ)) (y := (2 : ℝ)^16) (by norm_num) (by norm_num),Real.log_pow]
    ring
  rw [he]
  nlinarith [log_two_lower]

theorem energy_lower : ((7421/100000) : ℝ)<realEnergy rectangle25.diagram := by
  rw [rectangle25.energy_exact]
  have hlog := Real.log_lt_log rectangle25.determinant_pos determinant_upper
  have hl := logarithm_lower
  rw [show ((5000000000000000/39976523961) : ℝ)=((39976523961/5000000000000000) : ℝ)⁻¹ by norm_num,Real.log_inv] at hl
  nlinarith [entropy_upper]

end rectangle25
end
end SpanningTreeIsoperimetry.RefinedObstructionEnergy
