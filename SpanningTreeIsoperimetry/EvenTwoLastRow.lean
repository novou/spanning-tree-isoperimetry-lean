import SpanningTreeIsoperimetry.EvenTwoFamilyRows
import SpanningTreeIsoperimetry.LargeImbalanceGeometry

/-! The common final even selector-two multicorner row. -/
namespace SpanningTreeIsoperimetry.EvenTwoLastRow
open Ferrers CornerEnergy CornerPrimalDomains CrossHullCountComparison
  SmallFamilyProfiles SmallFamilyMonotonicity SmallFamilyCosts SmallFamilyCostBounds
  MulticornerEndpointChecks FixedStripEnergyUpper RectangularRemainder AspectCost
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem count_lt {m t : ℕ} (hm : 9≤m) (ht : t≤1) (M : Corner → Diagram)
    (hM : ∀ c,IsFerrers (M c)) (hk : totalDefect M=8-t^2)
    {c d : Corner} (hdc : d≠c) (hc : (M c).Nonempty) (hd : (M d).Nonempty) :
    treeCount (cornerPrimal (m-t-1) (m+t-1) M)<treeCount (cornerStrip (m-2) (m+2) 4) := by
  let r := m-t
  let s := m+t
  let R := m-2
  let S := m+2
  have hrNat : m-1≤r ∧ r≤m := by dsimp [r]; omega
  have hsNat : r≤s ∧ s≤S := by dsimp [r,s,S]; omega
  have hRNat : 7≤R ∧ R<r := by dsimp [R,r]; omega
  have hsum : r+s=R+S := by dsimp [r,s,R,S]; omega
  have hshape : S≤3*R := by dsimp [R,S]; omega
  have hkNat : 7≤totalDefect M ∧ totalDefect M<r := by
    dsimp [r]
    interval_cases t <;> norm_num at hk ⊢ <;> omega
  have harea : r*s+4=R*S+totalDefect M := by
    have he : m=(m-2)+2 := by omega
    rw [hk]
    dsimp [r,s,R,S]
    interval_cases t
    · change m*m+4=(m-2)*(m+2)+(8-0^2)
      rw [he]
      norm_num
      ring
    · change (m-1)*(m+1)+4=(m-2)*(m+2)+(8-1^2)
      have h1 : m-1=(m-2)+1 := by omega
      rw [h1,he]
      norm_num
      ring
  have hgap : r*s-R*S≤4 := by
    have hk8 : totalDefect M≤8 := by omega
    omega
  have hrfit : totalDefect M≤r-1 := by omega
  have hsfit : totalDefect M≤s-1 := by omega
  have hj : 4≤S-1 := by dsimp [S]; omega
  have hsource := EvenTwoFamilyRows.source_floor_twenty_two (m := m) (by omega : 2≤r)
    hsNat.1 hrNat.2 M hM hkNat.1 hrfit hsfit hdc hc hd
  have htarget := finiteTargetEnergy_antitone (by decide : 2≤7) (by omega : 2≤R)
    (by decide : 4≤11-1) hj hRNat.1 (show 11≤S by dsimp [S]; omega)
  have hcost := endpointCost_lt_floor 22 (show leftEnd 22≤(m : ℝ) by
    norm_num [leftEnd]; exact_mod_cast hm)
  have hraw := CoupledRectangleBounds.refined_rectangle_error (by omega : 4≤R)
    hRNat.2 hsNat.1 hsNat.2 hsum hshape
  have hR0 : (0 : ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have hr0 : (0 : ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have hm0 : (0 : ℝ)<(m : ℝ)-1 := by
    have hh : (9 : ℝ)≤m := by exact_mod_cast hm
    linarith
  have hmr : (m : ℝ)-1≤r := by
    have hh : (m-1 : ℕ)+1≤r+1 := by omega
    have hm1 : m-1+1=m := by omega
    rw [hm1] at hh
    have hh' : (m : ℝ)≤(r : ℝ)+1 := by exact_mod_cast hh
    linarith
  have hg : ((r*s-R*S : ℕ) : ℝ)≤4 := by exact_mod_cast hgap
  have hfirst : ((r*s-R*S : ℕ) : ℝ)/(2*(R : ℝ)^2*(r : ℝ)^2)≤
      4/(2*(R : ℝ)^2*((m : ℝ)-1)^2) := by
    apply (div_le_div_of_nonneg_right hg (by positivity)).trans
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    gcongr
  have hsecond : 1/(4*(r : ℝ)^4)≤1/(4*((m : ℝ)-1)^4) := by
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  have hRcast : (R : ℝ)=(m : ℝ)-2 := by
    have hh : R+2=m := by dsimp [R]; omega
    have hh' : (R : ℝ)+2=m := by exact_mod_cast hh
    linarith
  have herror : error r s-error R S≤remainderBound (1/4) 2 1 4 m := by
    unfold remainderBound
    rw [← hRcast]
    have heq : (1/4 : ℝ)/(R : ℝ)^4=1/(4*(R : ℝ)^4) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [heq]
    linarith only [hraw,hfirst,hsecond]
  have hsourceD : 0≤D (aspectOffset r s) := by
    apply LargeImbalanceGeometry.D_nonneg
    unfold aspectOffset
    have hh : (r : ℝ)≤s := by exact_mod_cast hsNat.1
    have hle : (1 : ℝ)≤(s : ℝ)/r := (le_div_iff₀ hr0).mpr (by simpa only [one_mul] using hh)
    linarith
  have htargetD : D (aspectOffset R S)=aspectStep 0 2 m := by
    have hSreal : (S : ℝ)=(R : ℝ)+4 := by exact_mod_cast (show S=R+4 by dsimp [S,R]; omega)
    have harg : aspectOffset R S=4/((m : ℝ)-2) := by
      unfold aspectOffset
      rw [hSreal,← hRcast]
      field_simp
      <;> ring
    rw [harg]
    norm_num [aspectStep,D]
  apply count_lt_of_refined_cost (by omega : 2≤R) hRNat.2.le hsNat.1 hsNat.2
    M hM hrfit hsfit hj harea hsum herror
  have htcap : finiteTargetEnergy (by omega : 2≤R) hj≤targetCap (targetCapKind 22) := by
    norm_num [targetCapKind,targetCap]
    exact htarget
  norm_num [endpointCost,upperCost,gap,hullShift,errorCoeff,sourceShift] at hcost
  rw [htargetD]
  linarith only [hcost,htcap,hsource,hsourceD]

end
end SpanningTreeIsoperimetry.EvenTwoLastRow
