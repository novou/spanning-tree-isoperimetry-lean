module

public import SpanningTreeIsoperimetry.SingleCornerShallowEnergy
public import SpanningTreeIsoperimetry.SmallFamilyCountComparison
public import SpanningTreeIsoperimetry.LargeImbalanceGeometry

@[expose] public section

set_option backward.privateInPublic true

/-! Shallow costs in actual source and target hull coordinates. -/
namespace SpanningTreeIsoperimetry.SingleCornerParameterCosts
open Ferrers CornerEnergy StripRigidity SingleCornerShallowEnergy SingleCornerShallowCosts
open LargeImbalanceGeometry SmallFamilyCountComparison SmallFamilyMonotonicity CrossHullCountComparison AspectCost FluxBounds
noncomputable section

private theorem offset_shift {R a : ℕ} (hR : 0<R) : aspectOffset R (R+a)=(a : ℝ)/R := by
  unfold aspectOffset
  push_cast
  have hn : (R : ℝ)≠0 := by exact_mod_cast hR.ne'
  field_simp
  <;> ring

theorem even_three_cost {R r s S j : ℕ} (hj : j≤6) (hR : j+7≤R)
    (hr : r=R+1) (hs : s=r+4) (hS : S=R+6)
    {M : Diagram} (hM : IsFerrers M) (hn : ¬IsStraightStrip M) (hk : j+5≤M.card) :
    realEnergy (horizontalStrip j)+D (aspectOffset R S)-D (aspectOffset r s)+
      fluxBound R S j<realEnergy M := by
  have hb := even_three_energy (r := (r : ℝ)) hj
    (by exact_mod_cast (show j+8≤r by omega)) hM hn hk
  have hdiff := aspect_difference (R := R) (r := r) (s := s) (S := S) (a := 4) (h := 1)
    (by omega) hr hs (by omega)
  norm_num at hdiff
  have hrr : (r : ℝ)-1=R := by rw [hr]; push_cast; ring
  have hss : (r : ℝ)+5=S := by rw [hr,hS]; push_cast; ring
  rw [hrr,hss] at hb
  have he : realEnergy (horizontalStrip j)+D (aspectOffset R S)-D (aspectOffset r s)=
      realEnergy (horizontalStrip j)+aspectStep 4 1 r := by linarith only [hdiff]
  rw [he]
  exact hb

theorem odd_three_cost {R r s S j : ℕ} (hj : j≤7) (hR : j+10≤R)
    (hr : r=R+1 ∨ r=R+2) (hsum : r+s=2*R+7) (hS : S=R+7)
    {M : Diagram} (hM : IsFerrers M) (hn : ¬IsStraightStrip M) (hk : j+5≤M.card) :
    realEnergy (horizontalStrip j)+D (aspectOffset R S)-D (aspectOffset r s)+
      fluxBound R S j<realEnergy M := by
  have hR0 : (0 : ℝ)<R := by exact_mod_cast (show 0<R by omega)
  have hb := odd_three_energy (r := (R : ℝ)+2) hj
    (by
      have hh : (j : ℝ)+10≤R := by exact_mod_cast hR
      linarith) hM hn hk
  have htarget : aspectOffset R S=7/(R : ℝ) := by rw [hS]; exact offset_shift (by omega)
  have hsource : D (3/((R : ℝ)+2))≤D (aspectOffset r s) := by
    rcases hr with hr|hr
    · have hs : s=r+5 := by omega
      rw [hs,offset_shift (by omega),hr,Nat.cast_add,Nat.cast_one]
      apply D_mono_nonneg (by positivity)
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ)<(R : ℝ)+2) (by positivity : (0 : ℝ)<(R : ℝ)+1)]
      norm_num
      linarith
    · have hs : s=r+3 := by omega
      rw [hs,offset_shift (by omega),hr,Nat.cast_add]
      norm_num
  have hleft : (R : ℝ)+2-2=R := by ring
  have hright : (R : ℝ)+2+5=S := by rw [hS]; push_cast; ring
  rw [hleft,hright] at hb
  have hstep : aspectStep 3 2 ((R : ℝ)+2)=D (7/(R : ℝ))-D (3/((R : ℝ)+2)) := by
    unfold aspectStep
    norm_num
  rw [hstep] at hb
  rw [htarget]
  linarith only [hb,hsource]

theorem odd_two_cost {R r s S j : ℕ} (hj : j≤5) (hrlo : j+6≤r)
    (hr : r=R+1) (hs : s=r+3) (hS : S=r+4) :
    realEnergy (horizontalStrip j)+D (aspectOffset R S)-D (aspectOffset r s)+
      fluxBound R S j<(if j=0 then (2837 : ℝ)/50000 else 7421/100000) := by
  let q : Fin 6 := ⟨j,by omega⟩
  have hb := single_odd_cost (r := (r : ℝ)) q (by exact_mod_cast hrlo)
  have hdiff := aspect_difference (R := R) (r := r) (s := s) (S := S) (a := 3) (h := 1)
    (by omega) hr hs (by omega)
  norm_num at hdiff
  have hrr : (r : ℝ)-1=R := by rw [hr]; push_cast; ring
  have hss : (r : ℝ)+4=S := by rw [hS]; push_cast; rfl
  have hq0 : q=0 ↔ j=0 := by simp [q,Fin.ext_iff]
  change realEnergy (horizontalStrip j)+aspectStep 3 1 r+fluxBound ((r : ℝ)-1) ((r : ℝ)+4) j<
    (if q=0 then (2837 : ℝ)/50000 else 7421/100000) at hb
  rw [hrr,hss] at hb
  simp only [hq0] at hb
  have he : realEnergy (horizontalStrip j)+D (aspectOffset R S)-D (aspectOffset r s)=
      realEnergy (horizontalStrip j)+aspectStep 3 1 r := by linarith only [hdiff]
  rw [he]
  exact hb

end
end SpanningTreeIsoperimetry.SingleCornerParameterCosts
