module

public import SpanningTreeIsoperimetry.CanonicalFluxBounds

@[expose] public section

/-! Selector arithmetic used by the actual large-imbalance scalar test. -/
namespace SpanningTreeIsoperimetry.LargeImbalanceGeometry
open FluxBounds AspectCost
noncomputable section

theorem source_deficit_lower {d T t e : ℕ} (hT : T*(T+e)≤d) (ht : t<T) :
    2*T+e-1+(d-T*(T+e))≤d-t*(t+e) := by
  have hT0 : 1≤T := by omega
  have hsub : T-1+1=T := Nat.sub_add_cancel hT0
  have hstep : 2*T+e-1+1=2*T+e := Nat.sub_add_cancel (by omega)
  have hid : T*(T+e)=(T-1)*(T-1+e)+(2*T+e-1) := by
    calc
      T*(T+e)=(T-1+1)*(T-1+1+e) := by rw [hsub]
      _ = (T-1)*(T-1+e)+(2*(T-1)+e+1) := by ring
      _ = _ := by congr 1 <;> omega
  have hp : t*(t+e)≤(T-1)*(T-1+e) := Nat.mul_le_mul (by omega) (by omega)
  have htfeas := selector_index_feasible hT ht.le
  have hTdef := Nat.sub_add_cancel hT
  have htdef := Nat.sub_add_cancel htfeas
  omega

theorem D_nonneg {w : ℝ} (hw : 0≤w) : 0≤D w := by
  have hh := D_strictMonoOn.monotoneOn (show 0∈Set.Ici (0 : ℝ) by simp)
    (show w∈Set.Ici (0 : ℝ) from hw) hw
  have h0 : D 0=0 := by simp [D]
  simpa only [h0] using hh

theorem D_mono_nonneg {u v : ℝ} (hu : 0≤u) (huv : u≤v) : D u≤D v :=
  D_strictMonoOn.monotoneOn hu (hu.trans huv) huv

theorem canonical_aspect_bound {T e R j : ℕ} (hT : 4≤T) (he : e≤1)
    (hj : j≤2*T+e) (hsize : T^2-T+T*e+j+1≤R) :
    (2*(T : ℝ)+e)/R≤2*T/((T : ℝ)^2-T+j+1) := by
  have ht2 : T≤T^2 := by simpa only [pow_two] using Nat.le_mul_self T
  have hr : (T : ℝ)^2-T+T*e+j+1≤R := by
    have hh : ((T^2-T+T*e+j+1 : ℕ) : ℝ)≤R := by exact_mod_cast hsize
    simpa only [Nat.cast_add,Nat.cast_sub ht2,Nat.cast_pow,Nat.cast_mul,Nat.cast_one] using hh
  have hT' : (4 : ℝ)≤T := by exact_mod_cast hT
  have hj0 : (0 : ℝ)≤j := Nat.cast_nonneg j
  have hA : 0<(T : ℝ)^2-T+j+1 := by nlinarith [sq_nonneg ((T : ℝ)-1)]
  have hT0 : (0 : ℝ)≤T := Nat.cast_nonneg T
  interval_cases e
  · norm_num at hr ⊢
    exact div_le_div_of_nonneg_left (by positivity) hA hr
  · norm_num at hr ⊢
    have hj' : (j : ℝ)≤2*T+1 := by exact_mod_cast hj
    have hAj : (j : ℝ)+1≤(T : ℝ)^2+T := by
      have hp := mul_nonneg (show (0 : ℝ)≤T-2 by linarith)
        (show (0 : ℝ)≤T+1 by positivity)
      nlinarith
    have hbase : 0<(T : ℝ)^2+j+1 := by positivity
    calc
      (2*(T : ℝ)+1)/R ≤ (2*(T : ℝ)+1)/((T : ℝ)^2+j+1) :=
        div_le_div_of_nonneg_left (by positivity) hbase hr
      _ ≤ 2*T/((T : ℝ)^2-T+j+1) := by
        apply (div_le_div_iff₀ hbase hA).mpr
        nlinarith

theorem four_flux_bound {e R S j : ℕ} (he : e≤1) (hj : j≤8+e)
    (hsize : 12+4*e+j+1≤R) (hside : S=R+8+e) :
    fluxBound R S j≤fluxBound 22 30 9 := by
  have hj9 : j≤9 := by omega
  have hr : 13+j≤R := by omega
  have hs : 21+j≤S := by omega
  have hj0 : (0 : ℝ)≤j := Nat.cast_nonneg j
  have hj9' : (j : ℝ)≤9 := by exact_mod_cast hj9
  have hr' : (13 : ℝ)+j≤R := by exact_mod_cast hr
  have hs' : (21 : ℝ)+j≤S := by exact_mod_cast hs
  have hleft := fluxBound_antitone_left (s := (S : ℝ))
    (show 2<(13 : ℝ)+j by linarith) hr' hj0
  have hright := fluxBound_antitone_right (r := (13 : ℝ)+j) hj0
    (show (j : ℝ)+1<21+j by linarith) hs'
  have hdiag := fluxBound_diagonal_monotone (a := (13 : ℝ)) (b := 21)
    (by norm_num) (by norm_num) (show (j : ℝ)∈Set.Icc 0 (13-1) by constructor <;> linarith)
    (show (9 : ℝ)∈Set.Icc 0 (13-1) by norm_num) hj9'
  norm_num at hdiag
  exact hleft.trans (hright.trans hdiag)

end
end SpanningTreeIsoperimetry.LargeImbalanceGeometry
