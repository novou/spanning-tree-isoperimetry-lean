module

public import SpanningTreeIsoperimetry.FiniteCornerCharges
public import SpanningTreeIsoperimetry.RectangleProfileContinuity
public import SpanningTreeIsoperimetry.AspectCost

@[expose] public section

/-! Actual cross-hull count criteria. The analytic remainder bounds are
explicit inputs to these reusable criteria; final exclusions instantiate
them with the checked rectangular error estimates. -/
namespace SpanningTreeIsoperimetry.CrossHullCountComparison
open Ferrers CornerEnergy CornerPrimalDomains CornerStripBridge FiniteCornerProducts
open FiniteCornerCharges RectangleProfileContinuity RectangularRemainder AspectCost
open SquareMaximality.Boundary
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def aspectOffset (r s : ℕ) : ℝ := (s : ℝ)/r-1

def finiteSourceEnergy {r s : ℕ} (M : Corner → Diagram) (hM : ∀ c, IsFerrers (M c))
    (hr : totalDefect M≤r-1) (hs : totalDefect M≤s-1) : ℝ :=
  ∑ c, dirichletEnergy (ferrers_family_fit hM hr hs c)

def finiteTargetEnergy {R S j : ℕ} (hR : 2≤R) (hj : j≤S-1) : ℝ :=
  dirichletEnergy (verticalDiagram_subset (by omega : 1≤R-1) hj)

theorem source_log_upper {r s : ℕ} (hr2 : 2≤r) (hs2 : 2≤s)
    (M : Corner → Diagram) (hM : ∀ c, IsFerrers (M c))
    (hr : totalDefect M≤r-1) (hs : totalDefect M≤s-1) :
    Real.log (treeCount (cornerPrimal (r-1) (s-1) M) : ℝ)≤
      Real.log (treeCount (rectangle r s) : ℝ)-SquareMaximality.squareLatticeEntropy*totalDefect M-
        finiteSourceEnergy M hM hr hs := by
  have hh := corner_log_count_upper (R := r-1) (S := s-1) (by omega) (by omega) hM hr hs
  simpa only [Nat.sub_add_cancel (show 1≤r by omega),Nat.sub_add_cancel (show 1≤s by omega),
    finiteSourceEnergy] using hh

theorem target_log_eq {R S j : ℕ} (hR : 2≤R) (hS : 2≤S) (hj : j≤S-1) :
    Real.log (treeCount (cornerStrip R S j) : ℝ)=
      Real.log (treeCount (rectangle R S) : ℝ)-SquareMaximality.squareLatticeEntropy*j-
        finiteTargetEnergy hR hj := by
  have hh := strip_log_count_eq (R := R-1) (S := S-1) (k := j) (by omega) (by omega) hj
  simpa only [Nat.sub_add_cancel (show 1≤R by omega),Nat.sub_add_cancel (show 1≤S by omega),
    finiteTargetEnergy] using hh

theorem count_lt_of_F_cost {r s R S j : ℕ} (hr2 : 2≤r) (hs2 : 2≤s)
    (hR2 : 2≤R) (hS2 : 2≤S) (M : Corner → Diagram) (hM : ∀ c, IsFerrers (M c))
    (hr : totalDefect M≤r-1) (hs : totalDefect M≤s-1) (hj : j≤S-1)
    (harea : r*s+j=R*S+totalDefect M) (hsum : r+s=R+S) {A : ℝ}
    (hF : F r s-F R S≤A)
    (hcost : finiteTargetEnergy hR2 hj+A<finiteSourceEnergy M hM hr hs) :
    treeCount (cornerPrimal (r-1) (s-1) M)<treeCount (cornerStrip R S j) := by
  have hsrc := source_log_upper hr2 hs2 M hM hr hs
  have htgt := target_log_eq hR2 hS2 hj
  have hareaR : (r : ℝ)*s+j=(R : ℝ)*S+totalDefect M := by exact_mod_cast harea
  have hsumR : (r : ℝ)+s=(R : ℝ)+S := by exact_mod_cast hsum
  have hbulk : SquareMaximality.squareLatticeEntropy*(r : ℝ)*s-
      SquareMaximality.squareLatticeEntropy*(R : ℝ)*S=
      SquareMaximality.squareLatticeEntropy*totalDefect M-SquareMaximality.squareLatticeEntropy*j := by
    have hh := congrArg (fun x : ℝ => SquareMaximality.squareLatticeEntropy*x) hareaR
    linear_combination hh
  have hboundary := congrArg (fun x : ℝ => SquareMaximality.Rectangle.Concrete.alpha*x) hsumR
  unfold F at hF
  have hlog : Real.log (treeCount (cornerPrimal (r-1) (s-1) M) : ℝ)<
      Real.log (treeCount (cornerStrip R S j) : ℝ) := by
    linarith only [hsrc,htgt,hF,hcost,hbulk,hboundary]
  have hpSrc := corner_count_pos (R := r-1) (S := s-1) (by omega) (by omega) hM hr hs
  have hpTgt : (0 : ℝ)<treeCount (cornerStrip R S j) := by
    have hh := strip_count_pos (R := R-1) (S := S-1) (k := j) (by omega) (by omega) hj
    simpa only [Nat.sub_add_cancel (show 1≤R by omega),Nat.sub_add_cancel (show 1≤S by omega)] using hh
  exact_mod_cast (Real.log_lt_log_iff hpSrc hpTgt).mp hlog

theorem F_difference_le {r s R S : ℕ} (hR : 2≤R) (hRr : R≤r) (hrs : r≤s)
    (hsS : s≤S) (hsum : r+s=R+S) {P : ℝ} (herror : error r s-error R S≤P) :
    F r s-F R S≤D (aspectOffset R S)-D (aspectOffset r s)+P := by
  have hr0 : 0<r := by omega
  have hs0 : 0<s := by omega
  have hR0 : 0<R := by omega
  have hS0 : 0<S := by omega
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr0
  have hRR : (0 : ℝ)<R := by exact_mod_cast hR0
  have hrsR : (r : ℝ)≤s := by exact_mod_cast hrs
  have hsSR : (s : ℝ)≤S := by exact_mod_cast hsS
  have hRrR : (R : ℝ)≤r := by exact_mod_cast hRr
  have hratio : (s : ℝ)/r≤(S : ℝ)/R :=
    (div_le_div_of_nonneg_right hsSR hrR.le).trans
      (div_le_div_of_nonneg_left (Nat.cast_nonneg S) hRR hRrR)
  have ha : 0≤aspectOffset r s := by
    have hh : (1 : ℝ)≤(s : ℝ)/r := (le_div_iff₀ hrR).mpr (by simpa using hrsR)
    unfold aspectOffset
    linarith
  have hab : aspectOffset r s≤aspectOffset R S := by unfold aspectOffset; linarith
  have hK := aspect_difference ha hab
  rw [show 1+aspectOffset r s=(s : ℝ)/r by unfold aspectOffset; ring,
    show 1+aspectOffset R S=(S : ℝ)/R by unfold aspectOffset; ring] at hK
  have hF1 := F_eq_K hr0 hs0
  have hF2 := F_eq_K hR0 hS0
  have hsumR : (r : ℝ)+s=(R : ℝ)+S := by exact_mod_cast hsum
  rw [hsumR] at hF1
  linarith

theorem count_lt_of_refined_cost {r s R S j : ℕ} (hR : 2≤R) (hRr : R≤r) (hrs : r≤s)
    (hsS : s≤S) (M : Corner → Diagram) (hM : ∀ c, IsFerrers (M c))
    (hr : totalDefect M≤r-1) (hs : totalDefect M≤s-1) (hj : j≤S-1)
    (harea : r*s+j=R*S+totalDefect M) (hsum : r+s=R+S) {P : ℝ}
    (herror : error r s-error R S≤P)
    (hcost : finiteTargetEnergy hR hj+D (aspectOffset R S)-D (aspectOffset r s)+P <
      finiteSourceEnergy M hM hr hs) :
    treeCount (cornerPrimal (r-1) (s-1) M)<treeCount (cornerStrip R S j) := by
  apply count_lt_of_F_cost (by omega) (by omega) hR (by omega) M hM hr hs hj harea hsum
    (F_difference_le hR hRr hrs hsS hsum herror)
  linarith

theorem finite_target_upper {R S j : ℕ} (hR : 3≤R) (hS : 2≤S) (hj : j+1<S) :
    finiteTargetEnergy (by omega : 2≤R) (by omega : j≤S-1)≤
      realEnergy (horizontalStrip j)+FluxBounds.fluxBound R S j := by
  by_cases hj0 : j=0
  · subst j
    have hh := target_log_eq (by omega : 2≤R) hS (show 0≤S-1 by omega)
    have hstrip : cornerStrip R S 0=rectangle R S := by simp [cornerStrip,rectangle]
    simp only [hstrip,Nat.cast_zero,mul_zero,sub_zero] at hh
    have hzero : finiteTargetEnergy (by omega : 2≤R) (show 0≤S-1 by omega)=0 := by linarith
    have hflux : FluxBounds.fluxBound (R : ℝ) S 0=0 := by
      simp [FluxBounds.fluxBound,FluxBounds.cubic,FluxBounds.quadratic]
    rw [hzero,realEnergy_strip_zero,Nat.cast_zero,hflux]
    norm_num
  · exact finite_strip_upper_primal hR (by omega) hj

theorem source_energy_charged {r s : ℕ} (M : Corner → Diagram) (hM : ∀ c, IsFerrers (M c))
    (hr : totalDefect M≤r-1) (hs : totalDefect M≤s-1) :
    (∑ c,realEnergy (M c))+(totalDefect M : ℝ)*correction (faceRectangle (r-1) (s-1)) {(0,0)}≤
      finiteSourceEnergy M hM hr hs := by
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset Corner))
    (fun c _ => finite_energy_ge_cell_charge (hM c) (ferrers_family_fit hM hr hs c))
  rw [Finset.sum_add_distrib,← Finset.sum_mul] at hh
  have hc : (∑ c : Corner, ((M c).card : ℝ))=(totalDefect M : ℝ) := by
    simp only [totalDefect,Nat.cast_sum]
  rw [hc] at hh
  exact hh

theorem count_lt_of_normalized_cost {r s R S j : ℕ} (hR : 3≤R) (hRr : R≤r) (hrs : r≤s)
    (hsS : s≤S) (M : Corner → Diagram) (hM : ∀ c, IsFerrers (M c))
    (hr : totalDefect M≤r-1) (hs : totalDefect M≤s-1) (hj : j+1<S)
    (harea : r*s+j=R*S+totalDefect M) (hsum : r+s=R+S)
    (habsorb : error r s-error R S≤((totalDefect M : ℝ)-j)*
      correction (faceRectangle (r-1) (s-1)) {(0,0)})
    (hcost : realEnergy (horizontalStrip j)+D (aspectOffset R S)-D (aspectOffset r s)+
      FluxBounds.fluxBound R S j < ∑ c,realEnergy (M c)) :
    treeCount (cornerPrimal (r-1) (s-1) M)<treeCount (cornerStrip R S j) := by
  apply count_lt_of_refined_cost (by omega : 2≤R) hRr hrs hsS M hM hr hs
    (show j≤S-1 by omega) harea hsum habsorb
  have ht := finite_target_upper hR (by omega : 2≤S) hj
  have he := source_energy_charged M hM hr hs
  have hc := correction_nonneg (faceRectangle (r-1) (s-1)) {(0,0)}
  have hjc := mul_nonneg (Nat.cast_nonneg j : (0 : ℝ)≤j) hc
  linarith

end
end SpanningTreeIsoperimetry.CrossHullCountComparison
