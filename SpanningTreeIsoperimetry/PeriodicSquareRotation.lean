import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Concrete periodic-square integration under (u,v)↦(u+v,u−v).
Only bounded measurability and two separate periods are used. The proof is
real-variable substitution, interval-shift invariance and Fubini. -/
namespace SpanningTreeIsoperimetry.PeriodicSquareRotation
open MeasureTheory Set Function
open scoped Topology ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem interval_integrable {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ x,|f x|≤C) (a b : ℝ) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  apply IntegrableOn.of_bound
    (lt_of_le_of_lt (measure_mono uIoc_subset_uIcc) isCompact_uIcc.measure_lt_top)
    hf.aestronglyMeasurable.restrict C
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x)

theorem rectangle_integrable {F : ℝ → ℝ → ℝ}
    (hF : Measurable (fun p : ℝ × ℝ => F p.1 p.2)) {C : ℝ}
    (hb : ∀ x y,|F x y|≤C) (a b c d : ℝ) :
    IntegrableOn F.uncurry (uIoc a b ×ˢ uIoc c d) := by
  apply IntegrableOn.of_bound
    (lt_of_le_of_lt (measure_mono (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc))
      (isCompact_uIcc.prod isCompact_uIcc).measure_lt_top)
    hF.aestronglyMeasurable.restrict C
  exact Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs] using hb p.1 p.2)

theorem integral_two_periods {f : ℝ → ℝ} {L : ℝ} (hper : Periodic f L)
    (hf : Measurable f) {C : ℝ} (hb : ∀ x,|f x|≤C) (t : ℝ) :
    (∫ x in t..t+2*L,f x)=2*∫ x in (0 : ℝ)..L,f x := by
  have h := hper.intervalIntegral_add_zsmul_eq (2 : ℤ) t (interval_integrable hf hb)
  have hp := hper.intervalIntegral_add_eq t 0
  simp only [zero_add] at hp
  rw [hp] at h
  simpa only [two_zsmul,two_mul] using h

/-- Periodic-square invariance under the two-to-one torus rotation, proved
without a quotient-space or Haar-measure adapter. -/
theorem rotation_invariant {F : ℝ → ℝ → ℝ} {L C : ℝ}
    (hF : Measurable (fun p : ℝ × ℝ => F p.1 p.2))
    (hb : ∀ x y,|F x y|≤C)
    (hx : ∀ y,Periodic (fun x => F x y) L) (hy : ∀ x,Periodic (F x) L) :
    (∫ u in (0 : ℝ)..L,∫ v in (0 : ℝ)..L,F (u+v) (u-v))=
      ∫ x in (0 : ℝ)..L,∫ y in (0 : ℝ)..L,F x y := by
  have hinner (u : ℝ) :
      (∫ v in (0 : ℝ)..L,F (u+v) (u-v))=∫ x in (0 : ℝ)..L,F x (2*u-x) := by
    let g : ℝ → ℝ := fun x => F x (2*u-x)
    have hg : Periodic g L := by
      intro x
      change F (x+L) (2*u-(x+L))=F x (2*u-x)
      have hshift := hx (2*u-(x+L)) x
      change F (x+L) (2*u-(x+L))=F x (2*u-(x+L)) at hshift
      rw [hshift,show 2*u-(x+L)=(2*u-x)-L by ring,(hy x).sub_eq]
    calc
      _=∫ v in (0 : ℝ)..L,g (u+v) := by
        apply intervalIntegral.integral_congr
        intro v _
        dsimp [g]
        congr 1
        ring
      _=∫ x in u..u+L,g x := by
        simpa only [add_zero] using intervalIntegral.integral_comp_add_left (f := g) (a := 0) (b := L) u
      _=∫ x in (0 : ℝ)..L,g x := by
        simpa only [zero_add] using hg.intervalIntegral_add_eq u 0
  have hdouble (x : ℝ) :
      (∫ u in (0 : ℝ)..L,F x (2*u-x))=∫ y in (0 : ℝ)..L,F x y := by
    have hm : Measurable (F x) := hF.comp (by fun_prop : Measurable (fun y : ℝ => (x,y)))
    have h := intervalIntegral.smul_integral_comp_mul_add (f := F x) (a := 0) (b := L) (2 : ℝ) (-x)
    have h' : 2*(∫ u in (0 : ℝ)..L,F x (2*u-x))=∫ y in -x..(-x)+2*L,F x y := by
      convert h using 1 <;> simp only [smul_eq_mul,sub_eq_add_neg,mul_zero,zero_add] <;>
        congr 1 <;> ring
    rw [integral_two_periods (hy x) hm (hb x)] at h'
    linarith only [h']
  have hm : Measurable (fun p : ℝ × ℝ => F p.2 (2*p.1-p.2)) :=
    hF.comp (by fun_prop : Measurable (fun p : ℝ × ℝ => (p.2,2*p.1-p.2)))
  have hi := rectangle_integrable (F := fun u x => F x (2*u-x)) hm (fun u x => hb x (2*u-x)) 0 L 0 L
  calc
    _=∫ u in (0 : ℝ)..L,∫ x in (0 : ℝ)..L,F x (2*u-x) := by
      apply intervalIntegral.integral_congr
      intro u _
      exact hinner u
    _=∫ x in (0 : ℝ)..L,∫ u in (0 : ℝ)..L,F x (2*u-x) :=
      intervalIntegral_intervalIntegral_swap hi
    _=_ := by
      apply intervalIntegral.integral_congr
      intro x _
      exact hdouble x

theorem integral_reflection (f : ℝ → ℝ) (L : ℝ) :
    (∫ x in (0 : ℝ)..L,f (L-x))=∫ x in (0 : ℝ)..L,f x := by
  simpa only [sub_self,sub_zero] using
    intervalIntegral.integral_comp_sub_left (f := f) (a := 0) (b := L) L

theorem integral_eq_two_half {f : ℝ → ℝ} {L C : ℝ} (hf : Measurable f)
    (hb : ∀ x,|f x|≤C) (hreflect : ∀ x,f (L-x)=f x) :
    (∫ x in (0 : ℝ)..L,f x)=2*∫ x in (0 : ℝ)..L/2,f x := by
  have h := intervalIntegral.integral_comp_sub_left (f := f) (a := L/2) (b := L) L
  simp_rw [hreflect] at h
  rw [sub_self,show L-L/2=L/2 by ring] at h
  rw [← intervalIntegral.integral_add_adjacent_intervals (interval_integrable hf hb 0 (L/2))
    (interval_integrable hf hb (L/2) L),h]
  ring

theorem square_eq_four_quarter {F : ℝ → ℝ → ℝ} {L C : ℝ}
    (hF : Measurable (fun p : ℝ × ℝ => F p.1 p.2)) (hb : ∀ x y,|F x y|≤C)
    (hx : ∀ x y,F (L-x) y=F x y) (hy : ∀ x y,F x (L-y)=F x y) :
    (∫ x in (0 : ℝ)..L,∫ y in (0 : ℝ)..L,F x y)=
      4*∫ x in (0 : ℝ)..L/2,∫ y in (0 : ℝ)..L/2,F x y := by
  have hmY (x : ℝ) : Measurable (F x) :=
    hF.comp (by fun_prop : Measurable (fun y : ℝ => (x,y)))
  have hmX (y : ℝ) : Measurable (fun x => F x y) :=
    hF.comp (by fun_prop : Measurable (fun x : ℝ => (x,y)))
  have h1 : (∫ x in (0 : ℝ)..L,∫ y in (0 : ℝ)..L,F x y)=
      2*∫ x in (0 : ℝ)..L,∫ y in (0 : ℝ)..L/2,F x y := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    exact integral_eq_two_half (hmY x) (hb x) (hy x)
  have h2 := intervalIntegral_intervalIntegral_swap (rectangle_integrable (F := F) hF hb 0 L 0 (L/2))
  have h3 : (∫ y in (0 : ℝ)..L/2,∫ x in (0 : ℝ)..L,F x y)=
      2*∫ y in (0 : ℝ)..L/2,∫ x in (0 : ℝ)..L/2,F x y := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y _
    exact integral_eq_two_half (hmX y) (fun x => hb x y) (fun x => hx x y)
  have h4 := intervalIntegral_intervalIntegral_swap (rectangle_integrable (F := F) hF hb 0 (L/2) 0 (L/2))
  rw [h1,h2,h3,← h4]
  ring

end
end SpanningTreeIsoperimetry.PeriodicSquareRotation
