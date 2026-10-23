module

public import SpanningTreeIsoperimetry.SmallFamilyDefinitions

@[expose] public section

/-! Exact aspect-cost simplification, independent of derivative certificates. -/
namespace SpanningTreeIsoperimetry.SmallFamilyCosts
open SmallFamilyMonotonicity AspectCost
noncomputable section
theorem aspectStep_eq {a h r : ℝ} (ha : 0≤a) (hh : 0<h) (hr : h<r) :
    aspectStep a h r=Real.pi*h*(2*r+a)/(12*r*(r-h))-(1/2)*Real.log (r/(r-h)) := by
  have hr0 : 0<r := hh.trans hr
  have hden : 0<r-h := by linarith
  have hnum : 0<2*r+a := by positivity
  have hx : 0<1+((a+2*h)/(r-h))/2 := by positivity
  have hy : 0<1+(a/r)/2 := by positivity
  have hratio : (1+((a+2*h)/(r-h))/2)/(1+(a/r)/2)=r/(r-h) := by
    field_simp [hr0.ne',hden.ne',hy.ne',hnum.ne']
    <;> ring
  have hlog : Real.log (1+((a+2*h)/(r-h))/2)-Real.log (1+(a/r)/2)=Real.log (r/(r-h)) := by
    rw [← Real.log_div hx.ne' hy.ne',hratio]
  have hrat : (a+2*h)/(r-h)-a/r=h*(2*r+a)/(r*(r-h)) := by
    field_simp
    <;> ring
  calc
    _=(Real.pi/12)*((a+2*h)/(r-h)-a/r)-
        (1/2)*(Real.log (1+((a+2*h)/(r-h))/2)-Real.log (1+(a/r)/2)) := by
      unfold aspectStep D
      ring
    _=_ := by
      rw [hrat,hlog]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

end
end SpanningTreeIsoperimetry.SmallFamilyCosts
