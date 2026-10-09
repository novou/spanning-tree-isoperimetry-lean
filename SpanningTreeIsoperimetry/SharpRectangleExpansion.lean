import SpanningTreeIsoperimetry.RectangularSecondProfile
import SpanningTreeIsoperimetry.RectangleResidualBounds
import SpanningTreeIsoperimetry.TrapezoidalKernelError

/-! Exact decomposition underlying the sharp fourth-order rectangle error.
The quantitative fourth-order bound is assembled separately from this identity. -/
namespace SpanningTreeIsoperimetry.SharpRectangleExpansion

open SquareMaximality SquareMaximality.Rectangle
open RectangularRemainder RectangularSecondProfile RectangleResidualBounds TrapezoidalKernelError
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def omittedBose (u : ℝ) (r : ℕ) : ℝ :=
  ∑' n : ℕ, ((r+n : ℕ) : ℝ)^3/(Real.exp (2*Real.pi*u*(r+n))-1)

def retainedCorrection (r s : ℕ) : ℝ := ∑ j∈Finset.Ico 1 r,
  (logTerm s (gamma (Real.pi*j/r))-logTerm s (Real.pi*j/r)+
    (s : ℝ)*(Real.pi*j/r)^3/(6*(Real.exp (2*s*(Real.pi*j/r))-1)))

def sharpError (r s : ℕ) : ℝ := error r s+K2 ((s : ℝ)/r)/((r : ℝ)+s)^2

theorem boseCubic_decomposition {u : ℝ} (hu : 0<u) {r : ℕ} (hr : 0<r) :
    boseCubic u=(∑ j∈Finset.Ico 1 r, (j : ℝ)^3/(Real.exp (2*Real.pi*u*j)-1))+omittedBose u r := by
  have hs := boseCubic_summable hu
  unfold boseCubic
  rw [← hs.sum_add_tsum_nat_add (r-1),Finset.sum_Ico_eq_sum_range]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    congr 2 <;> push_cast <;> ring
  · unfold omittedBose
    apply tsum_congr
    intro n
    congr 2 <;> push_cast [Nat.cast_sub (show 1≤r by omega)] <;> ring

theorem normalized_K2 {r s : ℕ} (hr : 0<r) (hs : 0<s) :
    K2 ((s : ℝ)/r)/((r : ℝ)+s)^2=
      Real.pi^3*s/(1440*(r : ℝ)^3)*(1+240*boseCubic ((s : ℝ)/r)) := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hsR : (0 : ℝ)<s := by exact_mod_cast hs
  have hL : (0 : ℝ)<(r : ℝ)+s := by positivity
  unfold K2
  field_simp [hrR.ne',hL.ne'] <;> ring

private theorem node_correction_eq {r s : ℕ} (hr : 0<r) (hs : 0<s) {j : ℕ} (hj : 0<j) :
    (s : ℝ)*(Real.pi*j/r)^3/(6*(Real.exp (2*s*(Real.pi*j/r))-1))=
      (Real.pi^3*s/(6*(r : ℝ)^3))*((j : ℝ)^3/(Real.exp (2*Real.pi*((s : ℝ)/r)*j)-1)) := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hsR : (0 : ℝ)<s := by exact_mod_cast hs
  have hjR : (0 : ℝ)<j := by exact_mod_cast hj
  have harg : 2*(s : ℝ)*(Real.pi*j/r)=2*Real.pi*((s : ℝ)/r)*j := by ring
  rw [harg]
  have hd : 0<Real.exp (2*Real.pi*((s : ℝ)/r)*j)-1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))
  field_simp [hrR.ne',hd.ne'] <;> ring

private theorem linear_mode_eq (r s j : ℝ) :
    Real.log (1-Real.exp (-2*Real.pi*(s/r)*j))=logTerm s (Real.pi*j/r) := by
  unfold logTerm
  congr 2
  ring

theorem retainedCorrection_eq {r s : ℕ} (hr : 0<r) (hs : 0<s) :
    retainedCorrection r s=
      (RectangularComparison.realResidual r s-
        ∑ j∈Finset.Ico 1 r, Real.log (1-Real.exp (-2*Real.pi*((s : ℝ)/r)*j)))+
      (Real.pi^3*s/(6*(r : ℝ)^3))*
        (∑ j∈Finset.Ico 1 r, (j : ℝ)^3/(Real.exp (2*Real.pi*((s : ℝ)/r)*j)-1)) := by
  rw [retainedCorrection,realResidual_as_gamma hr]
  simp_rw [linear_mode_eq]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact node_correction_eq hr hs (Finset.mem_Ico.mp hj).1

/-- Exact actual sharp error decomposition: quadrature correction, retained
Taylor errors, omitted linear/cubic modes, and the endpoint logarithm. -/
theorem sharpError_exact {r s : ℕ} (hr : 0<r) (hs : 0<s) :
    sharpError r s=
      -(s : ℝ)*(Concrete.epsilon squareLatticeEntropy r-Real.pi/(12*r)-Real.pi^3/(1440*(r : ℝ)^3))+
      retainedCorrection r s-logTail (Real.exp (-2*Real.pi*((s : ℝ)/r))) r+
      (Real.pi^3*s/(6*(r : ℝ)^3))*omittedBose ((s : ℝ)/r) r-
      (1/2)*Real.log (1-Real.exp (-4*r*Concrete.alpha)) := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hsR : (0 : ℝ)<s := by exact_mod_cast hs
  have hu : 0<(s : ℝ)/r := div_pos hsR hrR
  rw [sharpError,error_exact hr hs,normalized_K2 hr hs,retainedCorrection_eq hr hs,
    linearResidual_decomposition hu hr,boseCubic_decomposition hu hr]
  ring

end
end SpanningTreeIsoperimetry.SharpRectangleExpansion
