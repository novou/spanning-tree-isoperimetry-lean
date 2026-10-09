import SpanningTreeIsoperimetry.SummableKernelAlgebra
import SpanningTreeIsoperimetry.SummableDeterminantFirstOrder
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Concrete affine determinant paths at an explicitly invertible identity
perturbation. Every kernel product is the actual convergent entry sum. -/
namespace SpanningTreeIsoperimetry.SummableDeterminantAffine
open SummableKernelProduct SummableKernelAlgebra SummableKernelDeterminant
open SummableDeterminantFirstOrder SummableKernelTrace AbsolutelySummableDeterminant
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def affine (K H : Kernel) (t : ℝ) : Kernel := K+scale t H

def relativeDirection (J H : Kernel) : Kernel := H+product J H

theorem affine_summable {K H : Kernel} (hK : Summable (entryNorm K))
    (hH : Summable (entryNorm H)) (t : ℝ) : Summable (entryNorm (affine K H t)) :=
  add_summable hK (scale_summable t hH)

theorem relative_summable {J H : Kernel} (hJ : Summable (entryNorm J))
    (hH : Summable (entryNorm H)) : Summable (entryNorm (relativeDirection J H)) :=
  add_summable hH (product_summable hJ hH)

/-- Multiplying the relative direction by the original identity perturbation
recovers H, using precisely the stated inverse equation. -/
theorem relative_cancellation {K J H : Kernel} (hK : Summable (entryNorm K))
    (hJ : Summable (entryNorm J)) (hH : Summable (entryNorm H))
    (hKJ : composePerturbation K J=0) :
    relativeDirection J H+product K (relativeDirection J H)=H := by
  have hz := congrArg (fun A => product A H) hKJ
  rw [compose_eq_add,product_add_left (add_summable hK hJ) (product_summable hK hJ) hH,
    product_add_left hK hJ hH,zero_product] at hz
  calc
    relativeDirection J H+product K (relativeDirection J H)=
        H+(product K H+product J H+product (product K J) H) := by
      rw [relativeDirection,product_add_right hK hH (product_summable hJ hH),← product_assoc hK hJ hH]
      abel
    _=H := by rw [hz,add_zero]

theorem affine_factorization {K J H : Kernel} (hK : Summable (entryNorm K))
    (hJ : Summable (entryNorm J)) (hH : Summable (entryNorm H))
    (hKJ : composePerturbation K J=0) (t : ℝ) :
    composePerturbation K (scale t (relativeDirection J H))=affine K H t := by
  have hc := relative_cancellation hK hJ hH hKJ
  have hs (A : Kernel) : scale t A=t • A := rfl
  rw [compose_eq_add,hs,product_smul_right,affine,hs]
  rw [add_assoc,← smul_add,hc]

def affineDeterminant (K H : Kernel) (hK : Summable (entryNorm K))
    (hH : Summable (entryNorm H)) (t : ℝ) : ℝ :=
  detLimit (affine K H t) (affine_summable hK hH t)

theorem affineDeterminant_zero (K H : Kernel) (hK : Summable (entryNorm K))
    (hH : Summable (entryNorm H)) : affineDeterminant K H hK hH 0=detLimit K hK := by
  have he : affine K H 0=K := by ext i j; simp [affine,scale]
  exact detLimit_congr (affine_summable hK hH 0) hK he

theorem affineDeterminant_eq {K J H : Kernel} (hK : Summable (entryNorm K))
    (hJ : Summable (entryNorm J)) (hH : Summable (entryNorm H))
    (hKJ : composePerturbation K J=0) (t : ℝ) :
    affineDeterminant K H hK hH t=
      detLimit K hK*scalarDeterminant (relativeDirection J H) (relative_summable hJ hH) t := by
  have hG := relative_summable hJ hH
  have hc := detLimit_congr (compose_summable hK (scale_summable t hG))
    (affine_summable hK hH t) (affine_factorization hK hJ hH hKJ t)
  exact hc.symm.trans (detLimit_compose hK (scale_summable t hG))

/-- The derivative follows from a proved exact factorization and the actual
scalar determinant derivative at the identity. -/
theorem hasDerivAt_affine_zero {K J H : Kernel} (hK : Summable (entryNorm K))
    (hJ : Summable (entryNorm J)) (hH : Summable (entryNorm H))
    (hKJ : composePerturbation K J=0) :
    HasDerivAt (affineDeterminant K H hK hH)
      (detLimit K hK*trace (relativeDirection J H)) 0 := by
  have he : affineDeterminant K H hK hH=
      fun t => detLimit K hK*scalarDeterminant (relativeDirection J H) (relative_summable hJ hH) t := by
    funext t
    exact affineDeterminant_eq hK hJ hH hKJ t
  rw [he]
  exact (hasDerivAt_scalar_zero (relativeDirection J H) (relative_summable hJ hH)).const_mul (detLimit K hK)

theorem hasDerivAt_log_affine_zero {K J H : Kernel} (hK : Summable (entryNorm K))
    (hJ : Summable (entryNorm J)) (hH : Summable (entryNorm H))
    (hKJ : composePerturbation K J=0) :
    HasDerivAt (fun t => Real.log (affineDeterminant K H hK hH t))
      (trace (relativeDirection J H)) 0 := by
  have hn := (inverse_pair_nonzero hK hJ hKJ).1
  have hz := affineDeterminant_zero K H hK hH
  have hd := (hasDerivAt_affine_zero hK hJ hH hKJ).log (by rw [hz]; exact hn)
  rw [hz] at hd
  convert hd using 1
  field_simp

end
end SpanningTreeIsoperimetry.SummableDeterminantAffine
