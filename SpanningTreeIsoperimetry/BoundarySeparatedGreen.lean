module

public import SpanningTreeIsoperimetry.BoundarySineModes
public import SpanningTreeIsoperimetry.BoundaryHyperbolic
public import Mathlib.Analysis.SpecialFunctions.Arcosh

@[expose] public section

/-! Finite separation of variables for actual rectangular boundary Green
entries, using the checked sine modes and continuant inverse formula. -/
namespace SpanningTreeIsoperimetry.BoundarySeparatedGreen
open ScalarResolvent BoundarySineModes BoundaryHyperbolic SmallCases
open scoped BigOperators Matrix Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def modeGamma (n : ℕ) (j : Fin n) : ℝ := Real.arcosh (2-Real.cos (angle n j))

theorem cosine_lt_one (n : ℕ) (j : Fin n) : Real.cos (angle n j)<1 := by
  have h := Real.strictAntiOn_cos ⟨le_rfl,Real.pi_pos.le⟩
    ⟨(angle_pos n j).le,(angle_lt_pi n j).le⟩ (angle_pos n j)
  simpa only [Real.cos_zero] using h

theorem modeGamma_pos (n : ℕ) (j : Fin n) : 0<modeGamma n j := by
  unfold modeGamma
  apply Real.arcosh_pos
  linarith [cosine_lt_one n j]

theorem eigenvalue_eq_cosh (n : ℕ) (j : Fin n) :
    eigenvalue n j=2*Real.cosh (modeGamma n j) := by
  rw [modeGamma,Real.cosh_arcosh (show 1≤2-Real.cos (angle n j) by linarith [cosine_lt_one n j])]
  unfold eigenvalue
  ring

theorem continuant_eigenvalue_pos (n R : ℕ) (j : Fin n) :
    0<continuant (eigenvalue n j) R := by
  rw [eigenvalue_eq_cosh,continuant_cosh _ (modeGamma_pos n j)]
  apply div_pos
  · apply Real.sinh_pos_iff.mpr
    exact mul_pos (by positivity) (modeGamma_pos n j)
  · exact Real.sinh_pos_iff.mpr (modeGamma_pos n j)

theorem mode_continuant (n R : ℕ) (j : Fin n) :
    operatorContinuant n R *ᵥ mode n j=continuant (eigenvalue n j) R • mode n j := by
  induction R using Nat.twoStepInduction with
  | zero => simp
  | one => simpa only [operatorContinuant_one,continuant_one] using mode_mulVec n j
  | more R ih ih1 =>
    rw [operatorContinuant_recurrence,Matrix.sub_mulVec,← Matrix.mulVec_mulVec,ih1,
      Matrix.mulVec_smul,mode_mulVec,ih]
    rw [smul_smul,← sub_smul,continuant_recurrence]
    congr 1
    ring

/-- Actual finite boundary Green matrix on each sine mode. -/
theorem boundaryGreen_mode {R : ℕ} (hR : 0<R) (n : ℕ) (j : Fin n) :
    boundaryGreen hR n *ᵥ mode n j=
      (continuant (eigenvalue n j) (R-1)/continuant (eigenvalue n j) R) • mode n j := by
  have hB := green_first_column_continuant hR n ⟨0,hR⟩
  change boundaryGreen hR n*operatorContinuant n R=operatorContinuant n (R-1-0) at hB
  simp only [Nat.sub_zero] at hB
  have hv := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M *ᵥ mode n j) hB
  rw [← Matrix.mulVec_mulVec,mode_continuant,Matrix.mulVec_smul,mode_continuant] at hv
  ext i
  have hi := congrFun hv i
  simp only [Pi.smul_apply,smul_eq_mul] at hi ⊢
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (continuant_eigenvalue_pos n R j).ne').mpr
  nlinarith only [hi]

theorem sineMatrix_transpose (n : ℕ) : (sineMatrix n).transpose=sineMatrix n := by
  ext i j
  simp only [Matrix.transpose_apply,sineMatrix,mode]
  congr 1
  unfold angle
  ring

theorem sineMatrix_right_gram (n : ℕ) :
    sineMatrix n*(sineMatrix n).transpose=(((n : ℝ)+1)/2) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [sineMatrix_transpose]
  simpa only [sineMatrix_transpose] using sineMatrix_gram n

/-- Complete finite sine expansion of the actual rectangular Green boundary
block. The operator identity and the normalization are both proved locally. -/
theorem boundaryGreen_entry {R : ℕ} (hR : 0<R) (n : ℕ) (a b : Fin n) :
    boundaryGreen hR n a b=
      (2/((n : ℝ)+1))*∑ j : Fin n, mode n j a*mode n j b*
        (continuant (eigenvalue n j) (R-1)/continuant (eigenvalue n j) R) := by
  have hm : (boundaryGreen hR n*sineMatrix n)*(sineMatrix n).transpose=
      (((n : ℝ)+1)/2) • boundaryGreen hR n := by
    rw [Matrix.mul_assoc,sineMatrix_right_gram,Matrix.mul_smul,Matrix.mul_one]
  have hbq (j : Fin n) : (boundaryGreen hR n*sineMatrix n) a j=
      (continuant (eigenvalue n j) (R-1)/continuant (eigenvalue n j) R)*mode n j a := by
    change (boundaryGreen hR n *ᵥ mode n j) a=_
    exact congrFun (boundaryGreen_mode hR n j) a
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M a b) hm
  change (∑ j : Fin n, (boundaryGreen hR n*sineMatrix n) a j*mode n j b)=
    (((n : ℝ)+1)/2)*boundaryGreen hR n a b at he
  simp_rw [hbq] at he
  have hs : (∑ j : Fin n,
      (continuant (eigenvalue n j) (R-1)/continuant (eigenvalue n j) R)*mode n j a*mode n j b)=
      ∑ j : Fin n, mode n j a*mode n j b*
        (continuant (eigenvalue n j) (R-1)/continuant (eigenvalue n j) R) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs] at he
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (by positivity : (n : ℝ)+1≠0)).mpr
  nlinarith only [he]

/-- Hyperbolic spelling of that same actual inverse-entry expansion. -/
theorem boundaryGreen_entry_sinh (R n : ℕ) (a b : Fin n) :
    boundaryGreen (Nat.zero_lt_succ R) n a b=
      (2/((n : ℝ)+1))*∑ j : Fin n, mode n j a*mode n j b*
        (Real.sinh (((R : ℝ)+1)*modeGamma n j)/
          Real.sinh (((R : ℝ)+2)*modeGamma n j)) := by
  rw [boundaryGreen_entry]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [Nat.succ_sub_one,Nat.succ_eq_add_one,Nat.add_sub_cancel,eigenvalue_eq_cosh,
    endpoint_ratio _ (modeGamma_pos n j)]

end
end SpanningTreeIsoperimetry.BoundarySeparatedGreen
