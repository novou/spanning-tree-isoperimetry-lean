module

public import SpanningTreeIsoperimetry.BoundarySpectralKernel
public import SpanningTreeIsoperimetry.ScalarModular
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

/-! The explicit trigonometric residue expression in Section 7.
This is an independent proof-route addition; the scalar product theorem is
already closed without this spectral representation. -/
namespace SpanningTreeIsoperimetry.ScalarSpectralResidues
open ScalarResolvent ScalarModular BoundarySineModes BoundarySeparatedGreen
open BoundarySpectralKernel SmallCases Polynomial
open scoped Matrix BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def residue (R w : ℕ) (j : Fin w) : ℝ :=
  (2/((w : ℝ)+1))*Real.sin (angle w j)^2*
    (continuant (eigenvalue w j) (R-1)/continuant (eigenvalue w j) R)

theorem residue_pos (R w : ℕ) (j : Fin w) : 0<residue R w j := by
  have hs := Real.sin_pos_of_pos_of_lt_pi (angle_pos w j) (angle_lt_pi w j)
  have hf := continuant_eigenvalue_pos w (R-1) j
  have hg := continuant_eigenvalue_pos w R j
  unfold residue
  positivity

theorem eigenvalue_strictMono (w : ℕ) : StrictMono (eigenvalue w) := by
  intro i j hij
  have hval : (i.val : ℝ)<j.val := by exact_mod_cast hij
  have hangle : angle w i<angle w j := by
    unfold angle
    apply (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ)<w+1)).mpr
    nlinarith [Real.pi_pos]
  have hc := Real.strictAntiOn_cos ⟨(angle_pos w i).le,(angle_lt_pi w i).le⟩
    ⟨(angle_pos w j).le,(angle_lt_pi w j).le⟩ hangle
  unfold eigenvalue
  linarith

theorem eigenvalue_bounds (w : ℕ) (j : Fin w) : 2<eigenvalue w j ∧ eigenvalue w j<6 := by
  have hc1 := cosine_lt_one w j
  have hc2 := Real.strictAntiOn_cos ⟨(angle_pos w j).le,(angle_lt_pi w j).le⟩
    ⟨Real.pi_pos.le,le_rfl⟩ (angle_lt_pi w j)
  rw [Real.cos_pi] at hc2
  unfold eigenvalue
  constructor <;> linarith

def spectralInverse (w : ℕ) (z : ℝ) : Matrix (Fin w) (Fin w) ℝ :=
  (2/((w : ℝ)+1)) • ∑ j : Fin w, (z-eigenvalue w j)⁻¹ • modeOuter w j

theorem shifted_modeOuter (w : ℕ) (z : ℝ) (j : Fin w) :
    (z • (1 : Matrix (Fin w) (Fin w) ℝ)-pathOperator w)*modeOuter w j=
      (z-eigenvalue w j) • modeOuter w j := by
  rw [Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,modeOuter_path,sub_smul]

theorem shifted_mul_spectralInverse (w : ℕ) (z : ℝ)
    (hz : ∀ j : Fin w,z≠eigenvalue w j) :
    (z • (1 : Matrix (Fin w) (Fin w) ℝ)-pathOperator w)*spectralInverse w z=1 := by
  rw [spectralInverse,Matrix.mul_smul,Finset.mul_sum]
  simp_rw [Matrix.mul_smul,shifted_modeOuter,smul_smul]
  have hcj (j : Fin w) : (z-eigenvalue w j)⁻¹*(z-eigenvalue w j)=1 :=
    inv_mul_cancel₀ (sub_ne_zero.mpr (hz j))
  simp_rw [hcj,one_smul]
  rw [modeOuter_sum,smul_smul]
  have hc : (2/((w : ℝ)+1))*(((w : ℝ)+1)/2)=1 := by field_simp
  rw [hc,one_smul]

theorem resolvent_inverse_eq (w : ℕ) (z : ℝ) (hz : ∀ j : Fin w,z≠eigenvalue w j) :
    (z • (1 : Matrix (Fin w) (Fin w) ℝ)-pathOperator w)⁻¹=spectralInverse w z :=
  Matrix.inv_eq_right_inv (shifted_mul_spectralInverse w z hz)

theorem green_modeOuter {R : ℕ} (hR : 0<R) (w : ℕ) (j : Fin w) :
    boundaryGreen hR w*modeOuter w j=
      (continuant (eigenvalue w j) (R-1)/continuant (eigenvalue w j) R) • modeOuter w j := by
  ext a b
  change (∑ x : Fin w,boundaryGreen hR w a x*(mode w j x*mode w j b))=_
  have h := congrFun (boundaryGreen_mode hR w j) a
  change (∑ x : Fin w,boundaryGreen hR w a x*mode w j x)=
    (continuant (eigenvalue w j) (R-1)/continuant (eigenvalue w j) R)*mode w j a at h
  simp only [← mul_assoc,← Finset.sum_mul,h,Matrix.smul_apply,smul_eq_mul,modeOuter]

theorem scalar_resolvent_residues {R w : ℕ} (hR : 0<R) (hw : 0<w) (z : ℝ)
    (hz : ∀ j : Fin w,z≠eigenvalue w j) :
    (boundaryGreen hR w*(z • (1 : Matrix (Fin w) (Fin w) ℝ)-pathOperator w)⁻¹)
        ⟨0,hw⟩ ⟨0,hw⟩=∑ j : Fin w,residue R w j/(z-eigenvalue w j) := by
  rw [resolvent_inverse_eq w z hz,spectralInverse,Matrix.mul_smul,Finset.mul_sum]
  simp_rw [Matrix.mul_smul,green_modeOuter,smul_smul]
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [modeOuter,mode,Fin.val_mk,Nat.cast_zero,zero_add,mul_one,residue]
  ring

/-- The exact manuscript rational q/P has the stated positive spectral
residues at the explicit path eigenvalues. -/
theorem rational_scalar_residues {R w : ℕ} (hR : 0<R) (hw : 0<w) (z : ℝ)
    (hz : ∀ j : Fin w,z≠eigenvalue w j) :
    (rationalScalarNumerator hR hw).eval₂ (algebraMap ℚ ℝ) z/
      (rationalPathPolynomial w).eval₂ (algebraMap ℚ ℝ) z=
        ∑ j : Fin w,residue R w j/(z-eigenvalue w j) := by
  rw [← boundaryGreen_rational_scalar_resolvent hR hw]
  exact scalar_resolvent_residues hR hw z hz

theorem pathPolynomial_eigenvalue (w : ℕ) (j : Fin w) :
    (pathPolynomial w).eval (eigenvalue w j)=0 := by
  have hw : 0<w := by have h := j.isLt; omega
  have hm : (eigenvalue w j • (1 : Matrix (Fin w) (Fin w) ℝ)-pathOperator w)*ᵥ mode w j=0 := by
    rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,mode_mulVec,sub_self]
  by_contra hne
  have hd : (eigenvalue w j • (1 : Matrix (Fin w) (Fin w) ℝ)-pathOperator w).det≠0 := by
    rwa [shifted_pathOperator_det,← pathPolynomial_eval]
  have hz := Matrix.eq_zero_of_mulVec_eq_zero hd hm
  have hv := congrFun hz ⟨0,hw⟩
  have hp := Real.sin_pos_of_pos_of_lt_pi (angle_pos w j) (angle_lt_pi w j)
  simp only [mode,Fin.val_mk,Nat.cast_zero,zero_add,mul_one,Pi.zero_apply] at hv
  linarith

theorem pathPolynomial_factorization (w : ℕ) :
    pathPolynomial w=∏ j : Fin w,(X-C (eigenvalue w j)) := by
  have hmon : (∏ j : Fin w,(X-C (eigenvalue w j))).Monic := monic_prod_X_sub_C _ _
  have hdvd : (∏ j : Fin w,(X-C (eigenvalue w j)))∣pathPolynomial w :=
    Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C (eigenvalue_injective w))
      (fun j => (dvd_iff_isRoot).mpr (pathPolynomial_eigenvalue w j))
  apply eq_of_monic_of_dvd_of_natDegree_le hmon (pathPolynomial_monic w) hdvd
  simp only [pathPolynomial_natDegree,natDegree_finsetProd_X_sub_C_eq_card,Finset.card_univ,Fintype.card_fin,le_refl]

theorem pathPolynomial_eval_ne_zero_iff (w : ℕ) (z : ℝ) :
    (pathPolynomial w).eval z≠0 ↔ ∀ j : Fin w,z≠eigenvalue w j := by
  rw [pathPolynomial_factorization]
  simp only [Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,
    Finset.prod_ne_zero_iff,Finset.mem_univ,true_implies,sub_ne_zero]

end
end SpanningTreeIsoperimetry.ScalarSpectralResidues
