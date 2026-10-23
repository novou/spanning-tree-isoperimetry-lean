module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! The log-determinant tangent inequality for actual positive definite matrices.
No comparison in the Loewner order is required. -/
namespace SpanningTreeIsoperimetry.LogDetTangent
open scoped BigOperators Matrix
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem log_det_le_trace_sub_card {A : Matrix n n ℝ} (hA : A.PosDef) :
    Real.log A.det ≤ A.trace - Fintype.card n := by
  have hd : A.det=∏ i, hA.1.eigenvalues i := by simpa using hA.1.det_eq_prod_eigenvalues
  have ht : A.trace=∑ i, hA.1.eigenvalues i := by simpa using hA.1.trace_eq_sum_eigenvalues
  rw [hd, Real.log_prod (fun i _ => (hA.eigenvalues_pos i).ne'), ht]
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => Real.log_le_sub_one_of_pos (hA.eigenvalues_pos i))
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] using hs

theorem exists_whitening {H : Matrix n n ℝ} (hH : H.PosDef) :
    ∃ K : Matrix n n ℝ, IsUnit K ∧ K * H * Kᴴ = 1 := by
  let U := hH.1.eigenvectorUnitary
  let D : Matrix n n ℝ := diagonal hH.1.eigenvalues
  let S : Matrix n n ℝ := diagonal (fun i => (Real.sqrt (hH.1.eigenvalues i))⁻¹)
  have hS : Sᴴ = S := by simp [S]
  have hspec : H = (U : Matrix n n ℝ) * D * (U : Matrix n n ℝ)ᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Function.comp_def, RCLike.ofReal_real_eq_id,
      id_eq, star_eq_conjTranspose] using hH.1.spectral_theorem
  have hdiag : S * D * S = 1 := by
    dsimp only [S, D]
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    ext i j
    by_cases hij : i=j
    · subst j
      simp only [diagonal_apply_eq, one_apply_eq]
      have hp := hH.eigenvalues_pos i
      have hs := Real.sq_sqrt hp.le
      have hn := (Real.sqrt_pos.2 hp).ne'
      field_simp
      nlinarith
    · simp [hij]
  let K : Matrix n n ℝ := S * (U : Matrix n n ℝ)ᴴ
  have hwhite : K * H * Kᴴ = 1 := by
    have hu : (U : Matrix n n ℝ)ᴴ * (U : Matrix n n ℝ) = 1 :=
      Unitary.coe_star_mul_self U
    calc
      K * H * Kᴴ = S * ((U : Matrix n n ℝ)ᴴ * (U : Matrix n n ℝ)) * D *
          ((U : Matrix n n ℝ)ᴴ * (U : Matrix n n ℝ)) * S := by
        rw [hspec]
        dsimp only [K]
        rw [conjTranspose_mul, conjTranspose_conjTranspose, hS]
        noncomm_ring
      _ = 1 := by rw [hu, mul_one, mul_one, hdiag]
  have hdet := congrArg Matrix.det hwhite
  rw [det_mul, det_mul, det_conjTranspose, star_trivial, det_one] at hdet
  have hk : K.det ≠ 0 := by intro hz; rw [hz, zero_mul, zero_mul] at hdet; norm_num at hdet
  exact ⟨K, (Matrix.isUnit_iff_isUnit_det K).mpr (isUnit_iff_ne_zero.mpr hk), hwhite⟩

theorem log_det_tangent {H G : Matrix n n ℝ} (hH : H.PosDef) (hG : G.PosDef) :
    Real.log G.det - Real.log H.det ≤ Matrix.trace (H⁻¹ * (G-H)) := by
  obtain ⟨K,hK,hwhite⟩ := exists_whitening hH
  have hk : IsUnit K.det := (Matrix.isUnit_iff_isUnit_det K).mp hK
  have hki := Matrix.nonsing_inv_mul K hk
  have hinv : H⁻¹ = Kᴴ * K := by
    apply Matrix.inv_eq_right_inv
    calc
      H * (Kᴴ * K) = K⁻¹ * (K * H * Kᴴ) * K := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hki, one_mul]
      _ = 1 := by rw [hwhite, mul_one, hki]
  have hX : (K * G * Kᴴ).PosDef :=
    (Matrix.IsUnit.posDef_star_right_conjugate_iff hK).mpr hG
  have hlogH := congrArg Real.log (congrArg Matrix.det hwhite)
  have hlogG : Real.log (K * G * Kᴴ).det =
      Real.log K.det + Real.log G.det + Real.log K.det := by
    rw [det_mul, det_mul, det_conjTranspose, star_trivial,
      Real.log_mul (mul_ne_zero (isUnit_iff_ne_zero.mp hk) hG.det_pos.ne')
        (isUnit_iff_ne_zero.mp hk),
      Real.log_mul (isUnit_iff_ne_zero.mp hk) hG.det_pos.ne']
  rw [det_mul, det_mul, det_conjTranspose, star_trivial,
    Real.log_mul (mul_ne_zero (isUnit_iff_ne_zero.mp hk) hH.det_pos.ne')
      (isUnit_iff_ne_zero.mp hk),
    Real.log_mul (isUnit_iff_ne_zero.mp hk) hH.det_pos.ne', det_one, Real.log_one] at hlogH
  have htrace : Matrix.trace (H⁻¹ * (G-H)) =
      Matrix.trace (K * G * Kᴴ) - Fintype.card n := by
    rw [Matrix.mul_sub, Matrix.trace_sub,
      Matrix.nonsing_inv_mul H (isUnit_iff_ne_zero.mpr hH.det_pos.ne'), trace_one, hinv]
    rw [Matrix.trace_mul_cycle K G Kᴴ]
  rw [htrace]
  have hb := log_det_le_trace_sub_card hX
  rw [hlogG] at hb
  linarith

end
end SpanningTreeIsoperimetry.LogDetTangent
