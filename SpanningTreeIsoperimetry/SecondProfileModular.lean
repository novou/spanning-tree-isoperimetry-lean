module

public import SpanningTreeIsoperimetry.RectangularSecondProfile
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

@[expose] public section

/-! Exact reciprocal symmetry of the genuine second rectangular profile,
from the locally available weight-four Eisenstein series theorem. -/
namespace SpanningTreeIsoperimetry.SecondProfileModular
open RectangularSecondProfile CongruenceSubgroup
open scoped MatrixGroups
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def imaginaryAxis {u : ℝ} (hu : 0<u) : UpperHalfPlane :=
  ⟨(u : ℂ)*Complex.I,by simpa using hu⟩

theorem imaginaryAxis_q {u : ℝ} (hu : 0<u) :
    Complex.exp (2*(Real.pi : ℂ)*Complex.I*(imaginaryAxis hu : ℂ))=
      (Real.exp (-2*Real.pi*u) : ℂ) := by
  have he : 2*(Real.pi : ℂ)*Complex.I*(imaginaryAxis hu : ℂ)=((-2*Real.pi*u : ℝ) : ℂ) := by
    change 2*(Real.pi : ℂ)*Complex.I*((u : ℂ)*Complex.I)=_
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [he,← Complex.ofReal_exp]

theorem E4_imaginaryAxis {u : ℝ} (hu : 0<u) :
    ModularForm.E₄ (imaginaryAxis hu)=((1+240*boseCubic u : ℝ) : ℂ) := by
  have hbern : bernoulli 4=(-1/30 : ℚ) := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : 4≠1),bernoulli'_four]
  have h := EisensteinSeries.q_expansion_bernoulli (k := 4) (by decide) (by decide) (imaginaryAxis hu)
  norm_num [hbern] at h
  have hs : (∑' n : ℕ+, (ArithmeticFunction.sigma 3 n : ℂ)*
      Complex.exp (2*(Real.pi : ℂ)*Complex.I*(imaginaryAxis hu : ℂ))^(n : ℕ))=
        (boseCubic u : ℂ) := by
    rw [boseCubic_eq_divisor_series hu,Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rw [imaginaryAxis_q hu]
    simp
  rw [hs] at h
  simpa using h

theorem S_imaginaryAxis {u : ℝ} (hu : 0<u) :
    ModularGroup.S • imaginaryAxis hu=imaginaryAxis (inv_pos.mpr hu) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul]
  change (-((u : ℂ)*Complex.I))⁻¹=((u⁻¹ : ℝ) : ℂ)*Complex.I
  simp [inv_neg,mul_inv_rev,Complex.inv_I,mul_comm]

theorem E4_reciprocal {u : ℝ} (hu : 0<u) :
    1+240*boseCubic (u⁻¹)=u^4*(1+240*boseCubic u) := by
  letI : SlashInvariantFormClass (ModularForm 𝒮ℒ 4) (Gamma 1) 4 := by
    rw [Gamma_one_coe_eq_SL]
    infer_instance
  have h := SlashInvariantForm.slash_action_eqn_SL'' ModularForm.E₄
    (mem_Gamma_one ModularGroup.S) (imaginaryAxis hu)
  rw [S_imaginaryAxis hu,ModularGroup.denom_S,E4_imaginaryAxis (inv_pos.mpr hu),E4_imaginaryAxis hu] at h
  have hp : (imaginaryAxis hu : ℂ)^(4 : ℤ)=((u^4 : ℝ) : ℂ) := by
    change ((u : ℂ)*Complex.I)^(4 : ℤ)=_
    norm_num [mul_pow,show Complex.I^4=1 by norm_num [pow_succ,Complex.I_sq]]
  rw [hp] at h
  exact_mod_cast h

theorem K2_inv {u : ℝ} (hu : 0<u) : K2 (u⁻¹)=K2 u := by
  unfold K2
  rw [E4_reciprocal hu]
  field_simp [hu.ne']
  ring

end
end SpanningTreeIsoperimetry.SecondProfileModular
