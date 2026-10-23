module

public import SpanningTreeIsoperimetry.PotentialKernelIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! Normalization and harmonic recurrences for the actual integral-defined
full-plane potential. The double-integral singularity is removed only on a
proved null set; no Green-image or diagonal-evaluation identity is assumed. -/
namespace SpanningTreeIsoperimetry.PotentialKernelHarmonic
open PotentialKernelIntegral Set MeasureTheory
open scoped ENNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem denominator_zero_iff {p : ℝ × ℝ} (hp : p∈frequencySquare) :
    denominator p.1 p.2=0 ↔ p=(0,0) := by
  constructor
  · intro h
    have hx : Real.cos p.1=1 := by
      unfold denominator at h
      linarith [Real.cos_le_one p.1,Real.cos_le_one p.2]
    have hy : Real.cos p.2=1 := by
      unfold denominator at h
      linarith [Real.cos_le_one p.1,Real.cos_le_one p.2]
    have hxp : p.1=0 := (Real.cos_eq_one_iff_of_lt_of_lt
      (by have h0:=hp.1.1; nlinarith [Real.pi_pos])
      (by have h1:=hp.1.2; nlinarith [Real.pi_pos])).mp hx
    have hyp : p.2=0 := (Real.cos_eq_one_iff_of_lt_of_lt
      (by have h0:=hp.2.1; nlinarith [Real.pi_pos])
      (by have h1:=hp.2.2; nlinarith [Real.pi_pos])).mp hy
    exact Prod.ext hxp hyp
  · rintro rfl
    norm_num [denominator]

theorem denominator_ne_zero_ae :
    ∀ᵐ p : ℝ × ℝ ∂volume.restrict frequencySquare,denominator p.1 p.2≠0 := by
  have hmem : ∀ᵐ p : ℝ × ℝ ∂volume.restrict frequencySquare,p∈frequencySquare :=
    ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  letI : NullSingletonClass (volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  filter_upwards [hmem,ae_restrict_of_ae (volume.ae_ne ((0,0) : ℝ × ℝ))] with p hp hne
  exact fun h => hne ((denominator_zero_iff hp).mp h)

theorem cosine_integral (m : ℕ) :
    (∫ θ in Icc (0 : ℝ) Real.pi,Real.cos ((m : ℝ)*θ))=if m=0 then Real.pi else 0 := by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le Real.pi_pos.le]
  by_cases hm : m=0
  · subst m
    simp
  · have hm0 : (m : ℝ)≠0 := by exact_mod_cast hm
    rw [if_neg hm,intervalIntegral.integral_comp_mul_left _ hm0,integral_cos]
    simp only [mul_zero,Real.sin_zero,Real.sin_nat_mul_pi,sub_zero,smul_zero]

theorem cosine_product_integral (m n : ℕ) :
    (∫ p in frequencySquare,Real.cos ((m : ℝ)*p.1)*Real.cos ((n : ℝ)*p.2))=
      (if m=0 then Real.pi else 0)*(if n=0 then Real.pi else 0) := by
  have h := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun θ : ℝ => Real.cos ((m : ℝ)*θ)) (fun φ : ℝ => Real.cos ((n : ℝ)*φ))
    (Icc (0 : ℝ) Real.pi) (Icc (0 : ℝ) Real.pi)
  simpa only [frequencySquare,Measure.volume_eq_prod,cosine_integral] using h

/-- Reflection of a negative nearest neighbour to the nonnegative axis. -/
def previous (m : ℕ) : ℕ := if m=0 then 1 else m-1

theorem cosine_neighbors (m : ℕ) (θ : ℝ) :
    Real.cos (((m+1 : ℕ) : ℝ)*θ)+Real.cos ((previous m : ℝ)*θ)=
      2*Real.cos ((m : ℝ)*θ)*Real.cos θ := by
  by_cases hm : m=0
  · subst m
    simp [previous] <;> ring
  · have hm1 : 1≤m := by omega
    rw [previous,if_neg hm,Nat.cast_add,Nat.cast_one,Nat.cast_sub hm1,Nat.cast_one,
      add_mul,sub_mul,one_mul,Real.cos_add,Real.cos_sub]
    ring

/-- The pointwise Poisson identity off the single null singularity. -/
theorem density_poisson (m n : ℕ) (θ φ : ℝ) (hd : denominator θ φ≠0) :
    density (m+1) n θ φ+density (previous m) n θ φ+
      density m (n+1) θ φ+density m (previous n) θ φ-4*density m n θ φ=
        4*Real.cos ((m : ℝ)*θ)*Real.cos ((n : ℝ)*φ) := by
  have hx := congrArg (fun t : ℝ => t*Real.cos ((n : ℝ)*φ)) (cosine_neighbors m θ)
  have hy := congrArg (fun t : ℝ => Real.cos ((m : ℝ)*θ)*t) (cosine_neighbors n φ)
  unfold density
  field_simp [hd]
  unfold denominator
  simp only [mul_comm] at hx hy ⊢
  nlinarith only [hx,hy]

theorem density_poisson_ae (m n : ℕ) :
    (fun p : ℝ × ℝ => density (m+1) n p.1 p.2+density (previous m) n p.1 p.2+
      density m (n+1) p.1 p.2+density m (previous n) p.1 p.2-4*density m n p.1 p.2)
      =ᵐ[volume.restrict frequencySquare]
    (fun p => 4*Real.cos ((m : ℝ)*p.1)*Real.cos ((n : ℝ)*p.2)) := by
  filter_upwards [denominator_ne_zero_ae] with p hp
  exact density_poisson m n p.1 p.2 hp

/-- Integrated Poisson equation, including the unit source at the origin.
The sign convention is neighbour sum minus four times the central value. -/
theorem potential_poisson (m n : ℕ) :
    potential (m+1) n+potential (previous m) n+potential m (n+1)+potential m (previous n)-
      4*potential m n=if m=0 ∧ n=0 then 4 else 0 := by
  have h := integral_congr_ae (density_poisson_ae m n)
  have h1 := density_integrable (m+1) n
  have h2 := density_integrable (previous m) n
  have h3 := density_integrable m (n+1)
  have h4 := density_integrable m (previous n)
  have h0 := density_integrable m n
  have h12 : Integrable (fun p : ℝ × ℝ => density (m+1) n p.1 p.2+
      density (previous m) n p.1 p.2) (volume.restrict frequencySquare) := h1.add h2
  have h123 : Integrable (fun p : ℝ × ℝ => density (m+1) n p.1 p.2+
      density (previous m) n p.1 p.2+density m (n+1) p.1 p.2)
      (volume.restrict frequencySquare) := h12.add h3
  have h1234 : Integrable (fun p : ℝ × ℝ => density (m+1) n p.1 p.2+
      density (previous m) n p.1 p.2+density m (n+1) p.1 p.2+density m (previous n) p.1 p.2)
      (volume.restrict frequencySquare) := h123.add h4
  rw [integral_sub h1234 (h0.const_mul 4),integral_add h123 h4,
    integral_add h12 h3,integral_add h1 h2,integral_const_mul] at h
  have hr : (∫ p in frequencySquare,4*Real.cos ((m : ℝ)*p.1)*Real.cos ((n : ℝ)*p.2))=
      4*((if m=0 then Real.pi else 0)*(if n=0 then Real.pi else 0)) := by
    simp_rw [mul_assoc]
    rw [integral_const_mul,cosine_product_integral]
  rw [hr] at h
  unfold potential
  by_cases hm : m=0 <;> by_cases hn : n=0
  all_goals
    simp [hm,hn] at h ⊢
    field_simp [Real.pi_ne_zero]
    try simp only [Nat.add_comm] at h ⊢
    nlinarith only [h]

theorem potential_one_zero : potential 1 0=1 := by
  have h := potential_poisson 0 0
  norm_num [previous,potential_zero] at h
  simp_rw [potential_swap 0 1] at h
  linarith

theorem potential_zero_one : potential 0 1=1 := by rw [potential_swap,potential_one_zero]

theorem potential_harmonic {m n : ℕ} (hmn : m≠0 ∨ n≠0) :
    potential (m+1) n+potential (previous m) n+potential m (n+1)+potential m (previous n)=
      4*potential m n := by
  have h := potential_poisson m n
  have hn : ¬(m=0 ∧ n=0) := by tauto
  rw [if_neg hn] at h
  linarith

/-- The arbitrary interior harmonic recurrence from Appendix B. -/
theorem interior_recurrence {m n : ℕ} (hm : 1≤m) (hn : 1≤n) :
    potential (m+1) n=4*potential m n-potential (m-1) n-
      potential m (n+1)-potential m (n-1) := by
  have h := potential_harmonic (m := m) (n := n) (Or.inl (by omega))
  simp only [previous,if_neg (show m≠0 by omega),if_neg (show n≠0 by omega)] at h
  linarith

/-- The axis recurrence, with the two vertical neighbours identified by
reflection symmetry in the integral representation. -/
theorem axis_recurrence {m : ℕ} (hm : 1≤m) :
    potential (m+1) 0=4*potential m 0-potential (m-1) 0-2*potential m 1 := by
  have h := potential_harmonic (m := m) (n := 0) (Or.inl (by omega))
  simp only [previous,if_neg (show m≠0 by omega),ite_true,zero_add] at h
  linarith

/-- The adjacent-diagonal recurrence, using interchange of coordinates. -/
theorem diagonal_adjacent_recurrence {n : ℕ} (hn : 1≤n) :
    potential (n+1) n=2*potential n n-potential n (n-1) := by
  have h := potential_harmonic (m := n) (n := n) (Or.inl (by omega))
  simp only [previous,if_neg (show n≠0 by omega)] at h
  rw [potential_swap (n-1) n,potential_swap n (n+1)] at h
  linarith

end
end SpanningTreeIsoperimetry.PotentialKernelHarmonic
