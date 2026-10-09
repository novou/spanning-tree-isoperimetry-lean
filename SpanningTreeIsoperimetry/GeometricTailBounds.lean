import SpanningTreeIsoperimetry.RectangleResidualBounds

/-! Exact higher polynomial/geometric tail bounds for rectangular remainders. -/
namespace SpanningTreeIsoperimetry.GeometricTailBounds

open CoupledRectangleError RectangleResidualBounds
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

/-- For sufficiently fast geometric decay, every polynomially weighted term
decreases from the first positive integer onward. -/
theorem pow_mul_geometric_antitone (p : ℕ) {q : ℝ} (hq0 : 0≤q) (hq : 2^p*q≤1) :
    AntitoneOn (fun n : ℕ => (n : ℝ)^p*q^n) (Set.Ici 1) := by
  intro m hm n hn hmn
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih =>
    have hn1 : 1≤n := le_trans hm hmn
    have hnR : (1 : ℝ)≤n := by exact_mod_cast hn1
    have hp : ((n : ℝ)+1)^p≤2^p*(n : ℝ)^p := by
      calc
        _≤(2*(n : ℝ))^p := by gcongr; linarith
        _=_ := mul_pow _ _ _
    have hstep : q*((n : ℝ)+1)^p≤(n : ℝ)^p := by
      calc
        _≤q*(2^p*(n : ℝ)^p) := mul_le_mul_of_nonneg_left hp hq0
        _=(2^p*q)*(n : ℝ)^p := by ring
        _≤1*(n : ℝ)^p := mul_le_mul_of_nonneg_right hq (pow_nonneg (Nat.cast_nonneg n) p)
        _=(n : ℝ)^p := one_mul _
    calc
      ((n+1 : ℕ) : ℝ)^p*q^(n+1)=q^n*(q*((n : ℝ)+1)^p) := by push_cast; ring
      _≤q^n*(n : ℝ)^p := mul_le_mul_of_nonneg_left hstep (pow_nonneg hq0 n)
      _=(n : ℝ)^p*q^n := by ring
      _≤_ := ih hn1

def cubicTail (q : ℝ) (r : ℕ) : ℝ := ∑' n : ℕ, ((r+n : ℕ) : ℝ)^3*q^(r+n)

theorem cubicTail_hasSum {q : ℝ} (hq : |q|<1) (r : ℕ) :
    HasSum (fun n : ℕ => ((r+n : ℕ) : ℝ)^3*q^(r+n))
      (q^r*((r : ℝ)^3/(1-q)+3*(r : ℝ)^2*moment1 q+3*r*moment2 q+moment3 q)) := by
  have h0 := hasSum_geometric_of_abs_lt_one hq
  have h1 := (geometricMoment_summable 1 hq).hasSum
  have h2 := (geometricMoment_summable 2 hq).hasSum
  have h3 := (geometricMoment_summable 3 hq).hasSum
  rw [← geometricMoment,geometricMoment_one hq] at h1
  rw [← geometricMoment,geometricMoment_two hq] at h2
  rw [← geometricMoment,geometricMoment_three hq] at h3
  have h := (((h0.mul_left ((r : ℝ)^3)).add (h1.mul_left (3*(r : ℝ)^2))).add
    (h2.mul_left (3*(r : ℝ)))).add h3
  have hh := h.mul_left (q^r)
  convert hh using 1
  · funext n
    simp only [Pi.add_apply,Pi.mul_apply,Nat.cast_add,pow_add,pow_one]
    ring
  · ring

theorem cubicTail_eq {q : ℝ} (hq : |q|<1) (r : ℕ) :
    cubicTail q r=q^r*((r : ℝ)^3/(1-q)+3*(r : ℝ)^2*moment1 q+3*r*moment2 q+moment3 q) :=
  (cubicTail_hasSum hq r).tsum_eq

def tailAllowance (r : ℕ) : ℝ :=
  (r : ℝ)^4*(1/33)^r/(2*(1-(1/33)^r))+
    (r : ℝ)^4*(1/500)^r/(1-1/500)^2+
    ((22/7)^3/6)*(r : ℝ)^5*(1/500)^r*
      (1/(1-1/500)+3*moment1 (1/500)+3*moment2 (1/500)+moment3 (1/500))/(1-1/500)

/-- Exact constants for the omitted modes and endpoint, after polynomial decay. -/
theorem tailAllowance_four_lt : tailAllowance 4<1/1000 := by
  norm_num [tailAllowance,moment1,moment2,moment3]

theorem tailAllowance_three_lt : tailAllowance 3<1/500 := by
  norm_num [tailAllowance,moment1,moment2,moment3]

end
end SpanningTreeIsoperimetry.GeometricTailBounds
