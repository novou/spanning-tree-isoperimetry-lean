module

public import SpanningTreeIsoperimetry.BoundaryGreen
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Tactic.ComputeDegree

@[expose] public section

namespace SpanningTreeIsoperimetry.BoundaryGreen
open scoped BigOperators Topology
open Filter Polynomial
noncomputable section

def numeratorSix (j : Fin 6) : Polynomial ℝ :=
  ![C (-1),
    C (1/2) + C (3/2) * X^1 + C 1 * X^2,
    C 4 + C (91/6) * X^1 + C (223/12) * X^2 + C (28/3) * X^3 + C (5/3) * X^4,
    C 144 + C (5115/8) * X^1 + C (4151/4) * X^2 + C (19823/24) * X^3 + C (4169/12) * X^4 + C (445/6) * X^5 + C (19/3) * X^6,
    C 9792 + C (967311/20) * X^1 + C (1486011/16) * X^2 + C (11289547/120) * X^3 + C (13446389/240) * X^4 + C (609391/30) * X^5 + C (26471/6) * X^6 + C (7916/15) * X^7 + C (401/15) * X^8,
    C 1094400 + C (93492525/16) * X^1 + C (402751631/32) * X^2 + C (2381199003/160) * X^3 + C (348227363/32) * X^4 + C (831186551/160) * X^5 + C (132105473/80) * X^6 + C (6938239/20) * X^7 + C 46281 * X^8 + C (35519/10) * X^9 + C (597/5) * X^10] j

def denominatorSix (j : Fin 6) : Polynomial ℝ :=
  ∏ l ∈ Finset.range j.val, (X + C (l + 1 : ℝ))^2

def limitSix (j : Fin 6) : ℝ := ![-1,1,5/3,19/3,401/15,597/5] j

def initialSix (j : Fin 6) : ℝ := ![-1,1/2,1,4,17,76] j

def telescoperSix (j : Fin 6) (m : ℕ) : ℝ :=
  (numeratorSix j).eval (m : ℝ) / (denominatorSix j).eval (m : ℝ)

def boundaryCoefficientSix (j : Fin 6) (m : ℕ) : ℝ :=
  wallisReciprocal m * (∏ l ∈ Finset.range j.val, (2*(m : ℝ)+l+1)^2) *
    (2*m+j.val+1) /
    ((∏ l ∈ Finset.range j.val, ((m : ℝ)+l+1)^2) *
      (2*m+1) * 4^(j.val+1) * (m+1) * (m+j.val+1))

theorem boundaryCoefficientSix_nonneg (j : Fin 6) (m : ℕ) :
    0 ≤ boundaryCoefficientSix j m := by
  unfold boundaryCoefficientSix
  have hb := (wallisReciprocal_pos m).le
  positivity

theorem numeratorSix_degree (j : Fin 6) : (numeratorSix j).degree = (2*j.val : ℕ) := by
  fin_cases j <;> norm_num [numeratorSix] <;> compute_degree!

theorem denominatorSix_degree (j : Fin 6) : (denominatorSix j).degree = (2*j.val : ℕ) := by
  fin_cases j <;> simp only [denominatorSix, Finset.prod_range_succ, Finset.prod_range_zero] <;>
    compute_degree!

theorem numeratorSix_leadingCoeff (j : Fin 6) : (numeratorSix j).leadingCoeff = limitSix j := by
  rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some (numeratorSix_degree j)]
  fin_cases j <;> norm_num [numeratorSix, limitSix] <;> compute_degree!

theorem denominatorSix_leadingCoeff (j : Fin 6) : (denominatorSix j).leadingCoeff = 1 := by
  unfold denominatorSix
  exact monic_prod_of_monic _ _ (fun l _ => (monic_X_add_C (l+1 : ℝ)).pow 2)

theorem telescoperSix_tendsto (j : Fin 6) : Tendsto (telescoperSix j) atTop (𝓝 (limitSix j)) := by
  have hd : (numeratorSix j).degree = (denominatorSix j).degree := by
    rw [numeratorSix_degree, denominatorSix_degree]
  have h := (Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq
    (numeratorSix j) (denominatorSix j) hd).comp tendsto_natCast_atTop_atTop
  change Tendsto (fun m : ℕ => (numeratorSix j).eval (m : ℝ) /
    (denominatorSix j).eval (m : ℝ)) atTop (𝓝 (limitSix j))
  simpa only [Function.comp_def, numeratorSix_leadingCoeff, denominatorSix_leadingCoeff, div_one] using h

theorem telescoperSix_initial (j : Fin 6) : telescoperSix j 0 = initialSix j := by
  fin_cases j <;> norm_num [telescoperSix, numeratorSix, denominatorSix, initialSix,
    Finset.prod_range_succ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow]

set_option maxHeartbeats 800000 in
theorem boundaryCoefficientSix_telescope (j : Fin 6) (m : ℕ) :
    boundaryCoefficientSix j m = wallisReciprocal (m+1)*telescoperSix j (m+1) -
      wallisReciprocal m*telescoperSix j m := by
  rw [wallisReciprocal_succ]
  have hm (k : ℕ) : (m : ℝ) + k + 1 ≠ 0 := by positivity
  fin_cases j <;>
    norm_num [boundaryCoefficientSix, telescoperSix, numeratorSix, denominatorSix,
      Finset.prod_range_succ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow] <;>
    field_simp <;> ring

theorem boundaryCoefficientSix_hasSum (j : Fin 6) :
    HasSum (boundaryCoefficientSix j) (2 / Real.pi * limitSix j - initialSix j) := by
  have h := hasSum_of_wallis_telescope (boundaryCoefficientSix j) (telescoperSix j) (limitSix j)
    (boundaryCoefficientSix_nonneg j) (boundaryCoefficientSix_telescope j) (telescoperSix_tendsto j)
  simpa only [telescoperSix_initial] using h

end
end SpanningTreeIsoperimetry.BoundaryGreen
