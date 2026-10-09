import SpanningTreeIsoperimetry.StripFourierDecay
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Finite Hankel traces and the actual quadratic Fourier constant.
This establishes the trace limit needed by a determinant-limit argument;
it does not assert that the strip determinant has that limit. -/
namespace SpanningTreeIsoperimetry.StripHankelTrace
open StripFourierCoefficients StripFourierDecay Filter
open scoped Topology BigOperators
noncomputable section

def pairSquare (p : ℕ×ℕ) : ℝ := coefficient (p.1+p.2+1)^2

theorem antidiagonal_sum (n : ℕ) :
    (∑ p∈Finset.antidiagonal n,pairSquare p)=((n+1 : ℕ) : ℝ)*coefficient (n+1)^2 := by
  have he : (∑ p∈Finset.antidiagonal n,pairSquare p)=
      ∑ _p∈Finset.antidiagonal n,coefficient (n+1)^2 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [pairSquare,Finset.mem_antidiagonal.mp hp]
  rw [he,Finset.sum_const,Finset.Nat.card_antidiagonal,nsmul_eq_mul]

theorem pairSquare_summable : Summable pairSquare := by
  have hs : Summable (fun p : Σ n : ℕ, Finset.antidiagonal n => pairSquare p.2.val) := by
    apply (summable_sigma_of_nonneg (f := fun p : Σ n : ℕ, Finset.antidiagonal n => pairSquare p.2.val)
      (fun p => sq_nonneg (coefficient (p.2.val.1+p.2.val.2+1)))).mpr
    constructor
    · intro n
      exact (hasSum_fintype _).summable
    · simpa only [tsum_fintype,Finset.sum_coe_sort,antidiagonal_sum] using weighted_square_summable
  exact Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mp hs

theorem pairSquare_tsum : (∑' p : ℕ×ℕ,pairSquare p)=
    ∑' n : ℕ,((n+1 : ℕ) : ℝ)*coefficient (n+1)^2 := by
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq pairSquare]
  have hs := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr pairSquare_summable
  change (∑' p : Σ n : ℕ,Finset.antidiagonal n,pairSquare p.2.val)=_
  have hs' : Summable (fun p : Σ n : ℕ,Finset.antidiagonal n => pairSquare p.2.val) := hs
  rw [hs'.tsum_sigma' (fun n => (hasSum_fintype _).summable)]
  simp only [tsum_fintype,Finset.sum_coe_sort,antidiagonal_sum]

def hankel (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => coefficient (i.val+j.val+1)

def truncate (n : ℕ) (p : ℕ×ℕ) : ℝ := if p.1<n ∧ p.2<n then pairSquare p else 0

theorem truncate_tendsto (p : ℕ×ℕ) : Tendsto (fun n => truncate n p) atTop (𝓝 (pairSquare p)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (max p.1 p.2+1)] with n hn
  simp only [truncate,if_pos (show p.1<n ∧ p.2<n by omega)]

theorem tsum_truncate_eq_trace (n : ℕ) : (∑' p : ℕ×ℕ,truncate n p)=Matrix.trace (hankel n*hankel n) := by
  rw [tsum_eq_sum (s := Finset.range n ×ˢ Finset.range n)]
  · rw [Finset.sum_product]
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
    simp_rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp [truncate,pairSquare,hankel,i.is_lt,j.is_lt,pow_two,Nat.add_comm] <;> ring
  · intro p hp
    simp only [Finset.mem_product,Finset.mem_range] at hp
    simp only [truncate,if_neg hp]

theorem hankel_trace_tendsto : Tendsto (fun n => Matrix.trace (hankel n*hankel n)) atTop
    (𝓝 (∑' n : ℕ,((n+1 : ℕ) : ℝ)*coefficient (n+1)^2)) := by
  have ht := tendsto_tsum_of_dominated_convergence pairSquare_summable
    (f := truncate) (g := pairSquare) truncate_tendsto
    (Filter.Eventually.of_forall (fun n p => by
      unfold truncate
      split_ifs
      · simpa only [Real.norm_eq_abs,abs_of_nonneg (show 0≤pairSquare p from sq_nonneg _)] using (le_refl (pairSquare p))
      · simpa only [norm_zero] using (show 0≤pairSquare p from sq_nonneg _)))
  simpa only [tsum_truncate_eq_trace,pairSquare_tsum] using ht

end
end SpanningTreeIsoperimetry.StripHankelTrace
