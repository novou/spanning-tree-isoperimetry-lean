import SpanningTreeIsoperimetry.ScalarSpectralResidues
import SpanningTreeIsoperimetry.PositiveResidueInterlacing

/-! Strict zero interlacing for the actual rational q/P of Section 7,
separate from the previously closed signed-Euclidean product proof. -/
namespace SpanningTreeIsoperimetry.ScalarSpectralInterlacing
open ScalarResolvent ScalarModular BoundarySineModes ScalarSpectralResidues
open PositiveResidueInterlacing Polynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem numerator_eq_positiveResidues {R w : ℕ} (hR : 0<R) (hw : 0<w) :
    weightedNumerator hw (boundaryGreen hR w)=
      numerator (eigenvalue w) (residue R w) := by
  have hinf : Set.Infinite {z : ℝ | (pathPolynomial w).eval z≠0} := by
    simpa only [Polynomial.IsRoot,Set.compl_ofPred] using
      (Polynomial.finite_setOfPred_isRoot (pathPolynomial_monic w).ne_zero).infinite_compl
  apply Polynomial.eq_of_infinite_eval_eq
  apply hinf.mono
  intro z hz
  have hp := (pathPolynomial_eval_ne_zero_iff w z).mp hz
  apply (div_left_inj' hz).mp
  rw [← boundaryGreen_scalar_resolvent hR hw z,scalar_resolvent_residues hR hw z hp]
  have hn := eval_div_product (eigenvalue w) (residue R w) z hp
  have hden : (pathPolynomial w).eval z=∏ i : Fin w,(z-eigenvalue w i) := by
    rw [pathPolynomial_factorization]
    simp only [Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  rw [hden]
  exact hn.symm

/-- Every zero of the actual rational numerator lies strictly between
successive explicit zeros of P, one in each interval. The factorization and
nonzero leading coefficient make this a complete list of simple zeros. -/
theorem strict_zero_interlacing {R w : ℕ} (hR : 0<R) (hw : 0<w) :
    ∃ root : Fin (w-1) → ℝ, StrictMono root ∧
      (∀ i,eigenvalue w (leftIndex hw i)<root i ∧ root i<eigenvalue w (rightIndex hw i)) ∧
      (rationalScalarNumerator hR hw).map (algebraMap ℚ ℝ)=
        (∏ i : Fin (w-1),(X-C (root i)))*
          C ((rationalScalarNumerator hR hw).map (algebraMap ℚ ℝ)).leadingCoeff ∧
      ((rationalScalarNumerator hR hw).map (algebraMap ℚ ℝ)).leadingCoeff≠0 := by
  have h := exists_interlacing hw (eigenvalue w) (residue R w)
    (eigenvalue_strictMono w) (residue_pos R w)
  simpa only [← numerator_eq_positiveResidues hR hw,← rationalScalarNumerator_map hR hw] using h

end
end SpanningTreeIsoperimetry.ScalarSpectralInterlacing
