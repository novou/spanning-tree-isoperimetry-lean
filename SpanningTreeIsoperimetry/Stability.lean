module

public import SpanningTreeIsoperimetry.HullBounds
public import SpanningTreeIsoperimetry.RectangularComparison
public import SpanningTreeIsoperimetry.Targets

@[expose] public section

/-! The quantitative stability inequality in the current graph model.
Optimality of the coefficient requires a separate asymptotic argument. -/
namespace SpanningTreeIsoperimetry

/-- Cancelling the bulk terms leaves the exact hull side-sum penalty. -/
theorem hull_stability {S : Domain} {n r s : ℕ} {a b : ℤ}
    (hn : 0 < n) (hcard : S.card = n^2) (hconn : (domainGraph S).Connected)
    (hHull : SquareMaximality.IsRectHull S a b r s) :
    Real.log (treeCount (rectangle n n) : ℝ) - Real.log (treeCount S : ℝ) ≥
      Real.log (1 + Real.sqrt 2) * ((r : ℝ) + s - 2*n) := by
  have harea : n^2 ≤ r*s := by
    have hc := Finset.card_le_card hHull.2.2.1
    simpa only [hcard, SquareMaximality.rectangle_card] using hc
  have hbulk := hull_bulk_bound hconn hHull
  rw [hcard, Nat.cast_sub harea, Nat.cast_mul, Nat.cast_pow] at hbulk
  have hrect := RectangularComparison.rectangular_comparison hn hHull.1 hHull.2.1 harea
  linarith

/-- The inequality of manuscript `thm:sharp-stability`, for every connected
square-cardinality domain. Its asymptotic sharpness is a further obligation. -/
theorem sharp_stability_inequality {n : ℕ} (hn : 0 < n) (S : Domain)
    (hcard : S.card = n^2) (hconn : (domainGraph S).Connected) :
    Real.log ((treeCount (rectangle n n) : ℝ) / treeCount S) ≥
      (Real.log (1 + Real.sqrt 2) / 4) * n * normalizedAsymmetry n S ^ 2 := by
  obtain ⟨r,s,hr,hs,hfit,harea,hbulk⟩ := exists_hull_bulk_bound hconn
  have ha : n^2 ≤ r*s := by simpa only [hcard] using harea
  rw [hcard, Nat.cast_sub ha, Nat.cast_mul, Nat.cast_pow] at hbulk
  have hrect := RectangularComparison.rectangular_comparison hn hr hs ha
  have hlog : Real.log (1 + Real.sqrt 2) * ((r : ℝ) + s - 2*n) ≤
      Real.log (treeCount (rectangle n n) : ℝ) - Real.log (treeCount S : ℝ) := by
    linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnzero : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have halpha : 0 ≤ Real.log (1 + Real.sqrt 2) :=
    Real.log_nonneg (by linarith [Real.sqrt_nonneg (2 : ℝ)])
  have hgeom := mul_le_mul_of_nonneg_left
    (normalizedAsymmetry_sq_le_of_fits hn hcard hfit)
    (show 0 ≤ (Real.log (1 + Real.sqrt 2) / 4) * n by positivity)
  have hc : (Real.log (1 + Real.sqrt 2) / 4) * n *
      (4 * ((r : ℝ) + s - 2*n) / n) =
      Real.log (1 + Real.sqrt 2) * ((r : ℝ) + s - 2*n) := by
    field_simp
  rw [hc] at hgeom
  have hpS : (0 : ℝ) < treeCount S := by
    exact_mod_cast (treeCount_pos_iff_connected S).mpr hconn
  have hpSquare : (0 : ℝ) < treeCount (rectangle n n) := by
    rw [rectangle_treeCount_eq_foundation]
    exact_mod_cast SquareMaximality.tauRect_pos hn hn
  rw [Real.log_div (ne_of_gt hpSquare) (ne_of_gt hpS)]
  exact hgeom.trans hlog

/-- The recorded inequality target is now discharged by a closed proof. -/
theorem sharpStabilityInequalityTarget : SharpStabilityInequalityTarget := by
  intro n hn S hcard hconn
  exact sharp_stability_inequality hn S hcard hconn

end SpanningTreeIsoperimetry
