module

public import SquareMaximality.Boundary.DeterminantSeries

@[expose] public section

set_option backward.privateInPublic true

/-! Trace-moment comparison implies determinant comparison at every
positive spectral parameter. This generalizes the included finite
log-determinant proof to arbitrary parameters and different index types. -/
namespace SpanningTreeIsoperimetry.DeterminantComparison

open scoped BigOperators
open SquareMaximality.Boundary.DeterminantSeries

noncomputable def traceTerm {I : Type*} [Fintype I] [DecidableEq I]
    (c : ℝ) (A : Matrix I I ℝ) (n : ℕ) : ℝ :=
  Matrix.trace (A^(n+1)) / ((n+1 : ℝ)*c^(n+1))

theorem eigenvalue_series {c x : ℝ} (hc : 0 < c) (hx : |x| < c) :
    HasSum (fun n : ℕ => x^(n+1) / ((n+1 : ℝ)*c^(n+1)))
      (-Real.log (1-x/c)) := by
  have hr : |x/c| < 1 := by
    rw [abs_div, abs_of_pos hc]
    exact (div_lt_one hc).mpr hx
  refine (Real.hasSum_pow_div_log_of_abs_lt_one hr).congr_fun ?_
  intro n
  rw [div_pow]
  push_cast
  field_simp

private theorem hasSum_finset {I : Type*} (s : Finset I)
    (f : I → ℕ → ℝ) (g : I → ℝ) (h : ∀ i ∈ s, HasSum (f i) (g i)) :
    HasSum (fun n => ∑ i ∈ s, f i n) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (h i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem det_shift_eq_prod {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (hA : A.IsHermitian) (c : ℝ) :
    Matrix.det (c • (1 : Matrix I I ℝ)-A) = ∏ i, (c-hA.eigenvalues i) := by
  have hc : c • (1 : Matrix I I ℝ) = Matrix.scalar I c := by
    ext i j
    by_cases hij : i=j <;> simp [hij,Matrix.scalar_apply]
  rw [hc,← Matrix.eval_charpoly,hA.charpoly_eq,Polynomial.eval_prod]
  simp

theorem det_shift_pos {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (hA : A.IsHermitian) {c : ℝ}
    (hspec : ∀ i, |hA.eigenvalues i| < c) :
    0 < Matrix.det (c • (1 : Matrix I I ℝ)-A) := by
  rw [det_shift_eq_prod hA]
  exact Finset.prod_pos (fun i _ => sub_pos.mpr (abs_lt.mp (hspec i)).2)

/-- The full convergent trace expansion, with a strictly valid spectral parameter. -/
theorem logdet_hasSum {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℝ} (hA : A.IsHermitian) {c : ℝ} (hc : 0 < c)
    (hspec : ∀ i, |hA.eigenvalues i| < c) :
    HasSum (traceTerm c A)
      ((Fintype.card I : ℝ)*Real.log c - Real.log (Matrix.det (c • (1 : Matrix I I ℝ)-A))) := by
  have hseries := hasSum_finset Finset.univ
    (fun i n => hA.eigenvalues i^(n+1)/((n+1 : ℝ)*c^(n+1)))
    (fun i => -Real.log (1-hA.eigenvalues i/c))
    (fun i _ => eigenvalue_series hc (hspec i))
  have htrace : (fun n : ℕ => ∑ i, hA.eigenvalues i^(n+1)/((n+1 : ℝ)*c^(n+1))) =
      traceTerm c A := by
    funext n
    rw [traceTerm,trace_pow_eq_sum_eigenvalues_pow hA,Finset.sum_div]
  rw [htrace] at hseries
  have hfactor (i : I) : Real.log (c-hA.eigenvalues i) =
      Real.log c + Real.log (1-hA.eigenvalues i/c) := by
    have hp : 0 < 1-hA.eigenvalues i/c := by
      rw [sub_pos]
      exact (div_lt_one hc).mpr (abs_lt.mp (hspec i)).2
    rw [← Real.log_mul hc.ne' hp.ne']
    congr 1
    field_simp
  have hlog : Real.log (Matrix.det (c • (1 : Matrix I I ℝ)-A)) =
      ∑ i, (Real.log c + Real.log (1-hA.eigenvalues i/c)) := by
    rw [det_shift_eq_prod hA,Real.log_prod]
    · exact Finset.sum_congr rfl (fun i _ => hfactor i)
    · exact fun i _ => (sub_pos.mpr (abs_lt.mp (hspec i)).2).ne'
  convert hseries using 1
  rw [hlog,Finset.sum_add_distrib,Finset.sum_neg_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

/-- Larger positive-length trace moments give a smaller shifted determinant. -/
theorem determinant_le_of_trace_le {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {A : Matrix I I ℝ} {B : Matrix J J ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {c : ℝ} (hc : 0 < c)
    (hspecA : ∀ i, |hA.eigenvalues i| < c) (hspecB : ∀ i, |hB.eigenvalues i| < c)
    (hcard : Fintype.card I = Fintype.card J)
    (htrace : ∀ n : ℕ, Matrix.trace (A^(n+1)) ≤ Matrix.trace (B^(n+1))) :
    Matrix.det (c • (1 : Matrix J J ℝ)-B) ≤ Matrix.det (c • (1 : Matrix I I ℝ)-A) := by
  have ha := logdet_hasSum hA hc hspecA
  have hb := logdet_hasSum hB hc hspecB
  have hs := ha.summable.tsum_le_tsum (fun n =>
    div_le_div_of_nonneg_right (htrace n) (by positivity)) hb.summable
  change (∑' i, traceTerm c A i) ≤ ∑' i, traceTerm c B i at hs
  rw [ha.tsum_eq,hb.tsum_eq,hcard] at hs
  apply (Real.log_le_log_iff (det_shift_pos hB hspecB) (det_shift_pos hA hspecA)).mp
  linarith

/-- A strict inequality in any positive-length moment makes the determinant
comparison strict at every parameter covered by the spectral bounds. -/
theorem determinant_lt_of_trace_lt {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] {A : Matrix I I ℝ} {B : Matrix J J ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {c : ℝ} (hc : 0 < c)
    (hspecA : ∀ i, |hA.eigenvalues i| < c) (hspecB : ∀ i, |hB.eigenvalues i| < c)
    (hcard : Fintype.card I = Fintype.card J)
    (htrace : ∀ n : ℕ, Matrix.trace (A^(n+1)) ≤ Matrix.trace (B^(n+1)))
    (hstrict : ∃ n : ℕ, Matrix.trace (A^(n+1)) < Matrix.trace (B^(n+1))) :
    Matrix.det (c • (1 : Matrix J J ℝ)-B) < Matrix.det (c • (1 : Matrix I I ℝ)-A) := by
  obtain ⟨n,hn⟩ := hstrict
  have ha := logdet_hasSum hA hc hspecA
  have hb := logdet_hasSum hB hc hspecB
  have hs := Summable.tsum_lt_tsum (f := traceTerm c A) (g := traceTerm c B) (i := n)
    (fun k => show traceTerm c A k ≤ traceTerm c B k from
      div_le_div_of_nonneg_right (htrace k) (by positivity))
    (show traceTerm c A n < traceTerm c B n from
      div_lt_div_of_pos_right hn (by positivity))
    ha.summable hb.summable
  rw [ha.tsum_eq,hb.tsum_eq,hcard] at hs
  apply (Real.log_lt_log_iff (det_shift_pos hB hspecB) (det_shift_pos hA hspecA)).mp
  linarith

end SpanningTreeIsoperimetry.DeterminantComparison
