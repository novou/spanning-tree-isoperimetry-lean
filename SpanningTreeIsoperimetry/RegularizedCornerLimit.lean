import SpanningTreeIsoperimetry.RegularizedCornerDeterminant

/-! Actual quadrant inverse-minor normalization for the regularized loop
energy. The bulk term is the convergent closed-loop series, independently of
any symbol or determinant asymptotic. -/
namespace SpanningTreeIsoperimetry.RegularizedCornerLimit
open Ferrers CornerEnergy RegularizedGreenSeries RegularizedQuadrantGreen
open RegularizedCornerDeterminant StripSpectralRegularization BoundaryGreenBounds Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem correctionZ_tendsto_zero {z : ℝ} (hz : 4≤z) (M : Diagram) {m n : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop) :
    Tendsto (fun k => correctionZ z (faceRectangle (m k) (n k)) M) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (correction_tendsto_zero M hm hn)
  · exact Eventually.of_forall (fun k => correctionZ_nonneg hz _ M)
  · exact Eventually.of_forall (fun k => correctionZ_le hz _ M)

theorem greenMinorZ_det_tendsto {z : ℝ} (hz : 4≤z) {M : Diagram}
    (hM : IsFerrers M) {m n : ℕ → ℕ} (hfit : ∀ k,M⊆faceRectangle (m k) (n k))
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop) :
    Tendsto (fun k => (greenMinorZ z (hfit k)).det) atTop
      (𝓝 (Real.exp (-spectralEnergy M z-bulkEntropy z*M.card))) := by
  have he : Tendsto (fun k => spectralEnergy M z+correctionZ z (faceRectangle (m k) (n k)) M)
      atTop (𝓝 (spectralEnergy M z)) := by
    simpa only [add_zero] using tendsto_const_nhds.add (correctionZ_tendsto_zero hz M hm hn)
  have ht := (he.neg.sub_const (bulkEntropy z*M.card)).rexp
  convert ht using 1
  funext k
  rw [spectralEnergy_add_correctionZ_greenMinor hz hM (hfit k)]
  have hp := greenMinorZ_det_pos hz (Finset.Subset.refl (faceRectangle (m k) (n k))) (hfit k)
  convert (Real.exp_log hp).symm using 1 <;> congr 1 <;> ring

def quadrantMinorZ (z : ℝ) {ι : Type*} (points : ι → Point) : Matrix ι ι ℝ :=
  fun i j => quadrantGreenZ z (points i) (points j)

/-- Every finite Ferrers minor of the actual massive quadrant Green kernel
has the actual regularized closed-word energy as its normalized determinant. -/
theorem exp_spectralEnergy_eq_det {z : ℝ} (hz : 4≤z)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Diagram}
    (hM : IsFerrers M) (e : ι ≃ {p // p∈M}) :
    Real.exp (-spectralEnergy M z-bulkEntropy z*M.card)=
      (quadrantMinorZ z (fun i => (e i).val)).det := by
  let E := enclosingSide M
  let idx := fun N : ℕ => E+N-1
  have hE : 1≤E := by dsimp [E,enclosingSide]; omega
  have hidx : Tendsto idx atTop atTop := by
    apply tendsto_atTop_mono (fun N => by dsimp [idx]; omega) tendsto_id
  have hside : Tendsto (fun N : ℕ => E+N) atTop atTop := by
    apply tendsto_atTop_mono (fun N => by change N≤E+N; omega) tendsto_id
  have hfit (N : ℕ) : M⊆faceRectangle (E+N) (E+N) := subset_enclosingSquare M N
  have hbox (N : ℕ) : box (idx N)=faceRectangle (E+N) (E+N) := by
    unfold box
    rw [show idx N+1=E+N by dsimp [idx]; omega]
  have hentry (N : ℕ) : (greenMinorZ z (hfit N)).submatrix e e=
      (fun i j => greenZ z (box (idx N)) (e i).val (e j).val) := by
    ext i j
    rw [hbox,greenZ_mem (hfit N (e i).property) (hfit N (e j).property)]
    rfl
  have hdet (N : ℕ) : (greenMinorZ z (hfit N)).det=
      (Matrix.of (fun i j => greenZ z (box (idx N)) (e i).val (e j).val)).det := by
    rw [← Matrix.det_submatrix_equiv_self e,hentry]
    rfl
  have he := greenMinorZ_det_tendsto hz hM hfit hside hside
  simp only [hdet] at he
  have hm : Tendsto (fun N => Matrix.of (fun i j => greenZ z (box (idx N)) (e i).val (e j).val))
      atTop (𝓝 (quadrantMinorZ z (fun i => (e i).val))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact (greenZ_tendsto_quadrant hz (e i).val (e j).val).comp hidx
  have hd := ((show Continuous (Matrix.det : Matrix ι ι ℝ → ℝ)
    from continuous_id.matrix_det).tendsto _).comp hm
  exact tendsto_nhds_unique he hd

theorem spectralEnergy_eq_log_det {z : ℝ} (hz : 4≤z)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Diagram}
    (hM : IsFerrers M) (e : ι ≃ {p // p∈M}) :
    spectralEnergy M z= -Real.log ((quadrantMinorZ z (fun i => (e i).val)).det)-
      bulkEntropy z*M.card := by
  have h := congrArg Real.log (exp_spectralEnergy_eq_det hz hM e)
  rw [Real.log_exp] at h
  linarith

theorem quadrantMinorZ_det_pos {z : ℝ} (hz : 4≤z)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Diagram}
    (hM : IsFerrers M) (e : ι ≃ {p // p∈M}) :
    0<(quadrantMinorZ z (fun i => (e i).val)).det := by
  rw [← exp_spectralEnergy_eq_det hz hM e]
  exact Real.exp_pos _

end
end SpanningTreeIsoperimetry.RegularizedCornerLimit
