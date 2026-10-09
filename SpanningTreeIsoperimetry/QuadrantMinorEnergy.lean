import SpanningTreeIsoperimetry.BoundaryGreenBounds
import SpanningTreeIsoperimetry.CornerLimit

/-! Every actual finite Ferrers energy is the log determinant of its actual
quadrant Green minor, with no fixed-size restriction on the diagram. -/
namespace SpanningTreeIsoperimetry.QuadrantMinorEnergy

open Ferrers CornerEnergy BoundaryGreenBounds BoundaryGreenLoss Filter
open scoped BigOperators Matrix Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def quadrantMinor {ι : Type*} (points : ι → Point) : Matrix ι ι ℝ :=
  fun i j => quadrantGreen (points i) (points j)

theorem exp_energy_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Diagram}
    (hM : IsFerrers M) (e : ι ≃ {p // p∈M}) :
    Real.exp (-realEnergy M-SquareMaximality.squareLatticeEntropy*M.card) =
      (quadrantMinor (fun i => (e i).val)).det := by
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
  have hentry (N : ℕ) : (greenMinor (hfit N)).submatrix e e =
      (fun i j => green (box (idx N)) (e i).val (e j).val) := by
    ext i j
    rw [hbox,green_mem (hfit N (e i).property) (hfit N (e j).property)]
    rfl
  have hdet (N : ℕ) : (greenMinor (hfit N)).det =
      (Matrix.of (fun i j => green (box (idx N)) (e i).val (e j).val)).det := by
    rw [← Matrix.det_submatrix_equiv_self e,hentry]
    rfl
  have he := greenMinor_det_tendsto hM hfit hside hside
  simp only [hdet] at he
  have hm : Tendsto (fun N => Matrix.of (fun i j => green (box (idx N)) (e i).val (e j).val))
      atTop (𝓝 (quadrantMinor (fun i => (e i).val))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact (green_tendsto_quadrant (e i).val (e j).val).comp hidx
  have hd := ((show Continuous (Matrix.det : Matrix ι ι ℝ → ℝ)
    from continuous_id.matrix_det).tendsto _).comp hm
  exact tendsto_nhds_unique he hd

theorem energy_eq_log_det {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Diagram}
    (hM : IsFerrers M) (e : ι ≃ {p // p∈M}) :
    realEnergy M = -Real.log ((quadrantMinor (fun i => (e i).val)).det)-
      SquareMaximality.squareLatticeEntropy*M.card := by
  have h := congrArg Real.log (exp_energy_eq_det hM e)
  rw [Real.log_exp] at h
  linarith

theorem quadrantMinor_det_pos {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Diagram}
    (hM : IsFerrers M) (e : ι ≃ {p // p∈M}) :
    0<(quadrantMinor (fun i => (e i).val)).det := by
  rw [← exp_energy_eq_det hM e]
  exact Real.exp_pos _

end
end SpanningTreeIsoperimetry.QuadrantMinorEnergy
