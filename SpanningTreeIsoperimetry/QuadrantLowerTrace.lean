module

public import SpanningTreeIsoperimetry.QuadrantMinorEnergy
public import SpanningTreeIsoperimetry.GreenLogDetComparison
public import SpanningTreeIsoperimetry.GreenStripLimits
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

/-! Positive definiteness of actual quadrant minors, and a lower trace bound
for finite corrections after extending one side to an infinite strip. -/
namespace SpanningTreeIsoperimetry.QuadrantLowerTrace
open Ferrers CornerEnergy BoundaryGreenLoss BoundaryGreenBounds QuadrantMinorEnergy
  GreenStripLimits Filter
open scoped Classical BigOperators Matrix Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

def minor (M : Diagram) : Matrix {p // p∈M} {p // p∈M} ℝ := quadrantMinor Subtype.val

theorem minor_posDef {M : Diagram} (hM : IsFerrers M) : (minor M).PosDef := by
  let E := enclosingSide M
  let idx := fun N : ℕ => E+N-1
  have hE : 1≤E := by dsimp [E,enclosingSide]; omega
  have hidx : Tendsto idx atTop atTop :=
    tendsto_atTop_mono (fun N => by dsimp [idx]; omega) tendsto_id
  let hfit (N : ℕ) : M⊆faceRectangle (E+N) (E+N) := subset_enclosingSquare M N
  have hbox (N : ℕ) : box (idx N)=faceRectangle (E+N) (E+N) := by
    unfold box
    rw [show idx N+1=E+N by dsimp [idx]; omega]
  have hentry (N : ℕ) (i j : {p // p∈M}) :
      greenMinor (hfit N) i j=green (box (idx N)) i.val j.val := by
    rw [hbox,green_mem (hfit N i.property) (hfit N j.property)]
    rfl
  have ht : Tendsto (fun N => greenMinor (hfit N)) atTop (𝓝 (minor M)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    simp only [hentry]
    exact (green_tendsto_quadrant i.val j.val).comp hidx
  have hps : (minor M).PosSemidef := Matrix.posSemidef_is_closed.mem_of_tendsto ht
    (Eventually.of_forall (fun N => (GreenLogDetComparison.greenMinor_posDef
      (Finset.Subset.refl (faceRectangle (E+N) (E+N))) (hfit N)).posSemidef))
  apply hps.posDef_iff_det_ne_zero.mpr
  exact (quadrantMinor_det_pos hM (Equiv.refl {p // p∈M})).ne'

theorem correction_eq_log_det {R S : ℕ} {M : Diagram} (hM : IsFerrers M)
    (hfit : M⊆faceRectangle R S) :
    correction (faceRectangle R S) M=Real.log (minor M).det-Real.log (greenMinor hfit).det := by
  have he := dirichletEnergy_eq hM hfit
  have hq := energy_eq_log_det hM (Equiv.refl {p // p∈M})
  change realEnergy M= -Real.log (minor M).det-SquareMaximality.squareLatticeEntropy*M.card at hq
  unfold dirichletEnergy at he
  linarith only [he,hq]

theorem finite_lower_trace {R S : ℕ} {M : Diagram} (hM : IsFerrers M)
    (hfit : M⊆faceRectangle R S) :
    Matrix.trace ((minor M)⁻¹*(minor M-greenMinor hfit))≤correction (faceRectangle R S) M := by
  have h := LogDetTangent.log_det_tangent (minor_posDef hM)
    (GreenLogDetComparison.greenMinor_posDef (Finset.Subset.refl (faceRectangle R S)) hfit)
  have he : (minor M)⁻¹*(greenMinor hfit-minor M)= -((minor M)⁻¹*(minor M-greenMinor hfit)) := by
    noncomm_ring
  rw [he,Matrix.trace_neg] at h
  rw [correction_eq_log_det hM hfit]
  linarith only [h]

def stripMinorX (R : ℕ) (M : Diagram) : Matrix {p // p∈M} {p // p∈M} ℝ :=
  fun i j => stripX R i.val j.val

/-- Domain monotonicity is applied before the limiting trace, so this theorem
requires no entrywise sign assumption on the inverse quadrant minor. -/
theorem strip_lower_trace {R S : ℕ} {M : Diagram} (hM : IsFerrers M)
    (hfit : M⊆faceRectangle R S) :
    Matrix.trace ((minor M)⁻¹*(minor M-stripMinorX R M))≤correction (faceRectangle R S) M := by
  let fit (N : ℕ) : M⊆faceRectangle R (N+S) :=
    Finset.Subset.trans hfit (FiniteGreenMonotonicity.rectangle_subset le_rfl (by omega))
  have ht : Tendsto (fun N => greenMinor (fit N)) atTop (𝓝 (stripMinorX R M)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have he (N : ℕ) : greenMinor (fit N) i j=green (faceRectangle R (N+S)) i.val j.val := by
      rw [green_mem (fit N i.property) (fit N j.property)]
      rfl
    simp only [he]
    exact (stripX_tendsto R i.val j.val).comp (tendsto_add_atTop_nat S)
  have hc : Continuous (fun G : Matrix {p // p∈M} {p // p∈M} ℝ =>
      Matrix.trace ((minor M)⁻¹*(minor M-G))) := by fun_prop
  have hlim := (hc.tendsto (stripMinorX R M)).comp ht
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro N
  exact (finite_lower_trace hM (fit N)).trans
    (FiniteGreenMonotonicity.correction_antitone_ambient
      (FiniteGreenMonotonicity.rectangle_subset le_rfl (show S≤N+S by omega)))

end
end SpanningTreeIsoperimetry.QuadrantLowerTrace
