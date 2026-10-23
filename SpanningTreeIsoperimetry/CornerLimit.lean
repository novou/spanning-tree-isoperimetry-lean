module

public import SpanningTreeIsoperimetry.CornerDeterminant
public import Mathlib.Analysis.Normed.Group.Tannery

@[expose] public section

/-! The quadrant energy is the limit of the actual finite Green-minor
energies. The proof uses eventual containment of each finite word and the
already proved summable closed-word bound. -/
namespace SpanningTreeIsoperimetry.CornerEnergy

open Ferrers Filter
open scoped Topology

theorem lostCount_eq_zero_of_large {m n : ℕ} (M P : Diagram)
    (hm : M.sup Prod.fst + P.sup Prod.fst < m)
    (hn : M.sup Prod.snd + P.sup Prod.snd < n) :
    lostCount (faceRectangle m n) M P = 0 := by
  rw [lostCount, Finset.card_eq_zero, lostStarts, Finset.sdiff_eq_empty_iff_subset]
  intro t ht
  have hM := hitStarts_subset M P ht
  have hx := Finset.le_sup (f := Prod.fst) hM
  have hy := Finset.le_sup (f := Prod.snd) hM
  rw [fittingStarts_faceRectangle, mem_faceRectangle]
  constructor <;> omega

theorem lostCount_eventually_zero (M P : Diagram) {m n : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop) :
    ∀ᶠ k in atTop, lostCount (faceRectangle (m k) (n k)) M P = 0 := by
  filter_upwards [hm.eventually (eventually_gt_atTop (M.sup Prod.fst + P.sup Prod.fst)),
    hn.eventually (eventually_gt_atTop (M.sup Prod.snd + P.sup Prod.snd))] with k hkx hky
  exact lostCount_eq_zero_of_large M P hkx hky

theorem correctionTerm_eventually_zero (M : Diagram) (i : ℕ) {m n : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop) :
    ∀ᶠ k in atTop, correctionTerm (faceRectangle (m k) (n k)) M i = 0 := by
  have hall : ∀ᶠ k in atTop, ∀ w : ClosedWord (i+1),
      lostCount (faceRectangle (m k) (n k)) M (normalizedVisited w.val) = 0 :=
    eventually_all.mpr (fun w => lostCount_eventually_zero M (normalizedVisited w.val) hm hn)
  filter_upwards [hall] with k hk
  simp [correctionTerm, lostSum, hk]

/-- Both side lengths can tend to infinity independently. The nonnegative
finite-domain correction vanishes, without a quantitative aspect-ratio
condition or an assumed Green-function limit. -/
theorem correction_tendsto_zero (M : Diagram) {m n : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop) :
    Tendsto (fun k => correction (faceRectangle (m k) (n k)) M) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    (closedWordTerm_summable.mul_left (M.card : ℝ))
    (f := fun k i => correctionTerm (faceRectangle (m k) (n k)) M i)
    (g := fun _ => (0 : ℝ))
    (fun i => (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
      ((correctionTerm_eventually_zero M i hm hn).mono (fun _ hk => hk.symm)))
    (Eventually.of_forall (fun k i => by
      rw [Real.norm_eq_abs, abs_of_nonneg (correctionTerm_nonneg _ _ _)]
      exact correctionTerm_le_closedWordTerm _ _ _))
  simpa only [tsum_zero, correction] using h

theorem finiteWordEnergy_tendsto (M : Diagram) {m n : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop) :
    Tendsto (fun k => finiteWordEnergy (faceRectangle (m k) (n k)) M)
      atTop (𝓝 (realEnergy M)) := by
  simpa only [finiteWordEnergy, add_zero] using
    tendsto_const_nhds.add (correction_tendsto_zero M hm hn)

/-- The limiting energy is the limit of the actual inverse-matrix minors,
for every containing rectangular exhaustion of the quadrant. -/
theorem dirichletEnergy_tendsto {M : Diagram} (hM : IsFerrers M) {m n : ℕ → ℕ}
    (hfit : ∀ k, M ⊆ faceRectangle (m k) (n k))
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop) :
    Tendsto (fun k => dirichletEnergy (hfit k)) atTop (𝓝 (realEnergy M)) := by
  simp_rw [dirichletEnergy_eq hM]
  exact finiteWordEnergy_tendsto M hm hn

theorem greenMinor_det_tendsto {M : Diagram} (hM : IsFerrers M) {m n : ℕ → ℕ}
    (hfit : ∀ k, M ⊆ faceRectangle (m k) (n k))
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop) :
    Tendsto (fun k => Matrix.det (greenMinor (hfit k))) atTop
      (𝓝 (Real.exp (-realEnergy M - SquareMaximality.squareLatticeEntropy * M.card))) := by
  have ht := ((dirichletEnergy_tendsto hM hfit hm hn).neg.sub_const
    (SquareMaximality.squareLatticeEntropy * M.card)).rexp
  convert ht using 1
  funext k
  have hp := greenMinor_det_pos (Finset.Subset.refl (faceRectangle (m k) (n k))) (hfit k)
  change Matrix.det (greenMinor (hfit k)) = Real.exp
    (-(-Real.log (Matrix.det (greenMinor (hfit k))) -
      SquareMaximality.squareLatticeEntropy * M.card) -
      SquareMaximality.squareLatticeEntropy * M.card)
  convert (Real.exp_log hp).symm using 1 <;> congr 1 <;> ring

/-- An explicit exhaustion, so the limit theorem also has an endpoint with
no supplied sequence of containing rectangles. -/
def enclosingSide (M : Diagram) : ℕ := M.sup Prod.fst + M.sup Prod.snd + 1

theorem subset_enclosingSquare (M : Diagram) (k : ℕ) :
    M ⊆ faceRectangle (enclosingSide M + k) (enclosingSide M + k) := by
  intro t ht
  have hx := Finset.le_sup (f := Prod.fst) ht
  have hy := Finset.le_sup (f := Prod.snd) ht
  simp only [mem_faceRectangle, enclosingSide]
  constructor <;> omega

theorem enclosingSquareEnergy_tendsto {M : Diagram} (hM : IsFerrers M) :
    Tendsto (fun k => dirichletEnergy (subset_enclosingSquare M k))
      atTop (𝓝 (realEnergy M)) := by
  have ht : Tendsto (fun k : ℕ => enclosingSide M + k) atTop atTop := by
    apply tendsto_atTop_mono (fun k => Nat.le_add_left k (enclosingSide M)) tendsto_id
  exact dirichletEnergy_tendsto hM (subset_enclosingSquare M) ht ht

end SpanningTreeIsoperimetry.CornerEnergy
