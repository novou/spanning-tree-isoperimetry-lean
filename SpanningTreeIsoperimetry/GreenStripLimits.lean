module

public import SpanningTreeIsoperimetry.GreenUnionBound

@[expose] public section

/-! Actual infinite-strip Green kernels and the two-boundary loss inequality.
All limits are bounded monotone limits of finite inverse matrices. -/
namespace SpanningTreeIsoperimetry.GreenStripLimits
open Ferrers CornerEnergy BoundaryGreenLoss BoundaryGreenBounds GreenUnionBound
open Filter
open scoped Topology
noncomputable section

def stripX (R : ℕ) (p q : Point) : ℝ := ⨆ S : ℕ, green (faceRectangle R S) p q
def stripY (S : ℕ) (p q : Point) : ℝ := ⨆ R : ℕ, green (faceRectangle R S) p q

theorem stripX_bdd (R : ℕ) (p q : Point) :
    BddAbove (Set.range (fun S => green (faceRectangle R S) p q)) := by
  refine ⟨min ((p.1 : ℝ)+1) ((q.1 : ℝ)+1),?_⟩
  rintro _ ⟨S,rfl⟩
  exact green_le_tent (Finset.Subset.refl _) p q

theorem stripY_bdd (S : ℕ) (p q : Point) :
    BddAbove (Set.range (fun R => green (faceRectangle R S) p q)) := by
  refine ⟨min ((p.1 : ℝ)+1) ((q.1 : ℝ)+1),?_⟩
  rintro _ ⟨R,rfl⟩
  exact green_le_tent (Finset.Subset.refl _) p q

theorem stripX_tendsto (R : ℕ) (p q : Point) :
    Tendsto (fun S => green (faceRectangle R S) p q) atTop (𝓝 (stripX R p q)) := by
  apply tendsto_atTop_ciSup _ (stripX_bdd R p q)
  intro S T hST
  exact green_mono (Finset.Subset.refl _) (Finset.Subset.refl _)
    (FiniteGreenMonotonicity.rectangle_subset le_rfl hST) p q

theorem stripY_tendsto (S : ℕ) (p q : Point) :
    Tendsto (fun R => green (faceRectangle R S) p q) atTop (𝓝 (stripY S p q)) := by
  apply tendsto_atTop_ciSup _ (stripY_bdd S p q)
  intro R T hRT
  exact green_mono (Finset.Subset.refl _) (Finset.Subset.refl _)
    (FiniteGreenMonotonicity.rectangle_subset hRT le_rfl) p q

theorem finite_green_le_stripX (R S : ℕ) (p q : Point) : green (faceRectangle R S) p q≤stripX R p q :=
  le_ciSup (stripX_bdd R p q) S

theorem finite_green_le_stripY (R S : ℕ) (p q : Point) : green (faceRectangle R S) p q≤stripY S p q :=
  le_ciSup (stripY_bdd S p q) R

theorem stripX_le_quadrant (R : ℕ) (p q : Point) : stripX R p q≤quadrantGreen p q := by
  apply ciSup_le
  intro S
  exact finite_green_le_quadrant (Finset.Subset.refl _) p q

theorem stripY_le_quadrant (S : ℕ) (p q : Point) : stripY S p q≤quadrantGreen p q := by
  apply ciSup_le
  intro R
  exact finite_green_le_quadrant (Finset.Subset.refl _) p q

theorem shifted_rectangle_tendsto_quadrant {R S : ℕ} (hR : 1≤R) (hS : 1≤S) (p q : Point) :
    Tendsto (fun n : ℕ => green (faceRectangle (R+n) (S+n)) p q)
      atTop (𝓝 (quadrantGreen p q)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (green_tendsto_quadrant p q) tendsto_const_nhds
  · intro n
    exact green_mono (Finset.Subset.refl _) (Finset.Subset.refl _)
      (FiniteGreenMonotonicity.rectangle_subset (by omega : n+1≤R+n) (by omega)) p q
  · intro n
    exact finite_green_le_quadrant (Finset.Subset.refl _) p q

theorem stripX_shift_tendsto (R S : ℕ) (p q : Point) :
    Tendsto (fun n : ℕ => green (faceRectangle R (S+n)) p q) atTop (𝓝 (stripX R p q)) :=
  (stripX_tendsto R p q).comp
    (tendsto_atTop_mono (fun n => Nat.le_add_left n S) tendsto_id)

theorem stripY_shift_tendsto (R S : ℕ) (p q : Point) :
    Tendsto (fun n : ℕ => green (faceRectangle (R+n) S) p q) atTop (𝓝 (stripY S p q)) :=
  (stripY_tendsto S p q).comp
    (tendsto_atTop_mono (fun n => Nat.le_add_left n R) tendsto_id)

theorem rectangle_inter_shift (R S n : ℕ) :
    faceRectangle R (S+n)∩faceRectangle (R+n) S=faceRectangle R S := by
  ext p
  simp only [Finset.mem_inter,mem_faceRectangle]
  omega

theorem quadrant_loss_le_strip_losses {R S : ℕ} {p q : Point}
    (hp : p∈faceRectangle R S) (hq : q∈faceRectangle R S) :
    quadrantLoss (faceRectangle R S) p q≤
      (quadrantGreen p q-stripX R p q)+(quadrantGreen p q-stripY S p q) := by
  have hr : 1≤R := by have := (mem_faceRectangle.mp hp).1; omega
  have hs : 1≤S := by have := (mem_faceRectangle.mp hp).2; omega
  have htleft := (stripX_shift_tendsto R S p q).add (stripY_shift_tendsto R S p q)
  have htright := (shifted_rectangle_tendsto_quadrant hr hs p q).add_const
    (green (faceRectangle R S) p q)
  have hcompare := le_of_tendsto_of_tendsto htleft htright (Filter.Eventually.of_forall (fun n => by
    have hpI : p∈faceRectangle R (S+n)∩faceRectangle (R+n) S := by
      rw [rectangle_inter_shift]; exact hp
    have hqI : q∈faceRectangle R (S+n)∩faceRectangle (R+n) S := by
      rw [rectangle_inter_shift]; exact hq
    have hb := green_union_bound (Finset.Subset.refl (faceRectangle (R+n) (S+n)))
      (FiniteGreenMonotonicity.rectangle_subset (by omega : R≤R+n) le_rfl)
      (FiniteGreenMonotonicity.rectangle_subset le_rfl (by omega : S≤S+n)) hpI hqI
    simpa only [rectangle_inter_shift] using hb))
  unfold quadrantLoss
  linarith

end
end SpanningTreeIsoperimetry.GreenStripLimits
